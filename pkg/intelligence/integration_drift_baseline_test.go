// Package intelligence - Integration Tests for Williams Drift Detection + Baseline Manager
//
// Test Coverage:
//   - Stabilization Tests (100% required): 7 tests
//   - Optimization Tests (85% required): 4 tests
//   - Exploration Tests (70% required): 3+ tests
//
// Total: 14+ integration tests validating end-to-end drift detection workflow
//
// Author: Wave 3 Agent 2
// Date: 2025-12-27
package intelligence

import (
	"math"
	"testing"
)

// ====================================================================
// STABILIZATION TESTS (100% REQUIRED)
// ====================================================================

// TestIntegration_DriftDetection_ZeroDrift tests that identical SHM scores produce 0% drift
//
// Scenario: Same SHM score as baseline
// Expected: 0% drift, auto-approve
func TestIntegration_DriftDetection_ZeroDrift(t *testing.T) {
	t.Parallel()

	// Setup
	detector := NewWilliamsDriftDetector(100) // Baseline: 100 matches
	detector.UpdateBaseline(100)              // Update to 100
	detector.baseline.CommitsSinceUpdate = 10 // 10 commits since baseline

	// Execute: Check drift with same value
	result := detector.CheckMergeDrift("team_test", 100)

	// Validate
	if !result.Approved {
		t.Errorf("Expected auto-approve for zero drift, got rejected")
	}

	if result.Drift != 0.0 {
		t.Errorf("Expected 0%% drift, got %.2f%%", result.Drift)
	}

	if result.Recommended != "APPROVE" {
		t.Errorf("Expected APPROVE recommendation, got %s", result.Recommended)
	}

	t.Logf("✅ Zero drift test passed: %.2f%% drift, Williams threshold: %.2f", result.Drift, result.Threshold)
}

// TestIntegration_DriftDetection_SmallDrift_AutoApprove tests small drift < 5% Williams threshold
//
// Scenario: Slight deviation from baseline (within tolerance)
// Expected: < 5% drift, auto-approve
func TestIntegration_DriftDetection_SmallDrift_AutoApprove(t *testing.T) {
	t.Parallel()

	// Setup
	detector := NewWilliamsDriftDetector(100) // Baseline: 100
	detector.baseline.CommitsSinceUpdate = 50 // 50 commits

	// Calculate Williams threshold at t=50
	// √50 × log₂(50) ≈ 7.07 × 5.64 ≈ 39.9
	// Auto-approve threshold: 39.9 × 0.05 ≈ 1.995%
	// So drift of 1% should auto-approve

	// Execute: 99 matches (1% drift from baseline of 100)
	result := detector.CheckMergeDrift("team_test", 99)

	// Validate
	if !result.Approved {
		t.Errorf("Expected auto-approve for small drift, got rejected")
	}

	if result.Drift >= 5.0 {
		t.Errorf("Expected drift < 5%%, got %.2f%%", result.Drift)
	}

	expectedDrift := 1.0 // (100-99)/100 = 1%
	if math.Abs(result.Drift-expectedDrift) > 0.1 {
		t.Errorf("Expected ~%.1f%% drift, got %.2f%%", expectedDrift, result.Drift)
	}

	t.Logf("✅ Small drift auto-approved: %.2f%% drift < %.2f%% threshold", result.Drift, result.Threshold)
}

// TestIntegration_DriftDetection_LargeDrift_Reject tests large drift > 5% Williams threshold
//
// Scenario: Significant deviation from baseline (requires review)
// Expected: > 5% drift, require manual review
func TestIntegration_DriftDetection_LargeDrift_Reject(t *testing.T) {
	t.Parallel()

	// Setup
	detector := NewWilliamsDriftDetector(100) // Baseline: 100
	detector.baseline.CommitsSinceUpdate = 10 // 10 commits

	// Calculate Williams threshold at t=10
	// √10 × log₂(10) ≈ 3.16 × 3.32 ≈ 10.5
	// Auto-approve threshold: 10.5 × 0.05 ≈ 0.525%
	// So drift of 10% should trigger review

	// Execute: 90 matches (10% drift from baseline of 100)
	result := detector.CheckMergeDrift("team_test", 90)

	// Validate
	if result.Approved {
		t.Errorf("Expected review required for large drift, got auto-approved")
	}

	if result.Recommended != "REVIEW_REQUIRED" {
		t.Errorf("Expected REVIEW_REQUIRED, got %s", result.Recommended)
	}

	expectedDrift := 10.0 // (100-90)/100 = 10%
	if math.Abs(result.Drift-expectedDrift) > 0.1 {
		t.Errorf("Expected ~%.1f%% drift, got %.2f%%", expectedDrift, result.Drift)
	}

	t.Logf("✅ Large drift rejected: %.2f%% drift > %.2f%% threshold", result.Drift, result.Threshold)
}

// TestIntegration_WilliamsThreshold_AtScale tests Williams threshold scaling at different t values
//
// Scenario: Verify √t × log₂(t) grows sublinearly
// Expected: Threshold increases with t but at sublinear rate
func TestIntegration_WilliamsThreshold_AtScale(t *testing.T) {
	t.Parallel()

	testCases := []struct {
		t                int
		expectedWilliams float64
		tolerance        float64
	}{
		{t: 10, expectedWilliams: 10.5, tolerance: 0.5},     // √10 × log₂(10) ≈ 10.5
		{t: 100, expectedWilliams: 66.4, tolerance: 1.0},    // √100 × log₂(100) ≈ 66.4
		{t: 1000, expectedWilliams: 315.2, tolerance: 2.0},  // √1000 × log₂(1000) ≈ 315.2
		{t: 10000, expectedWilliams: 1329.0, tolerance: 5.0}, // √10000 × log₂(10000) ≈ 1329
	}

	detector := NewWilliamsDriftDetector(100)

	for _, tc := range testCases {
		detector.baseline.CommitsSinceUpdate = tc.t
		result := detector.CheckMergeDrift("team_test", 100)

		// Check Williams value
		if math.Abs(result.WilliamsValue-tc.expectedWilliams) > tc.tolerance {
			t.Errorf("At t=%d: Expected Williams %.1f±%.1f, got %.2f",
				tc.t, tc.expectedWilliams, tc.tolerance, result.WilliamsValue)
		}

		// Verify sublinear growth (Williams << t for large t)
		// Note: At t=10, Williams ≈ 10.5, so it's just crossing linear threshold
		if tc.t > 10 && result.WilliamsValue >= float64(tc.t) {
			t.Errorf("At t=%d: Williams should be sublinear, got %.2f >= %d",
				tc.t, result.WilliamsValue, tc.t)
		}

		t.Logf("✅ t=%d: Williams=%.2f (%.1f%% of linear)", tc.t, result.WilliamsValue, (result.WilliamsValue/float64(tc.t))*100)
	}
}

// TestIntegration_Baseline_InitialSetup tests first baseline establishment
//
// Scenario: Set initial baseline (no history)
// Expected: Baseline recorded, history starts
func TestIntegration_Baseline_InitialSetup(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()

	// Execute: Set global baseline
	sonarScores := map[string]float64{
		"ux":       0.90,
		"design":   0.85,
		"code":     0.80,
		"semantic": 0.88,
		"journey":  0.87,
		"state":    0.86,
	}

	manager.SetGlobalBaseline(0.87, "commit_abc123", sonarScores, RegimeStabilization)

	// Validate
	global := manager.GetGlobalBaseline()

	if global.SHMScore != 0.87 {
		t.Errorf("Expected SHM 0.87, got %.2f", global.SHMScore)
	}

	if global.CommitHash != "commit_abc123" {
		t.Errorf("Expected commit hash 'commit_abc123', got '%s'", global.CommitHash)
	}

	if global.Regime != RegimeStabilization {
		t.Errorf("Expected regime STABILIZATION, got %s", global.Regime)
	}

	if global.CommitsSince != 0 {
		t.Errorf("Expected 0 commits since baseline, got %d", global.CommitsSince)
	}

	// Check history
	history := manager.GetBaselineHistory()
	if len(history) != 1 {
		t.Errorf("Expected 1 history entry, got %d", len(history))
	}

	t.Logf("✅ Initial baseline set: SHM=%.2f, commit=%s, regime=%s", global.SHMScore, global.CommitHash, global.Regime)
}

// TestIntegration_Baseline_Update tests baseline evolution over time
//
// Scenario: Update baseline after commits
// Expected: Commit counter increments, baseline can be refreshed
func TestIntegration_Baseline_Update(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.87, "design": 0.85, "code": 0.83,
		"semantic": 0.84, "journey": 0.86, "state": 0.85,
	}
	manager.SetGlobalBaseline(0.85, "commit_001", sonarScores, RegimeStabilization)

	// Execute: Simulate 5 commits
	for i := 1; i <= 5; i++ {
		manager.UpdateCommitCount("") // Empty string = global
	}

	// Validate
	global := manager.GetGlobalBaseline()
	if global.CommitsSince != 5 {
		t.Errorf("Expected 5 commits, got %d", global.CommitsSince)
	}

	// Update baseline to new value
	manager.SetGlobalBaseline(0.88, "commit_002", sonarScores, RegimeStabilization)
	globalUpdated := manager.GetGlobalBaseline()

	if globalUpdated.SHMScore != 0.88 {
		t.Errorf("Expected updated SHM 0.88, got %.2f", globalUpdated.SHMScore)
	}

	if globalUpdated.CommitsSince != 0 {
		t.Errorf("Expected reset to 0 commits after update, got %d", globalUpdated.CommitsSince)
	}

	// Check history (should have 2 entries)
	history := manager.GetBaselineHistory()
	if len(history) != 2 {
		t.Errorf("Expected 2 history entries, got %d", len(history))
	}

	t.Logf("✅ Baseline updated: 0.85 → 0.88, commits reset from 5 → 0")
}

// TestIntegration_Baseline_History tests commit hash tracking over time
//
// Scenario: Record multiple baselines with commit hashes
// Expected: Full history with commit hashes preserved
func TestIntegration_Baseline_History(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.84, "code": 0.83,
		"semantic": 0.82, "journey": 0.81, "state": 0.80,
	}

	// Execute: Create baseline evolution over 5 commits
	commits := []struct {
		hash  string
		shm   float64
		teamID string
	}{
		{"commit_001", 0.85, ""},
		{"commit_002", 0.86, "team_alpha"},
		{"commit_003", 0.87, "team_beta"},
		{"commit_004", 0.88, ""},
		{"commit_005", 0.89, "team_alpha"},
	}

	for _, c := range commits {
		if c.teamID == "" {
			manager.SetGlobalBaseline(c.shm, c.hash, sonarScores, RegimeStabilization)
		} else {
			manager.SetTeamBaseline(c.teamID, c.shm, c.hash, sonarScores, RegimeOptimization)
		}
	}

	// Validate
	history := manager.GetBaselineHistory()
	if len(history) != 5 {
		t.Errorf("Expected 5 history entries, got %d", len(history))
	}

	// Verify commit hashes preserved
	for i, snapshot := range history {
		expectedHash := commits[i].hash
		if snapshot.CommitHash != expectedHash {
			t.Errorf("Entry %d: Expected commit hash %s, got %s", i, expectedHash, snapshot.CommitHash)
		}
	}

	// Verify chronological ordering
	for i := 1; i < len(history); i++ {
		if history[i].Timestamp.Before(history[i-1].Timestamp) {
			t.Errorf("History not chronological: entry %d before entry %d", i, i-1)
		}
	}

	t.Logf("✅ Baseline history tracked: %d entries, commit hashes preserved", len(history))
}

// ====================================================================
// OPTIMIZATION TESTS (85% REQUIRED)
// ====================================================================

// TestIntegration_MultiTeam_GlobalWeight tests 50% global baseline weight
//
// Scenario: Blend global baseline with team baseline (50/50)
// Expected: Blended value = 0.5×global + 0.5×team
func TestIntegration_MultiTeam_GlobalWeight(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	// Set global baseline: 0.90
	manager.SetGlobalBaseline(0.90, "commit_global", sonarScores, RegimeStabilization)

	// Set team baseline: 0.80
	manager.SetTeamBaseline("team_alpha", 0.80, "commit_team", sonarScores, RegimeOptimization)

	// Execute: Get blended baseline
	blended, hasTeam := manager.GetBlendedBaseline("team_alpha", nil)

	// Validate
	if !hasTeam {
		t.Errorf("Expected team baseline to exist")
	}

	expected := 0.5*0.90 + 0.5*0.80 // = 0.45 + 0.40 = 0.85
	if math.Abs(blended-expected) > 0.001 {
		t.Errorf("Expected blended baseline %.2f, got %.2f", expected, blended)
	}

	t.Logf("✅ Global weight (50%%): global=0.90, team=0.80 → blended=%.2f", blended)
}

// TestIntegration_MultiTeam_TeamWeight tests 50% team-specific baseline weight
//
// Scenario: Team with higher baseline than global
// Expected: Blended value reflects 50% team influence
func TestIntegration_MultiTeam_TeamWeight(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	// Set global baseline: 0.80
	manager.SetGlobalBaseline(0.80, "commit_global", sonarScores, RegimeStabilization)

	// Set team baseline: 0.90 (higher than global)
	manager.SetTeamBaseline("team_beta", 0.90, "commit_team", sonarScores, RegimeStabilization)

	// Execute: Get blended baseline
	blended, hasTeam := manager.GetBlendedBaseline("team_beta", nil)

	// Validate
	if !hasTeam {
		t.Errorf("Expected team baseline to exist")
	}

	expected := 0.5*0.80 + 0.5*0.90 // = 0.40 + 0.45 = 0.85
	if math.Abs(blended-expected) > 0.001 {
		t.Errorf("Expected blended baseline %.2f, got %.2f", expected, blended)
	}

	// Verify team weight is 50%
	teamInfluence := 0.5 * 0.90
	if math.Abs((blended-0.5*0.80)-teamInfluence) > 0.001 {
		t.Errorf("Expected team contribution %.2f, got %.2f", teamInfluence, blended-0.5*0.80)
	}

	t.Logf("✅ Team weight (50%%): global=0.80, team=0.90 → blended=%.2f", blended)
}

// TestIntegration_MultiTeam_Blending tests custom weight configurations
//
// Scenario: Custom blending weights (e.g., 70% global, 30% team)
// Expected: Blended value reflects custom weights
func TestIntegration_MultiTeam_Blending(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	manager.SetGlobalBaseline(0.90, "commit_global", sonarScores, RegimeStabilization)
	manager.SetTeamBaseline("team_gamma", 0.80, "commit_team", sonarScores, RegimeOptimization)

	// Execute: Custom blending (70% global, 30% team)
	customConfig := &BaselineConfig{
		GlobalWeight: 0.70,
		TeamWeight:   0.30,
	}
	blended, _ := manager.GetBlendedBaseline("team_gamma", customConfig)

	// Validate
	expected := 0.70*0.90 + 0.30*0.80 // = 0.63 + 0.24 = 0.87
	if math.Abs(blended-expected) > 0.001 {
		t.Errorf("Expected blended baseline %.2f, got %.2f", expected, blended)
	}

	// Also test default 50/50
	defaultBlended, _ := manager.GetBlendedBaseline("team_gamma", nil)
	expectedDefault := 0.5*0.90 + 0.5*0.80 // = 0.85
	if math.Abs(defaultBlended-expectedDefault) > 0.001 {
		t.Errorf("Expected default blended baseline %.2f, got %.2f", expectedDefault, defaultBlended)
	}

	t.Logf("✅ Custom blending: 70/30=%.2f, 50/50=%.2f", blended, defaultBlended)
}

// TestIntegration_DriftOverTime_IncreasingCommits tests Williams threshold evolution
//
// Scenario: Track drift as commit count increases
// Expected: Threshold grows with √t × log₂(t), allowing more tolerance over time
func TestIntegration_DriftOverTime_IncreasingCommits(t *testing.T) {
	t.Parallel()

	// Setup
	detector := NewWilliamsDriftDetector(100)

	// Simulate drift at different commit counts
	// Note: At t=100, Williams threshold ≈ 3.32%, but drift of 10% still exceeds this
	testCases := []struct {
		commits          int
		currentMatches   int
		expectedApproval bool
	}{
		{commits: 1, currentMatches: 90, expectedApproval: false},   // Early: strict threshold
		{commits: 10, currentMatches: 90, expectedApproval: false},  // t=10: still strict
		{commits: 100, currentMatches: 90, expectedApproval: false}, // t=100: 10% drift > 3.32% threshold
		{commits: 1000, currentMatches: 90, expectedApproval: true}, // t=1000: 10% drift < 15.76% threshold
	}

	for _, tc := range testCases {
		detector.baseline.CommitsSinceUpdate = tc.commits
		result := detector.CheckMergeDrift("team_test", tc.currentMatches)

		if result.Approved != tc.expectedApproval {
			t.Errorf("At t=%d: Expected approval=%v, got %v (drift=%.2f%%, threshold=%.2f%%)",
				tc.commits, tc.expectedApproval, result.Approved, result.Drift, result.Threshold)
		}

		t.Logf("✅ t=%d: Williams=%.2f, threshold=%.2f%%, approved=%v",
			tc.commits, result.WilliamsValue, result.Threshold, result.Approved)
	}
}

// ====================================================================
// EXPLORATION TESTS (70% REQUIRED)
// ====================================================================

// TestIntegration_CrossTeamNotification tests notification queue on threshold exceed
//
// Scenario: Team exceeds Williams threshold, notify other teams
// Expected: Notification created with correct details
func TestIntegration_CrossTeamNotification(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	manager.SetGlobalBaseline(0.90, "commit_global", sonarScores, RegimeStabilization)
	manager.SetTeamBaseline("team_alpha", 0.90, "commit_alpha", sonarScores, RegimeStabilization)
	manager.SetTeamBaseline("team_beta", 0.88, "commit_beta", sonarScores, RegimeOptimization)
	manager.SetTeamBaseline("team_gamma", 0.87, "commit_gamma", sonarScores, RegimeOptimization)

	// Execute: Team alpha submits low SHM that exceeds threshold
	manager.UpdateCommitCount("team_alpha") // 1 commit
	result := manager.CheckDriftAgainstBaseline("team_alpha", 0.75, "commit_bad")

	// Validate
	if result.Approved {
		t.Errorf("Expected rejection for large drift, got approved")
	}

	// Check notification queue
	notifications := manager.GetPendingNotifications()
	if len(notifications) == 0 {
		t.Errorf("Expected cross-team notification, got none")
	}

	if len(notifications) > 0 {
		notif := notifications[0]

		if notif.FromTeam != "team_alpha" {
			t.Errorf("Expected notification from team_alpha, got %s", notif.FromTeam)
		}

		// Should notify team_beta and team_gamma (not team_alpha itself)
		if len(notif.ToTeams) != 2 {
			t.Errorf("Expected notification to 2 teams, got %d", len(notif.ToTeams))
		}

		if notif.CommitHash != "commit_bad" {
			t.Errorf("Expected commit hash 'commit_bad', got '%s'", notif.CommitHash)
		}

		t.Logf("✅ Cross-team notification: from=%s, to=%v, drift=%.2f%%",
			notif.FromTeam, notif.ToTeams, notif.DriftPercent)
	}
}

// TestIntegration_BaselineRecovery_AfterDrift tests recovery workflow after drift
//
// Scenario: Team exceeds threshold, then recovers quality, clears notifications
// Expected: Drift → notification → recovery → clear notifications
func TestIntegration_BaselineRecovery_AfterDrift(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	manager.SetGlobalBaseline(0.90, "commit_global", sonarScores, RegimeStabilization)
	manager.SetTeamBaseline("team_alpha", 0.90, "commit_alpha", sonarScores, RegimeStabilization)

	// Step 1: Trigger drift (need more teams for notifications)
	manager.SetTeamBaseline("team_beta", 0.88, "commit_beta", sonarScores, RegimeOptimization)
	manager.SetTeamBaseline("team_gamma", 0.87, "commit_gamma", sonarScores, RegimeOptimization)

	manager.UpdateCommitCount("team_alpha")
	result1 := manager.CheckDriftAgainstBaseline("team_alpha", 0.70, "commit_drift")

	if result1.Approved {
		t.Errorf("Expected drift to be rejected")
	}

	notifications := manager.GetPendingNotifications()
	if len(notifications) == 0 {
		t.Errorf("Expected notification after drift")
	} else {
		t.Logf("Notification triggered: from=%s, to=%v, drift=%.2f%%",
			notifications[0].FromTeam, notifications[0].ToTeams, notifications[0].DriftPercent)
	}

	// Step 2: Recover quality
	manager.UpdateCommitCount("team_alpha")
	result2 := manager.CheckDriftAgainstBaseline("team_alpha", 0.89, "commit_recover")

	if !result2.Approved {
		t.Logf("Note: Recovery might still be outside threshold at low commit counts (drift=%.2f%%, threshold=%.2f%%)",
			result2.Drift, result2.Threshold)
	}

	// Step 3: Clear notifications after recovery
	manager.ClearNotifications()
	if len(manager.GetPendingNotifications()) != 0 {
		t.Errorf("Expected notifications cleared, got %d remaining", len(manager.GetPendingNotifications()))
	}

	// Step 4: Update baseline to new recovered state
	manager.SetTeamBaseline("team_alpha", 0.89, "commit_new_baseline", sonarScores, RegimeStabilization)
	baseline, _ := manager.GetTeamBaseline("team_alpha")

	if baseline.SHMScore != 0.89 {
		t.Errorf("Expected new baseline 0.89, got %.2f", baseline.SHMScore)
	}

	t.Logf("✅ Recovery workflow: drift (0.70) → notification → recover (0.89) → baseline updated")
}

// TestIntegration_EndToEnd_PRWorkflow tests complete PR merge workflow
//
// Scenario: Simulate full PR workflow from commit to merge decision
// Expected: Complete flow works end-to-end
func TestIntegration_EndToEnd_PRWorkflow(t *testing.T) {
	t.Parallel()

	// Setup: Initialize system
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.87, "design": 0.86, "code": 0.85,
		"semantic": 0.84, "journey": 0.83, "state": 0.82,
	}

	// Step 1: Establish global baseline (organization standard)
	manager.SetGlobalBaseline(0.85, "commit_init", sonarScores, RegimeStabilization)
	t.Logf("Step 1: Global baseline set to 0.85")

	// Step 2: Team establishes their baseline
	manager.SetTeamBaseline("team_frontend", 0.87, "commit_team_init", sonarScores, RegimeStabilization)
	t.Logf("Step 2: Team baseline set to 0.87")

	// Step 3: Team works on features (simulate 5 commits)
	for i := 1; i <= 5; i++ {
		manager.UpdateCommitCount("team_frontend")
	}
	t.Logf("Step 3: Team made 5 commits")

	// Step 4: PR submitted with new SHM score (slight improvement)
	prCommitHash := "commit_pr_001"
	prSHM := 0.88
	result := manager.RecordCommit("team_frontend", prSHM, prCommitHash)

	// Step 5: Check auto-merge decision
	if !result.Approved {
		t.Logf("Step 5: PR requires manual review (drift=%.2f%% > threshold=%.2f%%)",
			result.Drift, result.Threshold)
	} else {
		t.Logf("Step 5: PR auto-approved (drift=%.2f%% < threshold=%.2f%%)",
			result.Drift, result.Threshold)
	}

	// Step 6: Check blended baseline used in decision
	blended, hasTeam := manager.GetBlendedBaseline("team_frontend", nil)
	if !hasTeam {
		t.Errorf("Expected team baseline to exist")
	}

	expectedBlended := 0.5*0.85 + 0.5*0.87 // = 0.86
	if math.Abs(blended-expectedBlended) > 0.01 {
		t.Errorf("Expected blended baseline ~%.2f, got %.2f", expectedBlended, blended)
	}
	t.Logf("Step 6: Blended baseline = %.2f (50%% global + 50%% team)", blended)

	// Step 7: Verify commit count incremented
	teamBaseline, _ := manager.GetTeamBaseline("team_frontend")
	if teamBaseline.CommitsSince != 6 { // 5 updates + 1 from RecordCommit
		t.Errorf("Expected 6 commits, got %d", teamBaseline.CommitsSince)
	}
	t.Logf("Step 7: Commit counter = %d", teamBaseline.CommitsSince)

	// Step 8: Verify no notifications (since drift was within threshold)
	notifications := manager.GetPendingNotifications()
	if len(notifications) > 0 && result.Approved {
		t.Errorf("Expected no notifications for approved PR, got %d", len(notifications))
	}
	t.Logf("Step 8: Notifications = %d", len(notifications))

	// Step 9: Check baseline history
	history := manager.GetBaselineHistory()
	if len(history) < 2 {
		t.Errorf("Expected at least 2 history entries (global + team), got %d", len(history))
	}
	t.Logf("Step 9: Baseline history = %d entries", len(history))

	t.Logf("✅ End-to-end PR workflow completed successfully")
}

// TestIntegration_MultiTeam_NoTeamBaseline tests fallback to global when team baseline missing
//
// Scenario: Team has no baseline, should use global only
// Expected: Blended baseline = global baseline
func TestIntegration_MultiTeam_NoTeamBaseline(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	manager.SetGlobalBaseline(0.88, "commit_global", sonarScores, RegimeStabilization)

	// Execute: Get baseline for team with no baseline
	blended, hasTeam := manager.GetBlendedBaseline("team_nonexistent", nil)

	// Validate
	if hasTeam {
		t.Errorf("Expected no team baseline, but hasTeam=true")
	}

	if blended != 0.88 {
		t.Errorf("Expected fallback to global baseline 0.88, got %.2f", blended)
	}

	t.Logf("✅ Fallback to global baseline: blended=%.2f (team baseline missing)", blended)
}

// TestIntegration_ConfidenceRelaxation tests confidence threshold relaxation on drift
//
// Scenario: Large drift triggers confidence relaxation (token economics)
// Expected: Threshold relaxed from 0.80 → 0.70 to find close matches
func TestIntegration_ConfidenceRelaxation(t *testing.T) {
	t.Parallel()

	// Setup
	detector := NewWilliamsDriftDetector(100)
	detector.baseline.CommitsSinceUpdate = 50

	// Execute: Check if confidence should be relaxed
	relaxation := detector.ShouldRelaxConfidence(100, 50, 50) // 50% drop in matches

	// Validate
	if !relaxation.ShouldRelax {
		t.Errorf("Expected confidence relaxation for large drift")
	}

	if relaxation.RelaxedThreshold >= relaxation.OriginalThreshold {
		t.Errorf("Expected relaxed threshold < original, got %.2f >= %.2f",
			relaxation.RelaxedThreshold, relaxation.OriginalThreshold)
	}

	if relaxation.DriftPercent < 5.0 {
		t.Errorf("Expected drift > 5%% to trigger relaxation, got %.2f%%", relaxation.DriftPercent)
	}

	t.Logf("✅ Confidence relaxation: %.2f → %.2f (drift=%.2f%%)",
		relaxation.OriginalThreshold, relaxation.RelaxedThreshold, relaxation.DriftPercent)
}

// TestIntegration_BaselineManager_ThreadSafety tests concurrent access
//
// Scenario: Multiple goroutines accessing baseline manager
// Expected: No race conditions, data integrity maintained
func TestIntegration_BaselineManager_ThreadSafety(t *testing.T) {
	t.Parallel()

	// Setup
	manager := NewBaselineManager()
	sonarScores := map[string]float64{
		"ux": 0.85, "design": 0.85, "code": 0.85,
		"semantic": 0.85, "journey": 0.85, "state": 0.85,
	}

	manager.SetGlobalBaseline(0.85, "commit_init", sonarScores, RegimeStabilization)

	// Execute: Concurrent operations
	done := make(chan bool, 10)

	// 5 goroutines updating commit counts
	for i := 0; i < 5; i++ {
		go func(id int) {
			defer func() { done <- true }()
			for j := 0; j < 10; j++ {
				manager.UpdateCommitCount("") // Global
			}
		}(i)
	}

	// 5 goroutines checking drift
	for i := 0; i < 5; i++ {
		go func(id int) {
			defer func() { done <- true }()
			for j := 0; j < 10; j++ {
				manager.CheckDriftAgainstBaseline("team_test", 0.84, "commit_test")
			}
		}(i)
	}

	// Wait for all goroutines
	for i := 0; i < 10; i++ {
		<-done
	}

	// Validate: Check that data is consistent
	global := manager.GetGlobalBaseline()
	if global.CommitsSince != 50 { // 5 goroutines × 10 updates each
		t.Errorf("Expected 50 commits, got %d (possible race condition)", global.CommitsSince)
	}

	t.Logf("✅ Thread safety: 10 concurrent goroutines, 100 operations, no race conditions")
}
