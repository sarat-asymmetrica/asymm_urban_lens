// Package intelligence implements Multi-Team Baseline Management for Williams Drift Detection
//
// Baseline Management System:
// - Global baseline: 50% weight (organization-wide quality standard)
// - Team-specific baseline: 50% weight (allows for team variations)
// - Cross-team notifications when threshold exceeded
// - Baseline history tracking with commit hashes
//
// Research: UNIFIED_INTELLIGENCE_MONITORING_RESEARCH_PAPER.html (lines 877-899)
// Author: Wave 3 Agent 2 (Integration Tests)
// Date: 2025-12-27
package intelligence

import (
	"fmt"
	"sync"
	"time"
)

// BaselineManager manages global and team-specific baselines for SHM drift detection
type BaselineManager struct {
	mu                sync.RWMutex
	globalBaseline    BaselineSnapshot
	teamBaselines     map[string]BaselineSnapshot
	baselineHistory   []BaselineSnapshot
	notificationQueue []BaselineNotification
}

// BaselineSnapshot represents a point-in-time baseline measurement
type BaselineSnapshot struct {
	TeamID           string    // Empty string for global baseline
	SHMScore         float64   // System Health Metric score
	CommitHash       string    // Git commit hash when baseline was set
	CommitsSince     int       // Number of commits since baseline was set
	Timestamp        time.Time // When baseline was recorded
	SonarBreakdown   map[string]float64 // Individual sonar scores
	Regime           Regime    // Regime at time of snapshot
}

// BaselineNotification represents a cross-team alert when threshold exceeded
type BaselineNotification struct {
	FromTeam         string    // Team that triggered the notification
	ToTeams          []string  // Teams to notify
	DriftPercent     float64   // How much drift was detected
	Threshold        float64   // Williams threshold that was exceeded
	CommitHash       string    // Commit that triggered the notification
	Timestamp        time.Time // When notification was created
	Message          string    // Human-readable notification
}

// BaselineConfig contains configuration for baseline blending
type BaselineConfig struct {
	GlobalWeight float64 // Weight for global baseline (default: 0.50)
	TeamWeight   float64 // Weight for team-specific baseline (default: 0.50)
}

// NewBaselineManager creates a baseline manager with default configuration
func NewBaselineManager() *BaselineManager {
	return &BaselineManager{
		teamBaselines:     make(map[string]BaselineSnapshot),
		baselineHistory:   make([]BaselineSnapshot, 0),
		notificationQueue: make([]BaselineNotification, 0),
	}
}

// SetGlobalBaseline sets the organization-wide baseline
//
// This should be called after initial system stabilization to establish
// the global quality standard.
//
// Parameters:
//   - shmScore: Current system health metric
//   - commitHash: Git commit hash at baseline time
//   - sonarBreakdown: Individual sonar scores
//   - regime: Current regime (should be STABILIZATION for global baseline)
//
// Example:
//
//	manager.SetGlobalBaseline(0.87, "abc123", sonarScores, RegimeStabilization)
func (bm *BaselineManager) SetGlobalBaseline(
	shmScore float64,
	commitHash string,
	sonarBreakdown map[string]float64,
	regime Regime,
) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	snapshot := BaselineSnapshot{
		TeamID:         "", // Empty = global
		SHMScore:       shmScore,
		CommitHash:     commitHash,
		CommitsSince:   0,
		Timestamp:      time.Now(),
		SonarBreakdown: sonarBreakdown,
		Regime:         regime,
	}

	bm.globalBaseline = snapshot
	bm.baselineHistory = append(bm.baselineHistory, snapshot)
}

// SetTeamBaseline sets a team-specific baseline
//
// Teams can have different quality standards while still being measured
// against the global baseline (50/50 blend).
//
// Parameters:
//   - teamID: Team identifier (e.g., "team_alpha", "team_beta")
//   - shmScore: Team's current SHM score
//   - commitHash: Git commit hash
//   - sonarBreakdown: Team's sonar scores
//   - regime: Team's current regime
//
// Example:
//
//	manager.SetTeamBaseline("team_alpha", 0.85, "def456", sonarScores, RegimeOptimization)
func (bm *BaselineManager) SetTeamBaseline(
	teamID string,
	shmScore float64,
	commitHash string,
	sonarBreakdown map[string]float64,
	regime Regime,
) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	snapshot := BaselineSnapshot{
		TeamID:         teamID,
		SHMScore:       shmScore,
		CommitHash:     commitHash,
		CommitsSince:   0,
		Timestamp:      time.Now(),
		SonarBreakdown: sonarBreakdown,
		Regime:         regime,
	}

	bm.teamBaselines[teamID] = snapshot
	bm.baselineHistory = append(bm.baselineHistory, snapshot)
}

// GetBlendedBaseline computes 50/50 blend of global and team-specific baselines
//
// Formula (from research paper):
//   blended_baseline = (0.50 × global_baseline) + (0.50 × team_baseline)
//
// If no team-specific baseline exists, falls back to global baseline.
//
// Parameters:
//   - teamID: Team identifier
//   - config: Blending configuration (optional, defaults to 50/50)
//
// Returns:
//   - Blended SHM score
//   - true if team baseline exists, false if using global only
//
// Example:
//
//	blended, hasTeam := manager.GetBlendedBaseline("team_alpha", nil)
func (bm *BaselineManager) GetBlendedBaseline(
	teamID string,
	config *BaselineConfig,
) (float64, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	// Default to 50/50 blending
	if config == nil {
		config = &BaselineConfig{
			GlobalWeight: 0.50,
			TeamWeight:   0.50,
		}
	}

	// Get global baseline
	globalSHM := bm.globalBaseline.SHMScore

	// Check if team baseline exists
	teamBaseline, hasTeam := bm.teamBaselines[teamID]
	if !hasTeam {
		// No team baseline - use global only
		return globalSHM, false
	}

	// Blend 50/50 (or custom weights)
	blended := (config.GlobalWeight * globalSHM) + (config.TeamWeight * teamBaseline.SHMScore)

	return blended, true
}

// UpdateCommitCount increments commit counter for a baseline
//
// Call this after each commit to track drift over time.
//
// Parameters:
//   - teamID: Team identifier (empty string for global)
func (bm *BaselineManager) UpdateCommitCount(teamID string) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	if teamID == "" {
		// Update global baseline commit count
		bm.globalBaseline.CommitsSince++
	} else {
		// Update team baseline commit count
		if baseline, exists := bm.teamBaselines[teamID]; exists {
			baseline.CommitsSince++
			bm.teamBaselines[teamID] = baseline
		}
	}
}

// CheckDriftAgainstBaseline performs Williams drift detection against blended baseline
//
// Formula:
//   1. Get blended baseline (50% global + 50% team)
//   2. Calculate Williams threshold: √t × log₂(t) × 0.05
//   3. Compute drift: |current_shm - blended_baseline|
//   4. Auto-approve if drift_percent < williams_threshold
//
// Parameters:
//   - teamID: Team identifier
//   - currentSHM: Current system health metric
//   - commitHash: Current commit hash
//
// Returns:
//   - MergeDriftResult with approval decision
//
// Example:
//
//	result := manager.CheckDriftAgainstBaseline("team_alpha", 0.84, "ghi789")
//	if result.Approved {
//	    // Auto-approve merge
//	}
func (bm *BaselineManager) CheckDriftAgainstBaseline(
	teamID string,
	currentSHM float64,
	commitHash string,
) MergeDriftResult {
	bm.mu.RLock()

	// Get blended baseline
	blendedBaseline, hasTeam := bm.GetBlendedBaseline(teamID, nil)

	// Get commit count for Williams calculation
	commitsSince := bm.globalBaseline.CommitsSince
	if hasTeam {
		if teamBaseline, exists := bm.teamBaselines[teamID]; exists {
			commitsSince = teamBaseline.CommitsSince
		}
	}

	bm.mu.RUnlock()

	// Use Williams drift detector for calculation
	detector := NewWilliamsDriftDetector(int(blendedBaseline * 100))
	detector.baseline.CommitsSinceUpdate = commitsSince

	result := detector.CheckMergeDrift(teamID, int(currentSHM * 100))

	// Check if we should notify other teams
	if !result.Approved {
		bm.notifyTeamsOnThresholdExceed(teamID, result.Drift, result.Threshold, commitHash)
	}

	return result
}

// notifyTeamsOnThresholdExceed creates cross-team notifications
//
// When a team exceeds the Williams threshold, notify all other teams
// to be aware of potential system-wide quality issues.
func (bm *BaselineManager) notifyTeamsOnThresholdExceed(
	fromTeam string,
	driftPercent float64,
	threshold float64,
	commitHash string,
) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	// Get all teams except the triggering team
	toTeams := make([]string, 0)
	for teamID := range bm.teamBaselines {
		if teamID != fromTeam {
			toTeams = append(toTeams, teamID)
		}
	}

	if len(toTeams) == 0 {
		return // No other teams to notify
	}

	notification := BaselineNotification{
		FromTeam:     fromTeam,
		ToTeams:      toTeams,
		DriftPercent: driftPercent,
		Threshold:    threshold,
		CommitHash:   commitHash,
		Timestamp:    time.Now(),
		Message: fmt.Sprintf(
			"Team '%s' exceeded Williams threshold (%.2f%% drift > %.2f%% threshold) at commit %s. Review may be needed.",
			fromTeam,
			driftPercent,
			threshold,
			commitHash,
		),
	}

	bm.notificationQueue = append(bm.notificationQueue, notification)
}

// GetPendingNotifications returns all pending cross-team notifications
//
// Call this periodically to process notifications (e.g., send to Slack, email).
//
// Returns:
//   - Slice of pending notifications
func (bm *BaselineManager) GetPendingNotifications() []BaselineNotification {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	// Return copy to avoid race conditions
	notifications := make([]BaselineNotification, len(bm.notificationQueue))
	copy(notifications, bm.notificationQueue)

	return notifications
}

// ClearNotifications clears all pending notifications
//
// Call after processing notifications to avoid duplicate sends.
func (bm *BaselineManager) ClearNotifications() {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	bm.notificationQueue = make([]BaselineNotification, 0)
}

// GetBaselineHistory returns all historical baseline snapshots
//
// Useful for trend analysis and regression detection.
//
// Returns:
//   - Slice of baseline snapshots (chronological order)
func (bm *BaselineManager) GetBaselineHistory() []BaselineSnapshot {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	// Return copy
	history := make([]BaselineSnapshot, len(bm.baselineHistory))
	copy(history, bm.baselineHistory)

	return history
}

// GetGlobalBaseline returns the current global baseline
func (bm *BaselineManager) GetGlobalBaseline() BaselineSnapshot {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	return bm.globalBaseline
}

// GetTeamBaseline returns a team's current baseline
//
// Parameters:
//   - teamID: Team identifier
//
// Returns:
//   - BaselineSnapshot
//   - true if team baseline exists, false otherwise
func (bm *BaselineManager) GetTeamBaseline(teamID string) (BaselineSnapshot, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	baseline, exists := bm.teamBaselines[teamID]
	return baseline, exists
}

// GetAllTeamBaselines returns all team baselines
//
// Returns:
//   - Map of teamID -> BaselineSnapshot
func (bm *BaselineManager) GetAllTeamBaselines() map[string]BaselineSnapshot {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	// Return copy
	baselines := make(map[string]BaselineSnapshot, len(bm.teamBaselines))
	for k, v := range bm.teamBaselines {
		baselines[k] = v
	}

	return baselines
}

// RecordCommit updates baseline commit counters and returns drift detection result
//
// This is a convenience method that combines UpdateCommitCount and CheckDriftAgainstBaseline.
//
// Parameters:
//   - teamID: Team identifier (empty string for global)
//   - currentSHM: Current system health metric
//   - commitHash: Git commit hash
//
// Returns:
//   - MergeDriftResult with approval decision
//
// Example:
//
//	result := manager.RecordCommit("team_alpha", 0.86, "jkl012")
//	if result.Approved {
//	    // Auto-approve - drift within Williams threshold
//	} else {
//	    // Require manual review - drift exceeds threshold
//	}
func (bm *BaselineManager) RecordCommit(
	teamID string,
	currentSHM float64,
	commitHash string,
) MergeDriftResult {
	// Update commit count
	bm.UpdateCommitCount(teamID)

	// Check drift
	return bm.CheckDriftAgainstBaseline(teamID, currentSHM, commitHash)
}
