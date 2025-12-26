package sonars

import (
	"context"
	"fmt"
	"math"
	"time"
)

// JourneySonar measures user navigation and friction (Navigation Mechanic)
//
// Metrics:
// - Frustration points: Where users get stuck or confused
// - Rage clicks: Repeated clicks on non-responsive elements
// - Backtracking probability: Likelihood of users hitting "back"
// - Navigation depth: How many clicks to complete tasks
//
// Formula: journey_smoothness = (1.0 - frustration) × (1.0 - rage_clicks) × (1.0 - backtracking)
// Author: Dr. Yuki Tanaka (Cognitive Psychology PhD, MIT)
type JourneySonar struct {
	*BaseSonar
}

// NewJourneySonar creates user journey analysis sonar
func NewJourneySonar() *JourneySonar {
	return &JourneySonar{
		BaseSonar: NewBaseSonar("Journey Sonar"),
	}
}

// Ping collects user journey telemetry (simulated - real impl uses session recordings)
func (js *JourneySonar) Ping(ctx context.Context, app *AppState) (*TelemetryData, error) {
	startTime := time.Now()
	rawData := make(map[string]interface{})

	// Analyze navigation structure
	navComplexity := js.analyzeNavigationComplexity(app)
	rawData["nav_complexity"] = navComplexity

	// Detect potential frustration points
	frustrationPoints := js.detectFrustrationPoints(app)
	rawData["frustration_points"] = frustrationPoints

	// Estimate rage click likelihood
	rageClickRisk := js.estimateRageClickRisk(app)
	rawData["rage_click_risk"] = rageClickRisk

	// Calculate backtracking probability
	backtrackingProb := js.calculateBacktrackingProbability(app)
	rawData["backtracking_prob"] = backtrackingProb

	return &TelemetryData{
		SonarName:   js.Name(),
		CollectedAt: time.Now(),
		RawData:     rawData,
		Duration:    time.Since(startTime),
	}, nil
}

// Echo processes journey telemetry into metrics
func (js *JourneySonar) Echo(ctx context.Context, telemetry *TelemetryData) (*Metrics, error) {
	values := make(map[string]float64)
	details := make(map[string]interface{})

	// Process navigation complexity
	if navComplexity, ok := telemetry.RawData["nav_complexity"].(map[string]float64); ok {
		values["nav_depth"] = navComplexity["depth"]
		values["nav_breadth"] = navComplexity["breadth"]
		details["nav_structure"] = navComplexity
	}

	// Process frustration points
	if frustration, ok := telemetry.RawData["frustration_points"].(map[string]float64); ok {
		values["frustration_score"] = frustration["score"]
		values["friction_points"] = frustration["count"]
		details["frustration_analysis"] = frustration
	}

	// Process rage click risk
	if rageClick, ok := telemetry.RawData["rage_click_risk"].(map[string]float64); ok {
		values["rage_click_probability"] = rageClick["probability"]
		details["rage_click_analysis"] = rageClick
	}

	// Process backtracking probability
	if backtracking, ok := telemetry.RawData["backtracking_prob"].(map[string]float64); ok {
		values["backtracking_probability"] = backtracking["probability"]
		details["backtracking_analysis"] = backtracking
	}

	return &Metrics{
		SonarName: js.Name(),
		Values:    values,
		Details:   details,
		Timestamp: time.Now(),
	}, nil
}

// Map normalizes journey metrics to 0.0-1.0 score
func (js *JourneySonar) Map(ctx context.Context, metrics *Metrics) float64 {
	// Frustration (lower is better)
	frustration := metrics.Values["frustration_score"]
	frustrationScore := 1.0 - frustration

	// Rage clicks (lower is better)
	rageClick := metrics.Values["rage_click_probability"]
	rageClickScore := 1.0 - rageClick

	// Backtracking (lower is better)
	backtracking := metrics.Values["backtracking_probability"]
	backtrackingScore := 1.0 - backtracking

	// Navigation depth (optimal = 2-3 clicks, penalize deep navigation)
	navDepth := metrics.Values["nav_depth"]
	navScore := 1.0
	if navDepth > 5.0 {
		navScore = 0.5 // Deep navigation = poor UX
	} else if navDepth > 3.0 {
		navScore = 0.8
	}

	// Weighted average
	score := (frustrationScore*0.35 + rageClickScore*0.30 + backtrackingScore*0.20 + navScore*0.15)

	return ClampScore(score)
}

// Critique generates human-readable journey report
func (js *JourneySonar) Critique(ctx context.Context, score float64, metrics *Metrics) *Report {
	report := &Report{
		SonarName:       js.Name(),
		Score:           score,
		Status:          DetermineStatus(score),
		Findings:        []Finding{},
		Recommendations: []string{},
		Timestamp:       time.Now(),
	}

	frustration := metrics.Values["frustration_score"]
	rageClick := metrics.Values["rage_click_probability"]
	backtracking := metrics.Values["backtracking_probability"]
	navDepth := metrics.Values["nav_depth"]

	// Summary
	report.Summary = fmt.Sprintf("User Journey: %.1f%% frustration, %.1f%% rage clicks, %.1f clicks deep",
		frustration*100, rageClick*100, navDepth)

	// Analyze frustration
	if frustration < 0.10 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "Smooth user journey - minimal frustration points",
			Value:    frustration,
			Target:   0.10,
		})
	} else if frustration < 0.25 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Medium",
			Message:  fmt.Sprintf("Moderate friction (%.1f%%) - some confusion likely", frustration*100),
			Value:    frustration,
			Target:   0.25,
		})
		report.Recommendations = append(report.Recommendations,
			"Add tooltips or help text at friction points",
			"Improve form validation error messages",
			"Simplify multi-step workflows")
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "High",
			Message:  fmt.Sprintf("High frustration (%.1f%%) - users will struggle", frustration*100),
			Value:    frustration,
			Target:   0.25,
		})
		report.Recommendations = append(report.Recommendations,
			"URGENT: Conduct user testing to identify pain points",
			"Add onboarding tutorials for complex features",
			"Redesign confusing UI elements based on user feedback")
	}

	// Analyze rage clicks
	if rageClick < 0.05 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "No rage click indicators - responsive UI",
			Value:    rageClick,
			Target:   0.05,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "Critical",
			Message:  fmt.Sprintf("Rage click risk (%.1f%%) - elements not responding", rageClick*100),
			Value:    rageClick,
			Target:   0.05,
		})
		report.Recommendations = append(report.Recommendations,
			"Add loading spinners to all async actions",
			"Disable buttons during processing (prevent double-clicks)",
			"Show immediate feedback for all user interactions")
	}

	// Analyze backtracking
	if backtracking < 0.15 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "Linear flow - users rarely go back",
			Value:    backtracking,
			Target:   0.15,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Medium",
			Message:  fmt.Sprintf("High backtracking (%.1f%%) - users second-guessing", backtracking*100),
			Value:    backtracking,
			Target:   0.15,
		})
		report.Recommendations = append(report.Recommendations,
			"Add progress indicators for multi-step flows",
			"Allow editing previous steps without backtracking",
			"Provide summary/review step before final submission")
	}

	// Analyze navigation depth
	if navDepth <= 3.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  fmt.Sprintf("Shallow navigation (%.0f clicks) - easy to reach content", navDepth),
			Value:    navDepth,
			Target:   3.0,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "Medium",
			Message:  fmt.Sprintf("Deep navigation (%.0f clicks) - important content buried", navDepth),
			Value:    navDepth,
			Target:   3.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Flatten information architecture (max 3 levels)",
			"Add search functionality for quick access",
			"Create shortcuts/quick actions for common tasks")
	}

	return report
}

// analyzeNavigationComplexity measures navigation structure
func (js *JourneySonar) analyzeNavigationComplexity(app *AppState) map[string]float64 {
	depth := 2.0  // Default (good)
	breadth := 5.0 // Default (good)

	if app.Frontend != nil {
		// Estimate depth from route structure
		depth = math.Min(5.0, float64(len(app.Frontend.Routes))/3.0)

		// Breadth = number of top-level routes
		breadth = float64(len(app.Frontend.Routes))
	}

	return map[string]float64{
		"depth":   depth,
		"breadth": breadth,
	}
}

// detectFrustrationPoints identifies potential UX friction
func (js *JourneySonar) detectFrustrationPoints(app *AppState) map[string]float64 {
	// Simulated frustration detection
	// Real impl would analyze session recordings, heat maps, error rates

	frictionCount := 0.0
	totalInteractions := 10.0

	if app.Frontend != nil {
		// Assume complex apps have more friction
		frictionCount = math.Min(5.0, float64(len(app.Frontend.Components))/5.0)
	}

	frustrationScore := frictionCount / totalInteractions

	return map[string]float64{
		"score": frustrationScore,
		"count": frictionCount,
	}
}

// estimateRageClickRisk predicts rage click likelihood
func (js *JourneySonar) estimateRageClickRisk(app *AppState) map[string]float64 {
	// Simulated rage click risk
	// Real impl would check for:
	// - Async actions without loading states
	// - Buttons without disabled states during processing
	// - Forms without validation feedback

	riskScore := 0.05 // Low default

	return map[string]float64{
		"probability": riskScore,
	}
}

// calculateBacktrackingProbability estimates user backtracking
func (js *JourneySonar) calculateBacktrackingProbability(app *AppState) map[string]float64 {
	// Simulated backtracking probability
	// Real impl would analyze:
	// - Multi-step forms without edit capability
	// - Confusing navigation
	// - Lack of progress indicators

	backtrackProb := 0.12 // Moderate default

	return map[string]float64{
		"probability": backtrackProb,
	}
}
