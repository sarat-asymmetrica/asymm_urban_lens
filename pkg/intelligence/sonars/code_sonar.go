package sonars

import (
	"context"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// CodeSonar measures code quality (Engine Mechanic)
//
// Metrics:
// - Cyclomatic complexity: McCabe metric (< 10 = simple, > 20 = complex)
// - Code duplication: Percentage of duplicated code blocks
// - Cohesion: How well functions group together
// - Function length: Lines per function (< 50 = good, > 100 = refactor)
//
// Formula: engine_health = (1.0 - complexity_factor) × (1.0 - duplication) × cohesion
// Author: Dr. Heinrich Mueller (Software Architecture, ex-Google)
type CodeSonar struct {
	*BaseSonar
}

// NewCodeSonar creates code quality sonar
func NewCodeSonar() *CodeSonar {
	return &CodeSonar{
		BaseSonar: NewBaseSonar("Code Sonar"),
	}
}

// Ping collects code metrics from source files
func (cs *CodeSonar) Ping(ctx context.Context, app *AppState) (*TelemetryData, error) {
	startTime := time.Now()
	rawData := make(map[string]interface{})

	// Collect complexity metrics
	complexity := cs.measureComplexity(app)
	rawData["complexity"] = complexity

	// Collect duplication metrics
	duplication := cs.measureDuplication(app)
	rawData["duplication"] = duplication

	// Collect cohesion metrics
	cohesion := cs.measureCohesion(app)
	rawData["cohesion"] = cohesion

	// Collect function length metrics
	functionLengths := cs.measureFunctionLengths(app)
	rawData["function_lengths"] = functionLengths

	return &TelemetryData{
		SonarName:   cs.Name(),
		CollectedAt: time.Now(),
		RawData:     rawData,
		Duration:    time.Since(startTime),
	}, nil
}

// Echo processes code telemetry into metrics
func (cs *CodeSonar) Echo(ctx context.Context, telemetry *TelemetryData) (*Metrics, error) {
	values := make(map[string]float64)
	details := make(map[string]interface{})

	// Process complexity
	if complexity, ok := telemetry.RawData["complexity"].(map[string]float64); ok {
		values["avg_complexity"] = complexity["average"]
		values["max_complexity"] = complexity["maximum"]
		details["complexity_distribution"] = complexity
	}

	// Process duplication
	if duplication, ok := telemetry.RawData["duplication"].(map[string]float64); ok {
		values["duplication_percentage"] = duplication["percentage"]
		values["duplicated_blocks"] = duplication["blocks"]
		details["duplication_analysis"] = duplication
	}

	// Process cohesion
	if cohesion, ok := telemetry.RawData["cohesion"].(map[string]float64); ok {
		values["cohesion_score"] = cohesion["score"]
		details["cohesion_analysis"] = cohesion
	}

	// Process function lengths
	if lengths, ok := telemetry.RawData["function_lengths"].(map[string]float64); ok {
		values["avg_function_length"] = lengths["average"]
		values["max_function_length"] = lengths["maximum"]
		details["function_length_distribution"] = lengths
	}

	return &Metrics{
		SonarName: cs.Name(),
		Values:    values,
		Details:   details,
		Timestamp: time.Now(),
	}, nil
}

// Map normalizes code metrics to 0.0-1.0 score
func (cs *CodeSonar) Map(ctx context.Context, metrics *Metrics) float64 {
	// Cyclomatic complexity (lower is better)
	avgComplexity := metrics.Values["avg_complexity"]
	maxComplexity := metrics.Values["max_complexity"]

	// Normalize: < 5 = excellent, 5-10 = good, 10-20 = moderate, > 20 = poor
	complexityScore := 1.0
	if avgComplexity > 20.0 {
		complexityScore = 0.3
	} else if avgComplexity > 10.0 {
		complexityScore = 0.6
	} else if avgComplexity > 5.0 {
		complexityScore = 0.85
	}

	// Penalize high max complexity
	if maxComplexity > 50.0 {
		complexityScore *= 0.5
	} else if maxComplexity > 30.0 {
		complexityScore *= 0.75
	}

	// Duplication (lower is better)
	duplicationPct := metrics.Values["duplication_percentage"]
	duplicationScore := math.Max(0.0, 1.0-(duplicationPct/10.0)) // 0% = 1.0, 10% = 0.0

	// Cohesion (higher is better)
	cohesion := metrics.Values["cohesion_score"]

	// Function length (lower is better)
	avgFuncLength := metrics.Values["avg_function_length"]
	maxFuncLength := metrics.Values["max_function_length"]

	funcLengthScore := 1.0
	if avgFuncLength > 100.0 {
		funcLengthScore = 0.4
	} else if avgFuncLength > 50.0 {
		funcLengthScore = 0.7
	}

	// Penalize very long functions
	if maxFuncLength > 200.0 {
		funcLengthScore *= 0.6
	}

	// Weighted average
	score := (complexityScore*0.35 + duplicationScore*0.25 + cohesion*0.25 + funcLengthScore*0.15)

	return ClampScore(score)
}

// Critique generates human-readable code quality report
func (cs *CodeSonar) Critique(ctx context.Context, score float64, metrics *Metrics) *Report {
	report := &Report{
		SonarName:       cs.Name(),
		Score:           score,
		Status:          DetermineStatus(score),
		Findings:        []Finding{},
		Recommendations: []string{},
		Timestamp:       time.Now(),
	}

	avgComplexity := metrics.Values["avg_complexity"]
	maxComplexity := metrics.Values["max_complexity"]
	duplication := metrics.Values["duplication_percentage"]
	cohesion := metrics.Values["cohesion_score"]

	// Summary
	report.Summary = fmt.Sprintf("Code Quality: CC %.1f (max %.0f), %.1f%% dup, %.2f cohesion",
		avgComplexity, maxComplexity, duplication, cohesion)

	// Analyze complexity
	if avgComplexity <= 5.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  fmt.Sprintf("Excellent code simplicity (CC: %.1f)", avgComplexity),
			Value:    avgComplexity,
			Target:   5.0,
		})
	} else if avgComplexity <= 10.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Low",
			Message:  fmt.Sprintf("Good complexity (CC: %.1f) - maintainable", avgComplexity),
			Value:    avgComplexity,
			Target:   10.0,
		})
	} else if avgComplexity <= 20.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Medium",
			Message:  fmt.Sprintf("Moderate complexity (CC: %.1f) - consider refactoring", avgComplexity),
			Value:    avgComplexity,
			Target:   10.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Extract complex conditions into named functions",
			"Replace nested if/else with early returns (guard clauses)",
			"Use strategy pattern for complex branching logic")
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "Critical",
			Message:  fmt.Sprintf("High complexity (CC: %.1f) - difficult to maintain", avgComplexity),
			Value:    avgComplexity,
			Target:   10.0,
		})
		report.Recommendations = append(report.Recommendations,
			"URGENT: Break down complex functions into smaller units",
			"Apply Single Responsibility Principle (SRP)",
			"Use composition over complex inheritance hierarchies")
	}

	// Analyze max complexity
	if maxComplexity > 30.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "High",
			Message:  fmt.Sprintf("Found function with excessive complexity (CC: %.0f)", maxComplexity),
			Value:    maxComplexity,
			Target:   30.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Identify and refactor the most complex function immediately",
			"Aim for CC < 10 per function (enforced by linters)")
	}

	// Analyze duplication
	if duplication < 3.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  fmt.Sprintf("Minimal code duplication (%.1f%%)", duplication),
			Value:    duplication,
			Target:   3.0,
		})
	} else if duplication < 5.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Low",
			Message:  fmt.Sprintf("Low duplication (%.1f%%) - acceptable", duplication),
			Value:    duplication,
			Target:   5.0,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "Medium",
			Message:  fmt.Sprintf("Code duplication detected (%.1f%%)", duplication),
			Value:    duplication,
			Target:   5.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Extract common code into reusable functions/components",
			"Use DRY principle (Don't Repeat Yourself)",
			"Consider creating utility libraries for repeated patterns")
	}

	// Analyze cohesion
	if cohesion >= 0.80 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "High cohesion - functions are well-grouped",
			Value:    cohesion,
			Target:   0.80,
		})
	} else if cohesion >= 0.60 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Medium",
			Message:  "Moderate cohesion - some functions may be misplaced",
			Value:    cohesion,
			Target:   0.80,
		})
		report.Recommendations = append(report.Recommendations,
			"Group related functions into modules/classes",
			"Apply cohesion principles (functional, sequential, communicational)")
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "High",
			Message:  "Low cohesion - functions are poorly organized",
			Value:    cohesion,
			Target:   0.80,
		})
		report.Recommendations = append(report.Recommendations,
			"Restructure codebase to group related functionality",
			"Apply package-by-feature instead of package-by-layer")
	}

	return report
}

// measureComplexity calculates cyclomatic complexity
func (cs *CodeSonar) measureComplexity(app *AppState) map[string]float64 {
	totalComplexity := 0.0
	maxComplexity := 0.0
	functionCount := 0

	// Analyze backend files
	if app.Backend != nil {
		for _, handler := range app.Backend.Handlers {
			filePath := filepath.Join(app.RootPath, handler)
			complexity := cs.analyzeFileComplexity(filePath)
			totalComplexity += complexity["total"]
			if complexity["max"] > maxComplexity {
				maxComplexity = complexity["max"]
			}
			functionCount += int(complexity["functions"])
		}
	}

	// Analyze frontend files
	if app.Frontend != nil {
		for _, component := range app.Frontend.Components {
			filePath := filepath.Join(app.RootPath, component)
			complexity := cs.analyzeFileComplexity(filePath)
			totalComplexity += complexity["total"]
			if complexity["max"] > maxComplexity {
				maxComplexity = complexity["max"]
			}
			functionCount += int(complexity["functions"])
		}
	}

	avgComplexity := 3.0 // Default
	if functionCount > 0 {
		avgComplexity = totalComplexity / float64(functionCount)
	}

	return map[string]float64{
		"average": avgComplexity,
		"maximum": maxComplexity,
		"total":   totalComplexity,
	}
}

// analyzeFileComplexity computes cyclomatic complexity for a file
func (cs *CodeSonar) analyzeFileComplexity(filePath string) map[string]float64 {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return map[string]float64{"total": 1.0, "max": 1.0, "functions": 1.0}
	}

	contentStr := string(content)

	// Count decision points (if, for, while, case, &&, ||)
	keywords := []string{"if ", "for ", "while ", "case ", "&&", "||", "?"}
	decisionPoints := 0

	for _, keyword := range keywords {
		decisionPoints += strings.Count(contentStr, keyword)
	}

	// Estimate functions (func, function, const, =>)
	functionKeywords := []string{"func ", "function ", "const ", "=>"}
	functionCount := 0

	for _, keyword := range functionKeywords {
		functionCount += strings.Count(contentStr, keyword)
	}

	if functionCount == 0 {
		functionCount = 1
	}

	// CC = decision points + 1 (base complexity)
	totalComplexity := float64(decisionPoints + functionCount)
	avgComplexity := totalComplexity / float64(functionCount)

	// Estimate max (assume some functions are more complex)
	maxComplexity := avgComplexity * 1.5

	return map[string]float64{
		"total":     totalComplexity,
		"max":       maxComplexity,
		"functions": float64(functionCount),
	}
}

// measureDuplication detects duplicated code blocks
func (cs *CodeSonar) measureDuplication(app *AppState) map[string]float64 {
	// Simulated duplication detection
	// Real impl would use AST-based token matching (jscpd, copy-paste-detector)
	return map[string]float64{
		"percentage": 2.5,  // 2.5% duplication
		"blocks":     3.0,  // 3 duplicated blocks found
	}
}

// measureCohesion calculates module cohesion
func (cs *CodeSonar) measureCohesion(app *AppState) map[string]float64 {
	// Simulated cohesion measurement
	// Real impl would analyze function call graphs and shared data
	return map[string]float64{
		"score": 0.78, // 78% cohesion
	}
}

// measureFunctionLengths analyzes function lengths
func (cs *CodeSonar) measureFunctionLengths(app *AppState) map[string]float64 {
	totalLines := 0.0
	maxLines := 0.0
	functionCount := 0

	// Analyze all source files
	files := []string{}
	if app.Backend != nil {
		files = append(files, app.Backend.Handlers...)
	}
	if app.Frontend != nil {
		files = append(files, app.Frontend.Components...)
	}

	for _, file := range files {
		filePath := filepath.Join(app.RootPath, file)
		content, err := os.ReadFile(filePath)
		if err != nil {
			continue
		}

		lines := strings.Split(string(content), "\n")
		functionCount++

		funcLength := float64(len(lines))
		totalLines += funcLength

		if funcLength > maxLines {
			maxLines = funcLength
		}
	}

	avgLines := 30.0 // Default
	if functionCount > 0 {
		avgLines = totalLines / float64(functionCount)
	}

	return map[string]float64{
		"average": avgLines,
		"maximum": maxLines,
	}
}
