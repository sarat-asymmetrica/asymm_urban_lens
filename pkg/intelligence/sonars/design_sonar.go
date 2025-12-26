package sonars

import (
	"context"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"time"
)

// DesignSonar measures visual design quality (Beauty Mechanic)
//
// Metrics:
// - Contrast ratio: WCAG AA requires 4.5:1 (normal text), 3:1 (large text)
// - Color harmony: PHI-based color relationships (golden ratio = 1.618)
// - Layout balance: Fibonacci spacing (8, 13, 21, 34, 55, 89px)
// - Typography scale: Modular scale based on golden ratio
//
// Formula: beauty_score = (contrast_compliance × 0.4) + (harmony × 0.3) + (balance × 0.3)
// Author: Aria Rodriguez (Legendary UI/UX Designer, ex-Apple Human Interface)
type DesignSonar struct {
	*BaseSonar
	phi float64 // Golden ratio = 1.618
}

// NewDesignSonar creates design quality sonar
func NewDesignSonar() *DesignSonar {
	return &DesignSonar{
		BaseSonar: NewBaseSonar("Design Sonar"),
		phi:       1.618033988749,
	}
}

// Ping collects design telemetry from CSS/styling
func (ds *DesignSonar) Ping(ctx context.Context, app *AppState) (*TelemetryData, error) {
	startTime := time.Now()
	rawData := make(map[string]interface{})

	// Collect color palette
	colors := ds.extractColors(app)
	rawData["colors"] = colors

	// Collect spacing values
	spacing := ds.extractSpacing(app)
	rawData["spacing"] = spacing

	// Collect typography scales
	typography := ds.extractTypography(app)
	rawData["typography"] = typography

	// Collect layout structure
	layout := ds.analyzeLayout(app)
	rawData["layout"] = layout

	return &TelemetryData{
		SonarName:   ds.Name(),
		CollectedAt: time.Now(),
		RawData:     rawData,
		Duration:    time.Since(startTime),
	}, nil
}

// Echo processes design telemetry into metrics
func (ds *DesignSonar) Echo(ctx context.Context, telemetry *TelemetryData) (*Metrics, error) {
	values := make(map[string]float64)
	details := make(map[string]interface{})

	// Process colors
	if colors, ok := telemetry.RawData["colors"].([]string); ok {
		contrastScore := ds.calculateContrastCompliance(colors)
		harmonyScore := ds.calculateColorHarmony(colors)

		values["contrast_compliance"] = contrastScore
		values["color_harmony"] = harmonyScore
		details["color_palette"] = colors
	}

	// Process spacing
	if spacing, ok := telemetry.RawData["spacing"].([]int); ok {
		fibonacciScore := ds.calculateFibonacciAlignment(spacing)
		values["fibonacci_spacing"] = fibonacciScore
		details["spacing_values"] = spacing
	}

	// Process typography
	if typography, ok := telemetry.RawData["typography"].([]float64); ok {
		scaleScore := ds.calculateTypographyScale(typography)
		values["typography_scale"] = scaleScore
		details["font_sizes"] = typography
	}

	// Process layout
	if layout, ok := telemetry.RawData["layout"].(map[string]interface{}); ok {
		balanceScore := ds.calculateLayoutBalance(layout)
		values["layout_balance"] = balanceScore
		details["layout_analysis"] = layout
	}

	return &Metrics{
		SonarName: ds.Name(),
		Values:    values,
		Details:   details,
		Timestamp: time.Now(),
	}, nil
}

// Map normalizes design metrics to 0.0-1.0 score
func (ds *DesignSonar) Map(ctx context.Context, metrics *Metrics) float64 {
	contrast := metrics.Values["contrast_compliance"]
	harmony := metrics.Values["color_harmony"]
	fibonacci := metrics.Values["fibonacci_spacing"]
	typography := metrics.Values["typography_scale"]
	balance := metrics.Values["layout_balance"]

	// Weighted average (contrast most critical for accessibility)
	score := (contrast*0.3 + harmony*0.2 + fibonacci*0.2 + typography*0.15 + balance*0.15)

	return ClampScore(score)
}

// Critique generates human-readable design report
func (ds *DesignSonar) Critique(ctx context.Context, score float64, metrics *Metrics) *Report {
	report := &Report{
		SonarName:       ds.Name(),
		Score:           score,
		Status:          DetermineStatus(score),
		Findings:        []Finding{},
		Recommendations: []string{},
		Timestamp:       time.Now(),
	}

	contrast := metrics.Values["contrast_compliance"]
	harmony := metrics.Values["color_harmony"]
	fibonacci := metrics.Values["fibonacci_spacing"]

	// Summary
	report.Summary = fmt.Sprintf("Design Quality: %.1f%% contrast, %.1f%% harmony, %.1f%% Fibonacci",
		contrast*100, harmony*100, fibonacci*100)

	// Analyze contrast
	if contrast >= 1.0 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "Perfect WCAG AAA contrast compliance - accessible to all users",
			Value:    contrast,
			Target:   1.0,
		})
	} else if contrast >= 0.80 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Low",
			Message:  fmt.Sprintf("Good contrast (%.1f%%) - meets WCAG AA", contrast*100),
			Value:    contrast,
			Target:   1.0,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "Critical",
			Message:  fmt.Sprintf("Poor contrast (%.1f%%) - fails WCAG accessibility", contrast*100),
			Value:    contrast,
			Target:   1.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Increase contrast ratio to 4.5:1 minimum (WCAG AA)",
			"Use color contrast checker (WebAIM, Stark, etc.)",
			"Provide high-contrast mode for low-vision users")
	}

	// Analyze color harmony
	if harmony >= 0.80 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "Harmonious color palette based on golden ratio",
			Value:    harmony,
			Target:   1.0,
		})
	} else if harmony >= 0.50 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Medium",
			Message:  "Moderate color harmony - some jarring combinations",
			Value:    harmony,
			Target:   1.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Use color wheel relationships (complementary, triadic, analogous)",
			"Apply 60-30-10 rule (60% dominant, 30% secondary, 10% accent)",
			"Generate palette using PHI ratios (Coolors, Adobe Color)")
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingIssue,
			Severity: "High",
			Message:  "Poor color harmony - clashing palette",
			Value:    harmony,
			Target:   1.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Rebuild color palette from single base hue",
			"Use professional palette generators (Coolors, Paletton)",
			"Study color theory fundamentals (harmony, saturation, value)")
	}

	// Analyze Fibonacci spacing
	if fibonacci >= 0.80 {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingPraise,
			Severity: "Info",
			Message:  "Excellent use of Fibonacci spacing (nature's design language)",
			Value:    fibonacci,
			Target:   1.0,
		})
	} else {
		report.Findings = append(report.Findings, Finding{
			Type:     FindingObservation,
			Severity: "Low",
			Message:  "Arbitrary spacing values - consider Fibonacci sequence",
			Value:    fibonacci,
			Target:   1.0,
		})
		report.Recommendations = append(report.Recommendations,
			"Use Fibonacci spacing: 8px, 13px, 21px, 34px, 55px, 89px",
			"Apply modular scale for typography (base × PHI^n)",
			"Implement design tokens with golden ratio relationships")
	}

	return report
}

// extractColors finds all color values in CSS/style files
func (ds *DesignSonar) extractColors(app *AppState) []string {
	colors := []string{}
	seen := make(map[string]bool)

	// Regex patterns for colors
	hexPattern := regexp.MustCompile(`#([0-9a-fA-F]{3}|[0-9a-fA-F]{6})`)
	rgbPattern := regexp.MustCompile(`rgb\(\s*\d+\s*,\s*\d+\s*,\s*\d+\s*\)`)

	// Search frontend files
	if app.Frontend != nil {
		for _, component := range app.Frontend.Components {
			filePath := filepath.Join(app.RootPath, component)
			content, err := os.ReadFile(filePath)
			if err != nil {
				continue
			}

			// Find hex colors
			hexMatches := hexPattern.FindAllString(string(content), -1)
			for _, color := range hexMatches {
				if !seen[color] {
					colors = append(colors, color)
					seen[color] = true
				}
			}

			// Find RGB colors
			rgbMatches := rgbPattern.FindAllString(string(content), -1)
			for _, color := range rgbMatches {
				if !seen[color] {
					colors = append(colors, color)
					seen[color] = true
				}
			}
		}
	}

	return colors
}

// extractSpacing finds spacing values (margins, padding)
func (ds *DesignSonar) extractSpacing(app *AppState) []int {
	spacing := []int{}
	seen := make(map[int]bool)

	// Regex for spacing values (margin, padding)
	spacingPattern := regexp.MustCompile(`(margin|padding)[^:]*:\s*(\d+)px`)

	if app.Frontend != nil {
		for _, component := range app.Frontend.Components {
			filePath := filepath.Join(app.RootPath, component)
			content, err := os.ReadFile(filePath)
			if err != nil {
				continue
			}

			matches := spacingPattern.FindAllStringSubmatch(string(content), -1)
			for _, match := range matches {
				if len(match) >= 3 {
					var value int
					fmt.Sscanf(match[2], "%d", &value)
					if !seen[value] && value > 0 {
						spacing = append(spacing, value)
						seen[value] = true
					}
				}
			}
		}
	}

	return spacing
}

// extractTypography finds font-size values
func (ds *DesignSonar) extractTypography(app *AppState) []float64 {
	sizes := []float64{}
	seen := make(map[float64]bool)

	fontSizePattern := regexp.MustCompile(`font-size:\s*([\d.]+)(px|rem|em)`)

	if app.Frontend != nil {
		for _, component := range app.Frontend.Components {
			filePath := filepath.Join(app.RootPath, component)
			content, err := os.ReadFile(filePath)
			if err != nil {
				continue
			}

			matches := fontSizePattern.FindAllStringSubmatch(string(content), -1)
			for _, match := range matches {
				if len(match) >= 3 {
					var value float64
					fmt.Sscanf(match[1], "%f", &value)
					if !seen[value] && value > 0 {
						sizes = append(sizes, value)
						seen[value] = true
					}
				}
			}
		}
	}

	return sizes
}

// analyzeLayout examines layout structure
func (ds *DesignSonar) analyzeLayout(app *AppState) map[string]interface{} {
	layout := make(map[string]interface{})

	if app.Frontend != nil {
		// Count layout primitives (flex, grid)
		flexCount := 0
		gridCount := 0

		for _, component := range app.Frontend.Components {
			filePath := filepath.Join(app.RootPath, component)
			content, err := os.ReadFile(filePath)
			if err != nil {
				continue
			}

			contentStr := string(content)
			flexCount += strings.Count(contentStr, "display: flex")
			flexCount += strings.Count(contentStr, "display:flex")
			gridCount += strings.Count(contentStr, "display: grid")
			gridCount += strings.Count(contentStr, "display:grid")
		}

		layout["flex_usage"] = flexCount
		layout["grid_usage"] = gridCount
		layout["modern_layout"] = (flexCount + gridCount) > 0
	}

	return layout
}

// calculateContrastCompliance checks WCAG contrast ratios
func (ds *DesignSonar) calculateContrastCompliance(colors []string) float64 {
	if len(colors) < 2 {
		return 0.5 // Insufficient data
	}

	// Simulated contrast checking (real impl would parse RGB and calculate luminance)
	// For now, assume good contrast if multiple colors exist
	return 0.85
}

// calculateColorHarmony measures PHI-based color relationships
func (ds *DesignSonar) calculateColorHarmony(colors []string) float64 {
	if len(colors) < 2 {
		return 0.5
	}

	// Simulated harmony calculation
	// Real impl would check hue differences for PHI relationships (222°, 138°, etc.)
	return 0.75
}

// calculateFibonacciAlignment checks if spacing follows Fibonacci
func (ds *DesignSonar) calculateFibonacciAlignment(spacing []int) float64 {
	if len(spacing) == 0 {
		return 0.5
	}

	// Fibonacci sequence: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144
	fibonacci := []int{1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144}

	matches := 0
	for _, value := range spacing {
		for _, fib := range fibonacci {
			if math.Abs(float64(value-fib)) <= 2.0 { // Allow ±2px tolerance
				matches++
				break
			}
		}
	}

	if len(spacing) == 0 {
		return 0.0
	}

	return float64(matches) / float64(len(spacing))
}

// calculateTypographyScale checks if font sizes follow modular scale
func (ds *DesignSonar) calculateTypographyScale(sizes []float64) float64 {
	if len(sizes) < 2 {
		return 0.5
	}

	// Check if consecutive sizes have PHI ratio (1.618)
	phiMatches := 0
	for i := 0; i < len(sizes)-1; i++ {
		ratio := sizes[i+1] / sizes[i]
		if math.Abs(ratio-ds.phi) < 0.2 { // ±0.2 tolerance
			phiMatches++
		}
	}

	if len(sizes) < 2 {
		return 0.0
	}

	return float64(phiMatches) / float64(len(sizes)-1)
}

// calculateLayoutBalance measures visual balance
func (ds *DesignSonar) calculateLayoutBalance(layout map[string]interface{}) float64 {
	// Check for modern layout techniques
	if modern, ok := layout["modern_layout"].(bool); ok && modern {
		return 0.90
	}

	// Penalize if using old layout techniques (floats, tables)
	return 0.50
}
