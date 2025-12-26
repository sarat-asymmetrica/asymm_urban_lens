// Package matching examples
package matching_test

import (
	"fmt"

	"github.com/asymmetrica/urbanlens/pkg/matching"
)

// Example_basicFuzzyMatching demonstrates basic fuzzy matching
func Example_basicFuzzyMatching() {
	// Create matcher
	matcher := matching.NewFuzzyMatcher()

	// Create patterns
	patterns := []matching.Pattern{
		*matching.NewPattern("p1", "error_check", "if err != nil { return err }", "error_handling", "Go"),
		*matching.NewPattern("p2", "nil_check", "if x == nil { return }", "validation", "Go"),
	}

	// Match input
	input := "if error != nil { return error }"
	matches, _ := matcher.Match(input, patterns)

	if len(matches) > 0 {
		fmt.Printf("Found %d match(es)\n", len(matches))
		fmt.Printf("Best match: %s (score: %.2f)\n", matches[0].Pattern.Name, matches[0].Score)
	}

	// Output:
	// Found 1 match(es)
	// Best match: error_check (score: 0.94)
}

// Example_templateEngine demonstrates template-based matching
func Example_templateEngine() {
	// Create template engine
	engine := matching.NewTemplateEngine()

	// Create template pattern
	template := "if {{var}} != nil { return {{func}}({{var}}) }"
	pattern := matching.NewPattern("error_pattern", "error_handling", template, "error_handling", "Go")
	engine.RegisterPattern(*pattern)

	// Instantiate template
	bindings := map[string]interface{}{
		"var":  "err",
		"func": "fmt.Errorf",
	}
	result, _ := engine.Instantiate(template, bindings)
	fmt.Println("Instantiated:", result)

	// Extract bindings from concrete code
	input := "if err != nil { return fmt.Errorf(err) }"
	extractedBindings, _ := engine.ExtractBindings(template, input)
	fmt.Printf("Extracted bindings: var=%v, func=%v\n", extractedBindings["var"], extractedBindings["func"])

	// Output:
	// Instantiated: if err != nil { return fmt.Errorf(err) }
	// Extracted bindings: var=err, func=fmt.Errorf
}

// Example_patternRanking demonstrates quality-based ranking
func Example_patternRanking() {
	// Create ranker
	ranker := matching.NewPatternRanker()

	// Create patterns with different qualities
	p1 := matching.NewPattern("p1", "high_quality", "code1", "error_handling", "Go")
	p1.Confidence = 0.9
	p1.Frequency = 100

	p2 := matching.NewPattern("p2", "low_quality", "code2", "error_handling", "Go")
	p2.Confidence = 0.3
	p2.Frequency = 5

	patterns := []*matching.Pattern{p2, p1} // Intentionally out of order

	// Rank patterns
	ranked := ranker.RankPatterns(patterns)

	for _, r := range ranked {
		fmt.Printf("Rank %d: %s (quality: %.3f)\n", r.Rank, r.Pattern.Name, r.QualityScore)
	}

	// Output:
	// Rank 1: high_quality (quality: 0.547)
	// Rank 2: low_quality (quality: 0.030)
}

// Example_standardPatterns demonstrates using pre-built patterns
func Example_standardPatterns() {
	// Get standard patterns for Go
	patterns := matching.GetStandardPatterns("Go")

	fmt.Printf("Loaded %d standard patterns\n", len(patterns))

	// List categories
	categories := make(map[string]bool)
	for _, p := range patterns {
		categories[p.Category] = true
	}

	fmt.Println("Categories:")
	for cat := range categories {
		fmt.Printf("  - %s\n", cat)
	}

	// Output:
	// Loaded 3 standard patterns
	// Categories:
	//   - error_handling
	//   - validation
	//   - control_flow
}

// Example_customConfig demonstrates custom matcher configuration
func Example_customConfig() {
	// Custom config with stricter thresholds
	config := matching.MatcherConfig{
		MinSimilarity:        0.80,  // Higher threshold
		FuzzyMatchThreshold:  0.90,  // Stricter fuzzy matching
		UseDigitalRootFilter: true,  // Enable Vedic optimization
		StructuralWeight:     0.50,  // Prefer structural similarity
		QuaternionWeight:     0.30,
		SemanticWeight:       0.20,
	}

	matcher := matching.NewFuzzyMatcherWithConfig(config)

	patterns := []matching.Pattern{
		*matching.NewPattern("p1", "test", "if err != nil { return err }", "error_handling", "Go"),
	}

	input := "if err != nil { return err }"
	matches, _ := matcher.Match(input, patterns)

	if len(matches) > 0 {
		fmt.Printf("Exact match found with score: %.2f\n", matches[0].Score)
	}

	// Output:
	// Exact match found with score: 1.00
}

// Example_multiTierMatching demonstrates the three-tier matching strategy
func Example_multiTierMatching() {
	matcher := matching.NewFuzzyMatcher()

	patterns := []matching.Pattern{
		*matching.NewPattern("p1", "exact", "if err != nil { return err }", "error_handling", "Go"),
		*matching.NewPattern("p2", "similar", "if error != nil { return error }", "error_handling", "Go"),
	}

	// Test exact match (Tier 1)
	input1 := "if err != nil { return err }"
	matches1, _ := matcher.Match(input1, patterns)
	if len(matches1) > 0 {
		fmt.Printf("Tier 1 (exact): algorithm=%s, score=%.2f\n",
			matches1[0].Context.AlgorithmUsed, matches1[0].Score)
	}

	// Test fuzzy match (Tier 2)
	input2 := "if error != nil { return error }"
	matches2, _ := matcher.Match(input2, patterns)
	if len(matches2) > 0 {
		// Filter for fuzzy matches
		for _, m := range matches2 {
			if m.Context.AlgorithmUsed == "fuzzy" {
				fmt.Printf("Tier 2 (fuzzy): algorithm=%s, score=%.2f\n",
					m.Context.AlgorithmUsed, m.Score)
				break
			}
		}
	}

	// Output:
	// Tier 1 (exact): algorithm=exact, score=1.00
	// Tier 2 (fuzzy): algorithm=fuzzy, score=1.00
}
