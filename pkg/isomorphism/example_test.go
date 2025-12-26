package isomorphism

import (
	"fmt"
	"testing"
)

// ============================================================================
// EXAMPLE TESTS - URBAN LENS USE CASES
// ============================================================================

func TestWasteCollectorToOperationsTranslation(t *testing.T) {
	// Create engine
	engine := NewIsomorphismEngine()

	// Define waste collector skills
	skills := []string{
		"route_optimization",
		"collection_scheduling",
		"capacity_planning",
		"sorting_efficiency",
	}

	// Translate to operations domain
	translations, err := engine.TranslateWasteCollectorSkills(skills)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	// Verify we got translations
	if len(translations) == 0 {
		t.Error("Expected translations, got none")
	}

	// Print results
	fmt.Println("\n=== Waste Collector → Operations Manager ===")
	for skill, targets := range translations {
		fmt.Printf("✓ %s → %v\n", skill, targets)
	}
}

func TestStreetVendorToSalesTranslation(t *testing.T) {
	engine := NewIsomorphismEngine()

	skills := []string{
		"location_selection",
		"customer_interaction",
		"inventory_management",
		"pricing_strategy",
	}

	translations, err := engine.TranslateStreetVendorSkills(skills)
	if err != nil {
		t.Fatalf("Translation failed: %v", err)
	}

	if len(translations) == 0 {
		t.Error("Expected translations, got none")
	}

	fmt.Println("\n=== Street Vendor → Sales Professional ===")
	for skill, targets := range translations {
		fmt.Printf("✓ %s → %v\n", skill, targets)
	}
}

func TestBridgeWalking(t *testing.T) {
	engine := NewIsomorphismEngine()

	// Create concepts
	source := engine.CreateConcept(
		"route_optimization",
		"Finding the shortest path to visit all collection points",
		DomainWasteManagement,
		[]string{"optimization", "spatial", "logistics"},
	)

	target := engine.CreateConcept(
		"process_optimization",
		"Streamlining workflows to maximize efficiency",
		DomainOperations,
		[]string{"optimization", "workflow", "efficiency"},
	)

	// Find bridge
	bridge, err := engine.FindBridge(*source, *target)
	if err != nil {
		t.Fatalf("Bridge walking failed: %v", err)
	}

	// Verify bridge properties
	if bridge.Strength < 0.7 {
		t.Errorf("Expected strong bridge (≥0.7), got %.2f", bridge.Strength)
	}

	if len(bridge.Geodesic) == 0 {
		t.Error("Expected geodesic waypoints, got none")
	}

	// Print bridge details
	fmt.Println("\n=== Bridge Walking ===")
	fmt.Printf("Source: %s (%s)\n", bridge.SourceConcept.Name, bridge.SourceConcept.Domain)
	fmt.Printf("Target: %s (%s)\n", bridge.TargetConcept.Name, bridge.TargetConcept.Domain)
	fmt.Printf("Strength: %.2f\n", bridge.Strength)
	fmt.Printf("Type: %s\n", bridge.IsomorphismType)
	fmt.Printf("Waypoints: %d\n", len(bridge.Geodesic))
	fmt.Printf("Evidence:\n")
	for _, ev := range bridge.Evidence {
		fmt.Printf("  - %s\n", ev)
	}

	// Evaluate quality
	quality := engine.EvaluateBridgeQuality(bridge)
	fmt.Printf("Quality (5 Timbres): %.3f\n", quality)

	// Quality depends on isomorphism type - pattern type is lower weight
	// Expect at least 0.50 for valid bridges
	if quality < 0.50 {
		t.Errorf("Expected quality ≥0.50, got %.3f", quality)
	}

	// Note: For structural isomorphism (weight 0.30), quality would be higher (~0.70-0.80)
}

func TestConceptEncoding(t *testing.T) {
	engine := NewIsomorphismEngine()

	concept := &Concept{
		Name:        "test_concept",
		Domain:      DomainOperations,
		Description: "A test concept for encoding verification",
		Tags:        []string{"test", "optimization"},
		Properties:  make(map[string]float64),
	}

	// Encode
	engine.EncodeConcept(concept)

	// Verify quaternion is normalized
	norm := concept.Quaternion.Norm()
	if norm < 0.99 || norm > 1.01 {
		t.Errorf("Expected norm ≈ 1.0, got %.3f", norm)
	}

	fmt.Println("\n=== Concept Encoding ===")
	fmt.Printf("Concept: %s\n", concept.Name)
	fmt.Printf("Quaternion: (%.3f, %.3f, %.3f, %.3f)\n",
		concept.Quaternion.W,
		concept.Quaternion.X,
		concept.Quaternion.Y,
		concept.Quaternion.Z,
	)
	fmt.Printf("Norm: %.3f\n", norm)
}

func TestMultipleBridgeBuilding(t *testing.T) {
	engine := NewIsomorphismEngine()

	// Create source concepts (waste management)
	sources := []*Concept{
		engine.CreateConcept("route_optimization", "Optimize collection routes", DomainWasteManagement, []string{"optimization"}),
		engine.CreateConcept("capacity_planning", "Plan waste collection capacity", DomainWasteManagement, []string{"planning"}),
	}

	// Create target concepts (operations)
	targets := []*Concept{
		engine.CreateConcept("process_optimization", "Optimize business processes", DomainOperations, []string{"optimization"}),
		engine.CreateConcept("resource_allocation", "Allocate operational resources", DomainOperations, []string{"planning"}),
	}

	// Convert to non-pointer slices
	sourcesNonPtr := make([]Concept, len(sources))
	targetsNonPtr := make([]Concept, len(targets))
	for i, s := range sources {
		sourcesNonPtr[i] = *s
	}
	for i, t := range targets {
		targetsNonPtr[i] = *t
	}

	// Build bridges (Williams batching)
	bridges, err := engine.BuildBridges(sourcesNonPtr, targetsNonPtr)
	if err != nil {
		t.Fatalf("Bridge building failed: %v", err)
	}

	expectedCount := len(sources) * len(targets)
	if len(bridges) != expectedCount {
		t.Errorf("Expected %d bridges, got %d", expectedCount, len(bridges))
	}

	fmt.Println("\n=== Multiple Bridge Building ===")
	fmt.Printf("Built %d bridges\n", len(bridges))
	for i, bridge := range bridges {
		fmt.Printf("Bridge %d: %s → %s (strength: %.2f)\n",
			i+1,
			bridge.SourceConcept.Name,
			bridge.TargetConcept.Name,
			bridge.Strength,
		)
	}

	// Filter by strength
	strongBridges := engine.FilterBridges(bridges, 0.7)
	fmt.Printf("Strong bridges (≥0.7): %d\n", len(strongBridges))
}

func TestCareerTransition(t *testing.T) {
	engine := NewIsomorphismEngine()

	targetDomains := []Domain{
		DomainOperations,
		DomainProductManagement,
		DomainSystemArchitecture,
	}

	matches, err := engine.SuggestCareerTransition(
		"waste_collector",
		DomainWasteManagement,
		targetDomains,
	)

	if err != nil {
		t.Fatalf("Career transition failed: %v", err)
	}

	if len(matches) == 0 {
		t.Error("Expected career matches, got none")
	}

	fmt.Println("\n=== Career Transition Suggestions ===")
	fmt.Println("Current: Waste Collector")
	fmt.Println("Suggested Roles:")
	for i, match := range matches {
		fmt.Printf("%d. %s (Domain: %s, Confidence: %.2f)\n",
			i+1,
			match.RoleName,
			match.Domain,
			match.Confidence,
		)
	}
}

// ============================================================================
// BENCHMARK TESTS
// ============================================================================

func BenchmarkConceptEncoding(b *testing.B) {
	engine := NewIsomorphismEngine()

	concept := &Concept{
		Name:        "benchmark_concept",
		Domain:      DomainOperations,
		Description: "A concept for benchmarking encoding performance",
		Tags:        []string{"benchmark", "test"},
		Properties:  make(map[string]float64),
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		engine.EncodeConcept(concept)
	}
}

func BenchmarkBridgeWalking(b *testing.B) {
	engine := NewIsomorphismEngine()

	source := engine.CreateConcept("source", "Source concept", DomainWasteManagement, []string{"test"})
	target := engine.CreateConcept("target", "Target concept", DomainOperations, []string{"test"})

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		engine.FindBridge(*source, *target)
	}
}

func BenchmarkTranslation(b *testing.B) {
	engine := NewIsomorphismEngine()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		engine.TranslateConcept("route_optimization", DomainWasteManagement, DomainOperations)
	}
}
