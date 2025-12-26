package isomorphism

import (
	"fmt"
	"strings"
)

// ============================================================================
// ANALOGY GENERATOR - STRUCTURE-BASED ANALOGY DISCOVERY
// ============================================================================

// AnalogyGenerator discovers analogies via structural pattern matching
// Algorithm: Structure Mapping Theory (Gentner, 1983) + Quaternion similarity
//
// Core Insight: Analogies are isomorphisms between relational structures
//   - Surface similarity (attributes) is LOW priority
//   - Structural similarity (relations) is HIGH priority
//
// Example Analogy:
//   "Solar system is to sun as atom is to nucleus"
//   Structure: [central_body, orbiting_bodies, gravitational_force]
//   Maps to:   [nucleus, electrons, electromagnetic_force]
type AnalogyGenerator struct {
	translator     *TranslationEngine  // Domain translator
	structureMapper *StructureMapper   // Isomorphism detector
	patternLibrary map[string]Pattern  // Known patterns
}

// NewAnalogyGenerator creates a new analogy generator
func NewAnalogyGenerator(translator *TranslationEngine, mapper *StructureMapper) *AnalogyGenerator {
	gen := &AnalogyGenerator{
		translator:      translator,
		structureMapper: mapper,
		patternLibrary:  make(map[string]Pattern),
	}

	// Initialize common patterns
	gen.initializePatterns()

	return gen
}

// ============================================================================
// ANALOGY GENERATION
// ============================================================================

// GenerateAnalogy creates an analogy between two domains
// Returns: "A is to B as C is to D" analogies
func (ag *AnalogyGenerator) GenerateAnalogy(sourcePattern Pattern, targetDomain Domain) (*Analogy, error) {
	// Find matching pattern in target domain
	targetPattern, err := ag.findMatchingPattern(sourcePattern, targetDomain)
	if err != nil {
		return nil, fmt.Errorf("no matching pattern found: %w", err)
	}

	// Build element mapping
	mapping, confidence := ag.buildMapping(sourcePattern, targetPattern)

	// Determine isomorphism type
	isoType := ag.determineIsomorphismType(sourcePattern, targetPattern)

	// Generate explanation
	explanation := ag.generateExplanation(sourcePattern, targetPattern, mapping)

	analogy := &Analogy{
		SourcePattern: sourcePattern,
		TargetPattern: targetPattern,
		Mapping:       mapping,
		Confidence:    confidence,
		Type:          isoType,
		Explanation:   explanation,
	}

	return analogy, nil
}

// GenerateMultipleAnalogies generates analogies for multiple target domains
func (ag *AnalogyGenerator) GenerateMultipleAnalogies(sourcePattern Pattern, targetDomains []Domain) ([]*Analogy, error) {
	analogies := make([]*Analogy, 0, len(targetDomains))

	for _, domain := range targetDomains {
		analogy, err := ag.GenerateAnalogy(sourcePattern, domain)
		if err != nil {
			// Skip domains without matching patterns
			continue
		}
		analogies = append(analogies, analogy)
	}

	if len(analogies) == 0 {
		return nil, fmt.Errorf("no analogies found for any target domain")
	}

	return analogies, nil
}

// ============================================================================
// PATTERN MATCHING
// ============================================================================

// findMatchingPattern finds a pattern in target domain that matches source pattern
func (ag *AnalogyGenerator) findMatchingPattern(source Pattern, targetDomain Domain) (Pattern, error) {
	bestMatch := Pattern{}
	bestScore := 0.0

	// Search pattern library for target domain patterns
	for _, pattern := range ag.patternLibrary {
		if pattern.Domain != targetDomain {
			continue
		}

		// Check structural similarity
		score := ag.patternSimilarity(source, pattern)

		if score > bestScore {
			bestScore = score
			bestMatch = pattern
		}
	}

	if bestScore < 0.618 { // PHI threshold
		return Pattern{}, fmt.Errorf("no pattern with sufficient similarity (best: %.2f)", bestScore)
	}

	return bestMatch, nil
}

// patternSimilarity computes structural similarity between patterns
func (ag *AnalogyGenerator) patternSimilarity(p1, p2 Pattern) float64 {
	// Three similarity dimensions (weighted)

	// 1. Element count similarity (30%)
	elementRatio := float64(min(len(p1.Elements), len(p2.Elements))) / float64(max(len(p1.Elements), len(p2.Elements)))

	// 2. Relation structure similarity (50%) - MOST IMPORTANT
	relationSim := ag.relationSimilarity(p1, p2)

	// 3. Invariant preservation (20%)
	invariantSim := ag.invariantSimilarity(p1, p2)

	// Weighted combination
	similarity := 0.3*elementRatio + 0.5*relationSim + 0.2*invariantSim

	return similarity
}

// relationSimilarity compares relation structures
func (ag *AnalogyGenerator) relationSimilarity(p1, p2 Pattern) float64 {
	// Count matching relation patterns
	matches := 0
	total := max(len(p1.Relations), len(p2.Relations))

	if total == 0 {
		return 1.0 // Both have no relations
	}

	// Check for similar relation types
	for _, targets1 := range p1.Relations {
		for _, targets2 := range p2.Relations {
			// Check if relation structures are similar
			if len(targets1) == len(targets2) {
				matches++
			}
		}
	}

	return float64(matches) / float64(total)
}

// invariantSimilarity checks if structural invariants are preserved
func (ag *AnalogyGenerator) invariantSimilarity(p1, p2 Pattern) float64 {
	// Count matching invariants
	matches := 0
	total := max(len(p1.Invariants), len(p2.Invariants))

	if total == 0 {
		return 1.0 // No invariants to check
	}

	for _, inv1 := range p1.Invariants {
		for _, inv2 := range p2.Invariants {
			// Simple string matching (can be improved with semantic similarity)
			if strings.Contains(strings.ToLower(inv1), strings.ToLower(inv2)) ||
				strings.Contains(strings.ToLower(inv2), strings.ToLower(inv1)) {
				matches++
			}
		}
	}

	if matches > total {
		matches = total // Cap at 100%
	}

	return float64(matches) / float64(total)
}

// ============================================================================
// MAPPING CONSTRUCTION
// ============================================================================

// buildMapping constructs element mapping between patterns
func (ag *AnalogyGenerator) buildMapping(source, target Pattern) (map[string]string, float64) {
	mapping := make(map[string]string)
	totalConfidence := 0.0
	count := 0

	// Use quaternion similarity to map elements
	for i, sourceElem := range source.Elements {
		if i >= len(target.Elements) {
			break // No more target elements
		}

		targetElem := target.Elements[i]
		mapping[sourceElem] = targetElem

		// Compute mapping confidence (would use concept similarity in practice)
		confidence := 0.8 // Placeholder
		totalConfidence += confidence
		count++
	}

	avgConfidence := 1.0
	if count > 0 {
		avgConfidence = totalConfidence / float64(count)
	}

	return mapping, avgConfidence
}

// ============================================================================
// EXPLANATION GENERATION
// ============================================================================

// generateExplanation creates human-readable analogy explanation
func (ag *AnalogyGenerator) generateExplanation(source, target Pattern, mapping map[string]string) string {
	parts := make([]string, 0)

	parts = append(parts, fmt.Sprintf("Pattern '%s' (%s domain) is analogous to pattern '%s' (%s domain):",
		source.Name, source.Domain, target.Name, target.Domain))

	parts = append(parts, "\nElement mappings:")
	for sourceElem, targetElem := range mapping {
		parts = append(parts, fmt.Sprintf("  - %s → %s", sourceElem, targetElem))
	}

	if len(source.Invariants) > 0 || len(target.Invariants) > 0 {
		parts = append(parts, "\nStructural invariants preserved:")
		for _, inv := range source.Invariants {
			parts = append(parts, fmt.Sprintf("  - %s", inv))
		}
	}

	return strings.Join(parts, "\n")
}

// ============================================================================
// ISOMORPHISM TYPE DETECTION
// ============================================================================

// determineIsomorphismType classifies the analogy type
func (ag *AnalogyGenerator) determineIsomorphismType(source, target Pattern) IsomorphismType {
	// Analyze patterns to determine type

	// Check for structural similarity (same hierarchy)
	if ag.hasStructuralMatch(source, target) {
		return IsomorphismStructural
	}

	// Check for functional similarity (same purpose)
	if ag.hasFunctionalMatch(source, target) {
		return IsomorphismFunctional
	}

	// Check for relational similarity (same relationships)
	if ag.hasRelationalMatch(source, target) {
		return IsomorphismRelational
	}

	// Default to pattern-based
	return IsomorphismPatternBased
}

// hasStructuralMatch checks for structural similarity
func (ag *AnalogyGenerator) hasStructuralMatch(source, target Pattern) bool {
	// Same number of elements and similar hierarchy
	return len(source.Elements) == len(target.Elements) &&
		len(source.Relations) == len(target.Relations)
}

// hasFunctionalMatch checks for functional similarity
func (ag *AnalogyGenerator) hasFunctionalMatch(source, target Pattern) bool {
	// Check for functional keywords in pattern names/descriptions
	functionalKeywords := []string{"function", "purpose", "goal", "outcome"}

	sourceName := strings.ToLower(source.Name)
	targetName := strings.ToLower(target.Name)

	for _, keyword := range functionalKeywords {
		if strings.Contains(sourceName, keyword) && strings.Contains(targetName, keyword) {
			return true
		}
	}

	return false
}

// hasRelationalMatch checks for relational similarity
func (ag *AnalogyGenerator) hasRelationalMatch(source, target Pattern) bool {
	// Similar relation structures
	return ag.relationSimilarity(source, target) > 0.7
}

// ============================================================================
// PATTERN LIBRARY INITIALIZATION
// ============================================================================

// initializePatterns populates the pattern library with common patterns
func (ag *AnalogyGenerator) initializePatterns() {
	// Hierarchical pattern (universal)
	ag.patternLibrary["hierarchical_structure"] = Pattern{
		Name:     "hierarchical_structure",
		Domain:   "", // Universal
		Elements: []string{"root", "intermediate", "leaf"},
		Relations: map[string][]string{
			"root":         {"intermediate"},
			"intermediate": {"leaf"},
		},
		Invariants: []string{"transitive_hierarchy", "single_root"},
	}

	// Sequential pattern (universal)
	ag.patternLibrary["sequential_process"] = Pattern{
		Name:     "sequential_process",
		Domain:   "", // Universal
		Elements: []string{"start", "process", "end"},
		Relations: map[string][]string{
			"start":   {"process"},
			"process": {"end"},
		},
		Invariants: []string{"ordered_sequence", "no_cycles"},
	}

	// Optimization pattern (operations, programming)
	ag.patternLibrary["optimization_loop"] = Pattern{
		Name:     "optimization_loop",
		Domain:   DomainOperations,
		Elements: []string{"measure", "analyze", "improve", "verify"},
		Relations: map[string][]string{
			"measure": {"analyze"},
			"analyze": {"improve"},
			"improve": {"verify"},
			"verify":  {"measure"}, // Cycle
		},
		Invariants: []string{"continuous_improvement", "feedback_loop"},
	}

	// Waste collection route pattern (urban)
	ag.patternLibrary["route_optimization"] = Pattern{
		Name:     "route_optimization",
		Domain:   DomainWasteManagement,
		Elements: []string{"start_depot", "collection_points", "optimization_algorithm", "end_depot"},
		Relations: map[string][]string{
			"start_depot":            {"collection_points"},
			"collection_points":      {"optimization_algorithm"},
			"optimization_algorithm": {"end_depot"},
		},
		Invariants: []string{"minimize_total_distance", "visit_all_points"},
	}

	// Corresponding operations pattern
	ag.patternLibrary["process_optimization_ops"] = Pattern{
		Name:     "process_optimization",
		Domain:   DomainOperations,
		Elements: []string{"initial_state", "process_steps", "optimization_engine", "final_state"},
		Relations: map[string][]string{
			"initial_state":       {"process_steps"},
			"process_steps":       {"optimization_engine"},
			"optimization_engine": {"final_state"},
		},
		Invariants: []string{"minimize_total_cost", "complete_all_steps"},
	}

	// Dance choreography pattern
	ag.patternLibrary["dance_choreography"] = Pattern{
		Name:     "choreography",
		Domain:   DomainDance,
		Elements: []string{"opening", "development", "climax", "resolution"},
		Relations: map[string][]string{
			"opening":     {"development"},
			"development": {"climax"},
			"climax":      {"resolution"},
		},
		Invariants: []string{"emotional_arc", "spatial_progression"},
	}

	// UX user journey pattern (isomorphic to choreography!)
	ag.patternLibrary["user_journey"] = Pattern{
		Name:     "user_journey",
		Domain:   DomainUXDesign,
		Elements: []string{"entry_point", "exploration", "conversion", "completion"},
		Relations: map[string][]string{
			"entry_point": {"exploration"},
			"exploration": {"conversion"},
			"conversion":  {"completion"},
		},
		Invariants: []string{"engagement_arc", "flow_progression"},
	}
}

// ============================================================================
// PATTERN DISCOVERY (automatic pattern extraction)
// ============================================================================

// DiscoverPattern extracts a pattern from a concept graph
func (ag *AnalogyGenerator) DiscoverPattern(graph *ConceptGraph, patternName string) Pattern {
	// Extract elements (all nodes)
	elements := make([]string, 0, len(graph.Nodes))
	for id := range graph.Nodes {
		elements = append(elements, id)
	}

	// Extract relations (all edges)
	relations := make(map[string][]string)
	for source, edges := range graph.Edges {
		targets := make([]string, len(edges))
		for i, edge := range edges {
			targets[i] = edge.Target
		}
		relations[source] = targets
	}

	// Detect invariants (heuristic)
	invariants := ag.detectInvariants(graph)

	pattern := Pattern{
		Name:       patternName,
		Domain:     graph.Domain,
		Elements:   elements,
		Relations:  relations,
		Invariants: invariants,
	}

	// Add to library
	ag.patternLibrary[patternName] = pattern

	return pattern
}

// detectInvariants detects structural invariants in a graph
func (ag *AnalogyGenerator) detectInvariants(graph *ConceptGraph) []string {
	invariants := make([]string, 0)

	// Check for cycles
	if ag.hasCycles(graph) {
		invariants = append(invariants, "contains_cycles")
	} else {
		invariants = append(invariants, "acyclic")
	}

	// Check for tree structure
	if ag.isTree(graph) {
		invariants = append(invariants, "tree_structure")
	}

	// Check for connectivity
	if ag.isConnected(graph) {
		invariants = append(invariants, "fully_connected")
	}

	return invariants
}

// hasCycles checks if graph contains cycles (simplified DFS)
func (ag *AnalogyGenerator) hasCycles(graph *ConceptGraph) bool {
	// Simplified check: if any node has back-edge to visited node
	visited := make(map[string]bool)

	for node := range graph.Nodes {
		if ag.dfsHasCycle(graph, node, visited, make(map[string]bool)) {
			return true
		}
	}

	return false
}

// dfsHasCycle performs DFS cycle detection
func (ag *AnalogyGenerator) dfsHasCycle(graph *ConceptGraph, node string, visited, recStack map[string]bool) bool {
	if recStack[node] {
		return true // Back edge found
	}
	if visited[node] {
		return false
	}

	visited[node] = true
	recStack[node] = true

	for _, edge := range graph.Edges[node] {
		if ag.dfsHasCycle(graph, edge.Target, visited, recStack) {
			return true
		}
	}

	recStack[node] = false
	return false
}

// isTree checks if graph is a tree
func (ag *AnalogyGenerator) isTree(graph *ConceptGraph) bool {
	// Tree = connected + acyclic + (V-1) edges
	nodeCount := len(graph.Nodes)
	edgeCount := 0
	for _, edges := range graph.Edges {
		edgeCount += len(edges)
	}

	return !ag.hasCycles(graph) && ag.isConnected(graph) && edgeCount == nodeCount-1
}

// isConnected checks if graph is fully connected
func (ag *AnalogyGenerator) isConnected(graph *ConceptGraph) bool {
	if len(graph.Nodes) == 0 {
		return true
	}

	// BFS from first node
	visited := make(map[string]bool)
	queue := make([]string, 0)

	// Start from arbitrary node
	for node := range graph.Nodes {
		queue = append(queue, node)
		visited[node] = true
		break
	}

	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		for _, edge := range graph.Edges[current] {
			if !visited[edge.Target] {
				visited[edge.Target] = true
				queue = append(queue, edge.Target)
			}
		}
	}

	return len(visited) == len(graph.Nodes)
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
