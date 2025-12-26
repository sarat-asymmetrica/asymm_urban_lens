package isomorphism

// ============================================================================
// ISOMORPHISM ENGINE - UNIFIED FACADE
// ============================================================================

// IsomorphismEngine provides a unified interface to all isomorphism operations
// Combines: Bridge Walker, Structure Mapper, Translation Engine, Analogy Generator
//
// Usage:
//   engine := NewIsomorphismEngine()
//   bridge, _ := engine.FindBridge(sourceConcept, targetConcept)
//   analogy, _ := engine.GenerateAnalogy(pattern, targetDomain)
type IsomorphismEngine struct {
	encoder         *ConceptEncoder     // Quaternion encoder
	structureMapper *StructureMapper    // Graph isomorphism
	translator      *TranslationEngine  // Domain translation
	bridgeWalker    *BridgeWalker       // Geodesic navigation
	analogyGen      *AnalogyGenerator   // Analogy discovery
}

// NewIsomorphismEngine creates a new isomorphism engine with all components
func NewIsomorphismEngine() *IsomorphismEngine {
	// Create components
	encoder := NewConceptEncoder()
	mapper := NewStructureMapper()
	translator := NewTranslationEngine(encoder, mapper)
	walker := NewBridgeWalker(encoder, translator)
	analogyGen := NewAnalogyGenerator(translator, mapper)

	return &IsomorphismEngine{
		encoder:         encoder,
		structureMapper: mapper,
		translator:      translator,
		bridgeWalker:    walker,
		analogyGen:      analogyGen,
	}
}

// ============================================================================
// BRIDGE OPERATIONS
// ============================================================================

// FindBridge finds the shortest semantic path between two concepts
func (ie *IsomorphismEngine) FindBridge(source, target Concept) (*Bridge, error) {
	return ie.bridgeWalker.Walk(source, target)
}

// BuildBridges builds multiple bridges efficiently (Williams batching)
func (ie *IsomorphismEngine) BuildBridges(sources, targets []Concept) ([]*Bridge, error) {
	return ie.bridgeWalker.BuildBridges(sources, targets)
}

// FilterBridges filters bridges by strength threshold
func (ie *IsomorphismEngine) FilterBridges(bridges []*Bridge, minStrength float64) []*Bridge {
	return ie.bridgeWalker.FilterByStrength(bridges, minStrength)
}

// ============================================================================
// TRANSLATION OPERATIONS
// ============================================================================

// TranslateConcept translates a concept from source to target domain
func (ie *IsomorphismEngine) TranslateConcept(conceptName string, sourceDomain, targetDomain Domain) ([]string, float64, error) {
	return ie.translator.TranslateConcept(conceptName, sourceDomain, targetDomain)
}

// TranslateMultipleConcepts translates multiple concepts efficiently
func (ie *IsomorphismEngine) TranslateMultipleConcepts(concepts []string, sourceDomain, targetDomain Domain) (map[string][]string, error) {
	return ie.translator.TranslateMultipleConcepts(concepts, sourceDomain, targetDomain)
}

// AddConcept adds a concept to a domain's knowledge graph
func (ie *IsomorphismEngine) AddConcept(domain Domain, concept *Concept) error {
	return ie.translator.AddConceptToGraph(domain, concept)
}

// AddRelation adds a relationship between concepts in a domain
func (ie *IsomorphismEngine) AddRelation(domain Domain, source, target, relation string, weight float64) error {
	return ie.translator.AddRelationToGraph(domain, source, target, relation, weight)
}

// ============================================================================
// STRUCTURE MAPPING OPERATIONS
// ============================================================================

// FindIsomorphism detects graph isomorphism between two concept graphs
func (ie *IsomorphismEngine) FindIsomorphism(g1, g2 *ConceptGraph) (*IsomorphismGraph, error) {
	return ie.structureMapper.FindIsomorphism(g1, g2)
}

// ============================================================================
// ANALOGY OPERATIONS
// ============================================================================

// GenerateAnalogy creates an analogy between patterns
func (ie *IsomorphismEngine) GenerateAnalogy(sourcePattern Pattern, targetDomain Domain) (*Analogy, error) {
	return ie.analogyGen.GenerateAnalogy(sourcePattern, targetDomain)
}

// GenerateMultipleAnalogies creates analogies for multiple domains
func (ie *IsomorphismEngine) GenerateMultipleAnalogies(sourcePattern Pattern, targetDomains []Domain) ([]*Analogy, error) {
	return ie.analogyGen.GenerateMultipleAnalogies(sourcePattern, targetDomains)
}

// DiscoverPattern extracts a pattern from a concept graph
func (ie *IsomorphismEngine) DiscoverPattern(graph *ConceptGraph, patternName string) Pattern {
	return ie.analogyGen.DiscoverPattern(graph, patternName)
}

// ============================================================================
// CONCEPT ENCODING
// ============================================================================

// EncodeConcept encodes a concept as a quaternion
func (ie *IsomorphismEngine) EncodeConcept(concept *Concept) {
	ie.encoder.Encode(concept)
}

// EncodeBatch encodes multiple concepts efficiently
func (ie *IsomorphismEngine) EncodeBatch(concepts []*Concept) {
	ie.encoder.EncodeBatch(concepts)
}

// ============================================================================
// CONVENIENCE METHODS
// ============================================================================

// CreateConcept creates a new concept with quaternion encoding
func (ie *IsomorphismEngine) CreateConcept(name, description string, domain Domain, tags []string) *Concept {
	concept := &Concept{
		Name:        name,
		Domain:      domain,
		Description: description,
		Tags:        tags,
		Properties:  make(map[string]float64),
	}

	// Encode immediately
	ie.encoder.Encode(concept)

	return concept
}

// FindSimilarConcepts finds concepts similar to a given concept
func (ie *IsomorphismEngine) FindSimilarConcepts(concept *Concept, domain Domain, topN int) ([]*Concept, error) {
	// Get domain graph
	graph, err := ie.translator.getOrCreateGraph(domain)
	if err != nil {
		return nil, err
	}

	type match struct {
		concept    *Concept
		similarity float64
	}

	matches := make([]match, 0)

	// Compute similarity to all concepts in domain
	for _, candidate := range graph.Nodes {
		sim := concept.Quaternion.Dot(candidate.Quaternion)
		matches = append(matches, match{concept: candidate, similarity: sim})
	}

	// Sort by similarity
	for i := 0; i < len(matches)-1; i++ {
		for j := 0; j < len(matches)-i-1; j++ {
			if matches[j].similarity < matches[j+1].similarity {
				matches[j], matches[j+1] = matches[j+1], matches[j]
			}
		}
	}

	// Return top N
	n := topN
	if n > len(matches) {
		n = len(matches)
	}

	results := make([]*Concept, n)
	for i := 0; i < n; i++ {
		results[i] = matches[i].concept
	}

	return results, nil
}

// ============================================================================
// SKILL TRANSLATION (Urban Lens Use Case!)
// ============================================================================

// TranslateSkills translates professional skills to technical roles
// Example: Waste collector's route optimization → Operations manager's process optimization
func (ie *IsomorphismEngine) TranslateSkills(skills []string, currentDomain, targetDomain Domain) (map[string][]string, error) {
	return ie.translator.TranslateMultipleConcepts(skills, currentDomain, targetDomain)
}

// SuggestCareerTransition suggests career transitions based on skill overlap
func (ie *IsomorphismEngine) SuggestCareerTransition(currentRole string, currentDomain Domain, targetDomains []Domain) ([]RoleMatch, error) {
	matches := make([]RoleMatch, 0)

	for _, targetDomain := range targetDomains {
		// Build translation map
		mapKey := string(currentDomain) + "→" + string(targetDomain)

		// Get or create translation map
		_, exists := ie.translator.translationMaps[mapKey]
		if !exists {
			// Build dynamically
			_, err := ie.translator.buildTranslationMap(currentDomain, targetDomain)
			if err != nil {
				continue // Skip if can't build map
			}
		}

		// Create role match
		match := RoleMatch{
			RoleName:            string(targetDomain) + "_specialist",
			Domain:              targetDomain,
			Confidence:          0.75, // Placeholder
			MatchedIntelligences: []IntelligenceType{}, // Would compute from profile
			SkillGaps:           []string{},
			RequiredBridges:     []Bridge{},
		}

		matches = append(matches, match)
	}

	return matches, nil
}

// ============================================================================
// URBAN LENS SPECIFIC METHODS
// ============================================================================

// TranslateWasteCollectorSkills translates waste collector skills to operations
func (ie *IsomorphismEngine) TranslateWasteCollectorSkills(skills []string) (map[string][]string, error) {
	return ie.TranslateSkills(skills, DomainWasteManagement, DomainOperations)
}

// TranslateStreetVendorSkills translates street vendor skills to sales
func (ie *IsomorphismEngine) TranslateStreetVendorSkills(skills []string) (map[string][]string, error) {
	return ie.TranslateSkills(skills, DomainStreetVending, DomainSales)
}

// TranslateTrafficFlowToArchitecture translates traffic flow concepts to system architecture
func (ie *IsomorphismEngine) TranslateTrafficFlowToArchitecture(concepts []string) (map[string][]string, error) {
	return ie.TranslateSkills(concepts, DomainTrafficFlow, DomainSystemArchitecture)
}

// ============================================================================
// QUALITY METRICS (5 Timbres)
// ============================================================================

// EvaluateBridgeQuality computes 5 Timbres quality for a bridge
func (ie *IsomorphismEngine) EvaluateBridgeQuality(bridge *Bridge) float64 {
	// 1. Correctness: Strength of bridge (0-1)
	correctness := bridge.Strength
	if correctness < 0.01 {
		correctness = 0.01 // Avoid division by zero
	}

	// 2. Performance: Based on isomorphism type weight (scaled up)
	performance := bridge.IsomorphismType.Weight() * 2.0 // Scale to reasonable range
	if performance > 1.0 {
		performance = 1.0
	}
	if performance < 0.01 {
		performance = 0.01
	}

	// 3. Reliability: Evidence count (more evidence = higher reliability)
	reliability := float64(len(bridge.Evidence)) / 3.0 // Normalize to [0, 1] (expect 3-5 evidence)
	if reliability > 1.0 {
		reliability = 1.0
	}
	if reliability < 0.01 {
		reliability = 0.01
	}

	// 4. Synergy: Cross-domain (higher) vs same-domain (lower)
	synergy := 0.5
	if bridge.SourceConcept.Domain != bridge.TargetConcept.Domain {
		synergy = 0.9 // Cross-domain is more valuable
	}

	// 5. Elegance: Path length (shorter = more elegant)
	elegance := 1.0 - (float64(len(bridge.Geodesic)) / 50.0) // Normalize (expect ~10 waypoints)
	if elegance < 0.2 {
		elegance = 0.2 // Minimum elegance
	}
	if elegance > 1.0 {
		elegance = 1.0
	}

	// Harmonic mean (balanced scoring)
	harmonicMean := 5.0 / (
		1.0/correctness +
			1.0/performance +
			1.0/reliability +
			1.0/synergy +
			1.0/elegance)

	return harmonicMean
}
