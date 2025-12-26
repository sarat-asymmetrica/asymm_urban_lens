// Package isomorphism implements cross-domain concept translation via structural mapping
//
// Mathematical Foundation: Category Theory - Functors between categories preserve structure
// Application: Bridge Walker traverses concept bridges between domains
//
// Core Algorithms:
//   1. Structure Mapping Engine - Graph isomorphism via VF2 algorithm
//   2. Bridge Walker - SLERP-based geodesic traversal on S³
//   3. Analogy Generator - Pattern matching with quaternion similarity
//   4. Domain Translation - Concept mapping with confidence scoring
//
// Ported from: Ananta Backend (Isomorphism Engine Design Doc)
// Enhanced with: Quaternion encoding, GPU acceleration, Williams batching
//
// See: C:\Projects\asymm_ananta\backend\ISOMORPHISM_ENGINE.md
package isomorphism

import (
	"github.com/asymmetrica/urbanlens/pkg/math"
)

// ============================================================================
// CORE DOMAIN TYPES
// ============================================================================

// Domain represents a conceptual domain (field of knowledge/practice)
type Domain string

const (
	// Technical Domains
	DomainProgramming      Domain = "programming"
	DomainSystemArchitecture Domain = "system_architecture"
	DomainUXDesign         Domain = "ux_design"
	DomainQA               Domain = "quality_assurance"
	DomainOperations       Domain = "operations"
	DomainProductManagement Domain = "product_management"
	DomainDataScience      Domain = "data_science"
	DomainSales            Domain = "sales"
	DomainHR               Domain = "human_resources"

	// Professional Domains
	DomainDriving          Domain = "driving"
	DomainCooking          Domain = "cooking"
	DomainDance            Domain = "dance"
	DomainMusic            Domain = "music"
	DomainSecurity         Domain = "security"
	DomainCleaning         Domain = "cleaning"
	DomainRetail           Domain = "retail"
	DomainTeaching         Domain = "teaching"
	DomainCarpentry        Domain = "carpentry"

	// Urban Domains (NEW - Urban Lens specific!)
	DomainUrbanPlanning    Domain = "urban_planning"
	DomainTrafficFlow      Domain = "traffic_flow"
	DomainPublicTransit    Domain = "public_transit"
	DomainWasteManagement  Domain = "waste_management"
	DomainCommunityOrganizing Domain = "community_organizing"
	DomainStreetVending    Domain = "street_vending"
	DomainCivicEngagement  Domain = "civic_engagement"
)

// Concept represents an abstract idea/skill/pattern in a domain
type Concept struct {
	Name        string            // Canonical name (e.g., "route_optimization")
	Domain      Domain            // Source domain
	Description string            // Human-readable description
	Tags        []string          // Classification tags
	Quaternion  math.Quaternion   // S³ encoding (semantic vector)
	Properties  map[string]float64 // Numerical properties
}

// Bridge represents a structural mapping between two concepts
type Bridge struct {
	SourceConcept Concept          // Source concept
	TargetConcept Concept          // Target concept
	Strength      float64          // Confidence (0-1)
	IsomorphismType IsomorphismType // Type of structural match
	Evidence      []string         // Supporting evidence
	Geodesic      []math.Quaternion // SLERP path (S³ geodesic)
}

// IsomorphismType categorizes the type of structural similarity
type IsomorphismType string

const (
	// Five types from Gardner's research (ISOMORPHISM_ENGINE.md)
	IsomorphismStructural  IsomorphismType = "structural"  // Same hierarchy/organization (weight: 0.30)
	IsomorphismFunctional  IsomorphismType = "functional"  // Same purpose/outcome (weight: 0.25)
	IsomorphismRelational  IsomorphismType = "relational"  // Same relationships (weight: 0.20)
	IsomorphismProcessual  IsomorphismType = "processual"  // Same workflow/sequence (weight: 0.15)
	IsomorphismPatternBased IsomorphismType = "pattern"    // Same recurring patterns (weight: 0.10)
)

// TypeWeight returns the confidence weight for each isomorphism type
func (it IsomorphismType) Weight() float64 {
	weights := map[IsomorphismType]float64{
		IsomorphismStructural:  0.30,
		IsomorphismFunctional:  0.25,
		IsomorphismRelational:  0.20,
		IsomorphismProcessual:  0.15,
		IsomorphismPatternBased: 0.10,
	}
	return weights[it]
}

// ============================================================================
// GRAPH STRUCTURES (for isomorphism detection)
// ============================================================================

// ConceptGraph represents a domain as a directed graph of concepts
type ConceptGraph struct {
	Domain   Domain               // Domain this graph represents
	Nodes    map[string]*Concept  // Concept ID → Concept
	Edges    map[string][]Edge    // Source ID → Edges
	Metadata map[string]interface{} // Domain-specific metadata
}

// Edge represents a relationship between concepts
type Edge struct {
	Source     string  // Source concept ID
	Target     string  // Target concept ID
	Relation   string  // Relationship type (e.g., "requires", "produces", "similar_to")
	Weight     float64 // Relationship strength (0-1)
	Bidirectional bool // Can traverse in both directions
}

// AddNode adds a concept to the graph
func (g *ConceptGraph) AddNode(id string, concept *Concept) {
	if g.Nodes == nil {
		g.Nodes = make(map[string]*Concept)
	}
	g.Nodes[id] = concept
}

// AddEdge adds a relationship between concepts
func (g *ConceptGraph) AddEdge(source, target, relation string, weight float64, bidirectional bool) {
	if g.Edges == nil {
		g.Edges = make(map[string][]Edge)
	}

	edge := Edge{
		Source:        source,
		Target:        target,
		Relation:      relation,
		Weight:        weight,
		Bidirectional: bidirectional,
	}

	g.Edges[source] = append(g.Edges[source], edge)

	// Add reverse edge if bidirectional
	if bidirectional {
		reverseEdge := Edge{
			Source:        target,
			Target:        source,
			Relation:      relation,
			Weight:        weight,
			Bidirectional: true,
		}
		g.Edges[target] = append(g.Edges[target], reverseEdge)
	}
}

// GetNeighbors returns all concepts connected to a given concept
func (g *ConceptGraph) GetNeighbors(conceptID string) []*Concept {
	edges := g.Edges[conceptID]
	neighbors := make([]*Concept, 0, len(edges))

	for _, edge := range edges {
		if concept, exists := g.Nodes[edge.Target]; exists {
			neighbors = append(neighbors, concept)
		}
	}

	return neighbors
}

// ============================================================================
// TRANSLATION MAPPING
// ============================================================================

// TranslationMap defines concept mappings between two domains
type TranslationMap struct {
	SourceDomain Domain                      // Source domain
	TargetDomain Domain                      // Target domain
	Mappings     map[string]ConceptTranslation // Source concept → Target concepts
	Confidence   float64                     // Overall map quality (0-1)
	Graph        *IsomorphismGraph           // Structural isomorphism graph
}

// ConceptTranslation represents a single concept's translation
type ConceptTranslation struct {
	SourceConcept   string            // Source concept name
	TargetConcepts  []string          // Possible target concepts (ranked)
	Confidence      float64           // Translation confidence (0-1)
	IsomorphismType IsomorphismType   // Type of structural match
	Evidence        []string          // Supporting evidence
	Properties      map[string]float64 // Preserved properties
}

// IsomorphismGraph represents the graph-level isomorphism structure
type IsomorphismGraph struct {
	SourceGraph  *ConceptGraph           // Source domain graph
	TargetGraph  *ConceptGraph           // Target domain graph
	NodeMapping  map[string]string       // Source node → Target node
	EdgeMapping  map[string]string       // Source edge → Target edge
	Homomorphism bool                    // Is it structure-preserving?
	Similarity   float64                 // Graph similarity score (0-1)
}

// ============================================================================
// INTELLIGENCE TYPES (Gardner's Multiple Intelligences)
// ============================================================================

// IntelligenceType represents one of Gardner's 9 intelligence types
type IntelligenceType string

const (
	IntelligenceLogicalMath      IntelligenceType = "logical_mathematical"
	IntelligenceLinguistic       IntelligenceType = "linguistic"
	IntelligenceSpatial          IntelligenceType = "spatial"
	IntelligenceBodyKinesthetic  IntelligenceType = "body_kinesthetic"
	IntelligenceMusical          IntelligenceType = "musical"
	IntelligenceInterpersonal    IntelligenceType = "interpersonal"
	IntelligenceIntrapersonal    IntelligenceType = "intrapersonal"
	IntelligenceNaturalist       IntelligenceType = "naturalist"
	IntelligenceExistential      IntelligenceType = "existential"
)

// IntelligenceScore represents a measured intelligence score
type IntelligenceScore struct {
	Type  IntelligenceType `json:"type"`
	Score float64          `json:"score"` // 0-1
}

// IntelligenceProfile represents a person's intelligence profile
type IntelligenceProfile struct {
	Scores    []IntelligenceScore  `json:"scores"`
	Dominant  []IntelligenceType   `json:"dominant"`  // Top 3 intelligences
	Quaternion math.Quaternion     `json:"quaternion"` // S³ encoding
}

// RoleMatch represents a potential role match
type RoleMatch struct {
	RoleName       string               `json:"role_name"`
	Domain         Domain               `json:"domain"`
	Confidence     float64              `json:"confidence"`
	MatchedIntelligences []IntelligenceType `json:"matched_intelligences"`
	SkillGaps      []string             `json:"skill_gaps"`
	RequiredBridges []Bridge             `json:"required_bridges"`
}

// ============================================================================
// ANALOGY TYPES
// ============================================================================

// Analogy represents a structural similarity between two concept patterns
type Analogy struct {
	SourcePattern  Pattern         // Pattern in source domain
	TargetPattern  Pattern         // Pattern in target domain
	Mapping        map[string]string // Element mapping (source → target)
	Confidence     float64         // Analogy strength (0-1)
	Type           IsomorphismType // Type of structural match
	Explanation    string          // Human-readable explanation
}

// Pattern represents a structured pattern of concepts
type Pattern struct {
	Name      string              // Pattern name
	Domain    Domain              // Domain this pattern belongs to
	Elements  []string            // Concept IDs in pattern
	Relations map[string][]string // Relationships (concept → related concepts)
	Invariants []string           // Structural invariants (properties that must hold)
}
