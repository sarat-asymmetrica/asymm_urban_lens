// Package knowledge - Knowledge Graph for Asya (Neo4j backend)
// Maps scientific domains, proofs, concepts, and relationships
package knowledge

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Graph represents the knowledge graph interface
type Graph interface {
	// Concepts
	AddConcept(ctx context.Context, concept *Concept) error
	GetConcept(ctx context.Context, id string) (*Concept, error)
	SearchConcepts(ctx context.Context, query string) ([]*Concept, error)

	// Relationships
	AddRelationship(ctx context.Context, rel *Relationship) error
	GetRelated(ctx context.Context, conceptID string, relType RelationType) ([]*Concept, error)

	// Proofs
	AddProof(ctx context.Context, proof *Proof) error
	GetProof(ctx context.Context, id string) (*Proof, error)
	LinkProofToConcept(ctx context.Context, proofID, conceptID string) error

	// Domains
	GetDomain(ctx context.Context, name string) (*Domain, error)
	ListDomains(ctx context.Context) ([]*Domain, error)

	// User journey
	RecordInteraction(ctx context.Context, userID, conceptID string, interactionType string) error
	GetUserJourney(ctx context.Context, userID string) (*UserJourney, error)
}

// Concept represents a scientific concept node
type Concept struct {
	ID          string                 `json:"id"`
	Name        string                 `json:"name"`
	Domain      string                 `json:"domain"`        // e.g., "Mathematics", "Physics"
	Description string                 `json:"description"`
	Tags        []string               `json:"tags"`
	Difficulty  int                    `json:"difficulty"`    // 1-10 scale
	Prerequisites []string             `json:"prerequisites"` // IDs of prerequisite concepts
	Metadata    map[string]interface{} `json:"metadata"`
	CreatedAt   time.Time              `json:"created_at"`
	UpdatedAt   time.Time              `json:"updated_at"`
}

// Relationship represents a connection between concepts
type Relationship struct {
	ID        string       `json:"id"`
	SourceID  string       `json:"source_id"`
	TargetID  string       `json:"target_id"`
	Type      RelationType `json:"type"`
	Strength  float64      `json:"strength"`  // 0.0-1.0
	Metadata  map[string]interface{} `json:"metadata"`
	CreatedAt time.Time    `json:"created_at"`
}

// RelationType defines types of concept relationships
type RelationType string

const (
	RelPrerequisite RelationType = "PREREQUISITE"
	RelRelated      RelationType = "RELATED"
	RelGeneralizes  RelationType = "GENERALIZES"
	RelSpecializes  RelationType = "SPECIALIZES"
	RelProves       RelationType = "PROVES"
	RelRefutes      RelationType = "REFUTES"
	RelApplies      RelationType = "APPLIES_TO"
)

// Proof represents a mathematical proof
type Proof struct {
	ID          string    `json:"id"`
	Title       string    `json:"title"`
	Statement   string    `json:"statement"`
	LeanCode    string    `json:"lean_code"`     // Lean 4 formalization
	Verified    bool      `json:"verified"`      // Lean verification status
	Difficulty  int       `json:"difficulty"`    // 1-10
	Tags        []string  `json:"tags"`
	RelatedProofs []string `json:"related_proofs"` // IDs
	CreatedAt   time.Time `json:"created_at"`
	UpdatedAt   time.Time `json:"updated_at"`
}

// Domain represents a scientific domain
type Domain struct {
	Name        string   `json:"name"`
	Description string   `json:"description"`
	SubDomains  []string `json:"sub_domains"`
	KeyConcepts []string `json:"key_concepts"` // Concept IDs
}

// UserJourney tracks a user's learning path
type UserJourney struct {
	UserID         string                  `json:"user_id"`
	ConceptsVisited []ConceptVisit         `json:"concepts_visited"`
	ProofsCompleted []string               `json:"proofs_completed"`
	CurrentLevel    map[string]int         `json:"current_level"` // domain -> level
	Interests       map[string]float64     `json:"interests"`     // domain -> interest score
}

// ConceptVisit records a user's interaction with a concept
type ConceptVisit struct {
	ConceptID     string    `json:"concept_id"`
	VisitedAt     time.Time `json:"visited_at"`
	TimeSpent     int       `json:"time_spent"` // seconds
	Understood    bool      `json:"understood"`
	QuestionsAsked []string `json:"questions_asked"`
}

// ═══════════════════════════════════════════════════════════════════════════
// IN-MEMORY IMPLEMENTATION (for local dev, replace with Neo4j for production)
// ═══════════════════════════════════════════════════════════════════════════

// MemoryGraph is an in-memory implementation for development
type MemoryGraph struct {
	concepts      map[string]*Concept
	proofs        map[string]*Proof
	relationships map[string]*Relationship
	domains       map[string]*Domain
	journeys      map[string]*UserJourney
}

// NewMemoryGraph creates an in-memory knowledge graph
func NewMemoryGraph() *MemoryGraph {
	g := &MemoryGraph{
		concepts:      make(map[string]*Concept),
		proofs:        make(map[string]*Proof),
		relationships: make(map[string]*Relationship),
		domains:       make(map[string]*Domain),
		journeys:      make(map[string]*UserJourney),
	}
	g.seedDefaultDomains()
	return g
}

func (g *MemoryGraph) seedDefaultDomains() {
	domains := []*Domain{
		{
			Name:        "Mathematics",
			Description: "The study of numbers, quantities, shapes, and patterns",
			SubDomains:  []string{"Algebra", "Geometry", "Topology", "Number Theory"},
		},
		{
			Name:        "Physics",
			Description: "The study of matter, energy, and the fundamental forces of nature",
			SubDomains:  []string{"Mechanics", "Thermodynamics", "Quantum Mechanics", "Relativity"},
		},
		{
			Name:        "Computer Science",
			Description: "The study of computation, algorithms, and information processing",
			SubDomains:  []string{"Algorithms", "Complexity Theory", "Type Theory", "Formal Verification"},
		},
	}

	for _, d := range domains {
		g.domains[d.Name] = d
	}
}

func (g *MemoryGraph) AddConcept(ctx context.Context, concept *Concept) error {
	if concept.ID == "" {
		concept.ID = fmt.Sprintf("concept_%d", time.Now().UnixNano())
	}
	concept.CreatedAt = time.Now()
	concept.UpdatedAt = time.Now()
	g.concepts[concept.ID] = concept
	return nil
}

func (g *MemoryGraph) GetConcept(ctx context.Context, id string) (*Concept, error) {
	c, ok := g.concepts[id]
	if !ok {
		return nil, fmt.Errorf("concept not found: %s", id)
	}
	return c, nil
}

func (g *MemoryGraph) SearchConcepts(ctx context.Context, query string) ([]*Concept, error) {
	var results []*Concept
	query = strings.ToLower(query)

	for _, c := range g.concepts {
		if strings.Contains(strings.ToLower(c.Name), query) ||
		   strings.Contains(strings.ToLower(c.Description), query) {
			results = append(results, c)
		}
	}

	return results, nil
}

func (g *MemoryGraph) AddRelationship(ctx context.Context, rel *Relationship) error {
	if rel.ID == "" {
		rel.ID = fmt.Sprintf("rel_%d", time.Now().UnixNano())
	}
	rel.CreatedAt = time.Now()
	g.relationships[rel.ID] = rel
	return nil
}

func (g *MemoryGraph) GetRelated(ctx context.Context, conceptID string, relType RelationType) ([]*Concept, error) {
	var related []*Concept

	for _, rel := range g.relationships {
		if rel.SourceID == conceptID && (relType == "" || rel.Type == relType) {
			if c, ok := g.concepts[rel.TargetID]; ok {
				related = append(related, c)
			}
		}
	}

	return related, nil
}

func (g *MemoryGraph) AddProof(ctx context.Context, proof *Proof) error {
	if proof.ID == "" {
		proof.ID = fmt.Sprintf("proof_%d", time.Now().UnixNano())
	}
	proof.CreatedAt = time.Now()
	proof.UpdatedAt = time.Now()
	g.proofs[proof.ID] = proof
	return nil
}

func (g *MemoryGraph) GetProof(ctx context.Context, id string) (*Proof, error) {
	p, ok := g.proofs[id]
	if !ok {
		return nil, fmt.Errorf("proof not found: %s", id)
	}
	return p, nil
}

func (g *MemoryGraph) LinkProofToConcept(ctx context.Context, proofID, conceptID string) error {
	return g.AddRelationship(ctx, &Relationship{
		SourceID: proofID,
		TargetID: conceptID,
		Type:     RelProves,
		Strength: 1.0,
	})
}

func (g *MemoryGraph) GetDomain(ctx context.Context, name string) (*Domain, error) {
	d, ok := g.domains[name]
	if !ok {
		return nil, fmt.Errorf("domain not found: %s", name)
	}
	return d, nil
}

func (g *MemoryGraph) ListDomains(ctx context.Context) ([]*Domain, error) {
	var domains []*Domain
	for _, d := range g.domains {
		domains = append(domains, d)
	}
	return domains, nil
}

func (g *MemoryGraph) RecordInteraction(ctx context.Context, userID, conceptID string, interactionType string) error {
	journey, ok := g.journeys[userID]
	if !ok {
		journey = &UserJourney{
			UserID:         userID,
			ConceptsVisited: []ConceptVisit{},
			ProofsCompleted: []string{},
			CurrentLevel:    make(map[string]int),
			Interests:       make(map[string]float64),
		}
		g.journeys[userID] = journey
	}

	visit := ConceptVisit{
		ConceptID:  conceptID,
		VisitedAt:  time.Now(),
		TimeSpent:  0,
		Understood: false,
	}
	journey.ConceptsVisited = append(journey.ConceptsVisited, visit)

	return nil
}

func (g *MemoryGraph) GetUserJourney(ctx context.Context, userID string) (*UserJourney, error) {
	journey, ok := g.journeys[userID]
	if !ok {
		return nil, fmt.Errorf("no journey found for user: %s", userID)
	}
	return journey, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

func (c *Concept) ToJSON() (string, error) {
	bytes, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return "", err
	}
	return string(bytes), nil
}

func (p *Proof) ToJSON() (string, error) {
	bytes, err := json.MarshalIndent(p, "", "  ")
	if err != nil {
		return "", err
	}
	return string(bytes), nil
}
