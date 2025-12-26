// Package knowledge - Cross-domain connections and learning path discovery
package knowledge

import (
	"context"
	"fmt"
	"math"
	"strings"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// CONNECTION TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Connection represents a bridge between domains or concepts
type Connection struct {
	ID          string                 `json:"id"`
	FromID      string                 `json:"from_id"`     // Source concept/domain
	ToID        string                 `json:"to_id"`       // Target concept/domain
	BridgeType  BridgeType             `json:"bridge_type"` // Type of connection
	Strength    float64                `json:"strength"`    // 0.0-1.0 connection strength
	Description string                 `json:"description"` // Human-readable explanation
	Examples    []string               `json:"examples"`    // Concrete examples
	Difficulty  int                    `json:"difficulty"`  // 1-10 difficulty to understand
	Metadata    map[string]interface{} `json:"metadata"`
}

// BridgeType categorizes types of cross-domain connections
type BridgeType string

const (
	BridgeAnalogy       BridgeType = "ANALOGY"        // Similar patterns
	BridgeApplication   BridgeType = "APPLICATION"    // Direct application
	BridgeMathematical  BridgeType = "MATHEMATICAL"   // Mathematical relationship
	BridgeEvolutionary  BridgeType = "EVOLUTIONARY"   // Historical development
	BridgeMetaphorical  BridgeType = "METAPHORICAL"   // Teaching metaphor
)

// PathNode represents a step in a learning path
type PathNode struct {
	ConceptID   string   `json:"concept_id"`
	Depth       int      `json:"depth"`         // Distance from start
	Difficulty  int      `json:"difficulty"`    // 1-10
	Prerequisites []string `json:"prerequisites"` // Concepts needed before this
	Description string   `json:"description"`
	Estimated   int      `json:"estimated_time"` // Estimated learning time (minutes)
}

// LearningPath represents a structured journey from anchor to target
type LearningPath struct {
	ID          string      `json:"id"`
	FromID      string      `json:"from_id"`   // Starting concept
	ToID        string      `json:"to_id"`     // Target concept
	Nodes       []PathNode  `json:"nodes"`     // Ordered path
	TotalTime   int         `json:"total_time"` // Total estimated time (minutes)
	Difficulty  int         `json:"difficulty"` // Overall difficulty 1-10
	Description string      `json:"description"`
}

// Suggestion represents an exploration suggestion for a user
type Suggestion struct {
	ConceptID   string   `json:"concept_id"`
	Reason      string   `json:"reason"`      // Why this is suggested
	Relevance   float64  `json:"relevance"`   // 0.0-1.0 relevance score
	Difficulty  int      `json:"difficulty"`  // 1-10
	Prerequisites []string `json:"prerequisites"` // What to learn first
}

// UserProfile represents a user's learning preferences and history
type UserProfile struct {
	UserID          string         `json:"user_id"`
	Interests       []string       `json:"interests"`        // Domain/tag interests
	SkillLevel      map[string]int `json:"skill_level"`      // domain -> level (1-10)
	PreferredPace   string         `json:"preferred_pace"`   // "slow", "medium", "fast"
	LearningStyle   string         `json:"learning_style"`   // "visual", "analytical", etc.
	TimeAvailable   int            `json:"time_available"`   // Minutes per session
}

// ═══════════════════════════════════════════════════════════════════════════
// CONNECTION INTERFACE EXTENSION
// ═══════════════════════════════════════════════════════════════════════════

// ConnectionGraph extends Graph with cross-domain connection capabilities
type ConnectionGraph interface {
	DiscoveryGraph

	// Bridges between concepts/domains
	AddBridge(ctx context.Context, conn *Connection) error
	GetBridge(ctx context.Context, id string) (*Connection, error)
	FindBridges(ctx context.Context, domain1, domain2 string) ([]Connection, error)

	// Learning path discovery
	BuildLearningPath(ctx context.Context, fromConceptID, toConceptID string) (*LearningPath, error)
	GetShortestPath(ctx context.Context, fromID, toID string) ([]PathNode, error)

	// Exploration suggestions
	SuggestExplorations(ctx context.Context, currentConceptID string, profile UserProfile) ([]Suggestion, error)
	GetRelatedByInterest(ctx context.Context, userID string, limit int) ([]*Concept, error)

	// Analytics
	GetStrongestBridges(ctx context.Context, limit int) ([]Connection, error)
	GetDomainConnectivity(ctx context.Context, domain string) (map[string]float64, error)
}

// ═══════════════════════════════════════════════════════════════════════════
// MEMORY IMPLEMENTATION - CONNECTIONS
// ═══════════════════════════════════════════════════════════════════════════

// MemoryConnectionGraph extends MemoryDiscoveryGraph with connections
type MemoryConnectionGraph struct {
	*MemoryDiscoveryGraph
	connections map[string]*Connection
	mu          sync.RWMutex
}

// NewMemoryConnectionGraph creates an in-memory connection graph
func NewMemoryConnectionGraph() *MemoryConnectionGraph {
	return &MemoryConnectionGraph{
		MemoryDiscoveryGraph: NewMemoryDiscoveryGraph(),
		connections:          make(map[string]*Connection),
	}
}

// AddBridge adds a connection between concepts/domains
func (g *MemoryConnectionGraph) AddBridge(ctx context.Context, conn *Connection) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	if conn.ID == "" {
		conn.ID = fmt.Sprintf("bridge_%d", time.Now().UnixNano())
	}

	g.connections[conn.ID] = conn

	return nil
}

// GetBridge retrieves a connection by ID
func (g *MemoryConnectionGraph) GetBridge(ctx context.Context, id string) (*Connection, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	conn, ok := g.connections[id]
	if !ok {
		return nil, fmt.Errorf("bridge not found: %s", id)
	}

	return conn, nil
}

// FindBridges finds connections between two domains
func (g *MemoryConnectionGraph) FindBridges(ctx context.Context, domain1, domain2 string) ([]Connection, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var results []Connection

	// Get all concepts in domain1 and domain2
	domain1Concepts := g.getConceptsByDomain(domain1)
	domain2Concepts := g.getConceptsByDomain(domain2)

	// Find connections between concepts in these domains
	for _, conn := range g.connections {
		from := conn.FromID
		to := conn.ToID

		// Check if connection bridges the two domains
		fromInD1 := contains(domain1Concepts, from)
		toInD2 := contains(domain2Concepts, to)
		fromInD2 := contains(domain2Concepts, from)
		toInD1 := contains(domain1Concepts, to)

		if (fromInD1 && toInD2) || (fromInD2 && toInD1) {
			results = append(results, *conn)
		}
	}

	return results, nil
}

// BuildLearningPath constructs a path from one concept to another
func (g *MemoryConnectionGraph) BuildLearningPath(ctx context.Context, fromConceptID, toConceptID string) (*LearningPath, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	// Use breadth-first search to find shortest path
	nodes, err := g.bfs(fromConceptID, toConceptID)
	if err != nil {
		return nil, err
	}

	// Build path with metadata
	path := &LearningPath{
		ID:     fmt.Sprintf("path_%d", time.Now().UnixNano()),
		FromID: fromConceptID,
		ToID:   toConceptID,
		Nodes:  nodes,
	}

	// Calculate total time and difficulty
	totalTime := 0
	maxDifficulty := 0

	for _, node := range nodes {
		totalTime += node.Estimated
		if node.Difficulty > maxDifficulty {
			maxDifficulty = node.Difficulty
		}
	}

	path.TotalTime = totalTime
	path.Difficulty = maxDifficulty

	fromConcept, _ := g.MemoryGraph.GetConcept(ctx, fromConceptID)
	toConcept, _ := g.MemoryGraph.GetConcept(ctx, toConceptID)

	if fromConcept != nil && toConcept != nil {
		path.Description = fmt.Sprintf("Learning path from %s to %s", fromConcept.Name, toConcept.Name)
	}

	return path, nil
}

// GetShortestPath finds shortest path between concepts
func (g *MemoryConnectionGraph) GetShortestPath(ctx context.Context, fromID, toID string) ([]PathNode, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	return g.bfs(fromID, toID)
}

// SuggestExplorations suggests next concepts based on user profile
func (g *MemoryConnectionGraph) SuggestExplorations(ctx context.Context, currentConceptID string, profile UserProfile) ([]Suggestion, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var suggestions []Suggestion

	// Get current concept
	current, err := g.MemoryGraph.GetConcept(ctx, currentConceptID)
	if err != nil {
		return nil, err
	}

	// Find related concepts through relationships
	related, _ := g.MemoryGraph.GetRelated(ctx, currentConceptID, "")

	for _, concept := range related {
		// Calculate relevance based on user profile
		relevance := g.calculateRelevance(concept, profile, current)

		// Check if prerequisites are met
		prereqsMet := g.checkPrerequisites(concept.Prerequisites, profile)

		if prereqsMet {
			suggestions = append(suggestions, Suggestion{
				ConceptID:     concept.ID,
				Reason:        g.generateReason(concept, current, profile),
				Relevance:     relevance,
				Difficulty:    concept.Difficulty,
				Prerequisites: concept.Prerequisites,
			})
		}
	}

	// Sort by relevance (simple bubble sort for small n)
	for i := 0; i < len(suggestions)-1; i++ {
		for j := 0; j < len(suggestions)-i-1; j++ {
			if suggestions[j].Relevance < suggestions[j+1].Relevance {
				suggestions[j], suggestions[j+1] = suggestions[j+1], suggestions[j]
			}
		}
	}

	return suggestions, nil
}

// GetRelatedByInterest finds concepts matching user interests
func (g *MemoryConnectionGraph) GetRelatedByInterest(ctx context.Context, userID string, limit int) ([]*Concept, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	// Get user journey to determine interests
	journey, err := g.MemoryGraph.GetUserJourney(ctx, userID)
	if err != nil {
		return []*Concept{}, nil // No journey yet
	}

	// Find concepts in domains of interest
	var results []*Concept
	seen := make(map[string]bool)

	for domain := range journey.Interests {
		concepts := g.getConceptsByDomain(domain)
		for _, conceptID := range concepts {
			if !seen[conceptID] {
				concept, _ := g.MemoryGraph.GetConcept(ctx, conceptID)
				if concept != nil {
					results = append(results, concept)
					seen[conceptID] = true
				}
			}
		}
	}

	// Limit results
	if limit > 0 && limit < len(results) {
		results = results[:limit]
	}

	return results, nil
}

// GetStrongestBridges retrieves connections with highest strength
func (g *MemoryConnectionGraph) GetStrongestBridges(ctx context.Context, limit int) ([]Connection, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	// Convert to slice
	var all []Connection
	for _, conn := range g.connections {
		all = append(all, *conn)
	}

	// Sort by strength
	for i := 0; i < len(all)-1; i++ {
		for j := 0; j < len(all)-i-1; j++ {
			if all[j].Strength < all[j+1].Strength {
				all[j], all[j+1] = all[j+1], all[j]
			}
		}
	}

	// Limit results
	if limit > 0 && limit < len(all) {
		all = all[:limit]
	}

	return all, nil
}

// GetDomainConnectivity calculates how connected a domain is to others
func (g *MemoryConnectionGraph) GetDomainConnectivity(ctx context.Context, domain string) (map[string]float64, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	connectivity := make(map[string]float64)
	domainConcepts := g.getConceptsByDomain(domain)

	// For each connection, check if it links to other domains
	for _, conn := range g.connections {
		fromInDomain := contains(domainConcepts, conn.FromID)
		toInDomain := contains(domainConcepts, conn.ToID)

		if fromInDomain || toInDomain {
			// Find the other concept's domain
			var otherID string
			if fromInDomain {
				otherID = conn.ToID
			} else {
				otherID = conn.FromID
			}

			otherConcept, err := g.MemoryGraph.GetConcept(ctx, otherID)
			if err == nil && otherConcept.Domain != domain {
				connectivity[otherConcept.Domain] += conn.Strength
			}
		}
	}

	return connectivity, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// bfs performs breadth-first search to find shortest path
func (g *MemoryConnectionGraph) bfs(fromID, toID string) ([]PathNode, error) {
	if fromID == toID {
		return []PathNode{}, nil
	}

	// BFS data structures
	queue := []string{fromID}
	visited := make(map[string]bool)
	parent := make(map[string]string)
	depth := make(map[string]int)

	visited[fromID] = true
	depth[fromID] = 0

	// BFS traversal
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		if current == toID {
			// Reconstruct path
			return g.reconstructPath(fromID, toID, parent, depth)
		}

		// Explore neighbors via relationships
		for _, rel := range g.MemoryGraph.relationships {
			var next string
			if rel.SourceID == current {
				next = rel.TargetID
			} else if rel.TargetID == current {
				next = rel.SourceID
			}

			if next != "" && !visited[next] {
				visited[next] = true
				parent[next] = current
				depth[next] = depth[current] + 1
				queue = append(queue, next)
			}
		}
	}

	return nil, fmt.Errorf("no path found from %s to %s", fromID, toID)
}

// reconstructPath builds PathNode list from BFS results
func (g *MemoryConnectionGraph) reconstructPath(fromID, toID string, parent map[string]string, depth map[string]int) ([]PathNode, error) {
	var path []PathNode

	// Trace back from toID to fromID
	current := toID
	for current != fromID {
		concept, err := g.MemoryGraph.GetConcept(context.Background(), current)
		if err != nil {
			return nil, err
		}

		node := PathNode{
			ConceptID:     current,
			Depth:         depth[current],
			Difficulty:    concept.Difficulty,
			Prerequisites: concept.Prerequisites,
			Description:   concept.Description,
			Estimated:     g.estimateTime(concept.Difficulty),
		}

		path = append([]PathNode{node}, path...) // Prepend
		current = parent[current]
	}

	return path, nil
}

// getConceptsByDomain returns concept IDs in a domain
func (g *MemoryConnectionGraph) getConceptsByDomain(domain string) []string {
	var results []string

	for id, concept := range g.MemoryGraph.concepts {
		if strings.EqualFold(concept.Domain, domain) {
			results = append(results, id)
		}
	}

	return results
}

// calculateRelevance scores how relevant a concept is to user
func (g *MemoryConnectionGraph) calculateRelevance(concept *Concept, profile UserProfile, current *Concept) float64 {
	score := 0.0

	// Interest match
	for _, interest := range profile.Interests {
		if strings.EqualFold(concept.Domain, interest) {
			score += 0.5
		}
		for _, tag := range concept.Tags {
			if strings.EqualFold(tag, interest) {
				score += 0.3
			}
		}
	}

	// Difficulty match
	skillLevel := profile.SkillLevel[concept.Domain]
	difficultyGap := math.Abs(float64(concept.Difficulty - skillLevel))
	score += (10.0 - difficultyGap) / 10.0 * 0.3

	// Domain continuity (same domain as current)
	if strings.EqualFold(concept.Domain, current.Domain) {
		score += 0.2
	}

	return math.Min(score, 1.0)
}

// checkPrerequisites validates if user has met prerequisites
func (g *MemoryConnectionGraph) checkPrerequisites(prereqs []string, profile UserProfile) bool {
	// Simplified: assume met if user has skill level in domain
	// In production, would check actual concept completion
	return true
}

// generateReason creates human-readable suggestion reason
func (g *MemoryConnectionGraph) generateReason(concept, current *Concept, profile UserProfile) string {
	if strings.EqualFold(concept.Domain, current.Domain) {
		return fmt.Sprintf("Continues from %s in %s", current.Name, current.Domain)
	}

	for _, interest := range profile.Interests {
		if strings.EqualFold(concept.Domain, interest) {
			return fmt.Sprintf("Matches your interest in %s", concept.Domain)
		}
	}

	return fmt.Sprintf("Related to %s", current.Name)
}

// estimateTime estimates learning time based on difficulty
func (g *MemoryConnectionGraph) estimateTime(difficulty int) int {
	// Base: 10 minutes per difficulty level
	return difficulty * 10
}

// contains checks if slice contains string
func contains(slice []string, item string) bool {
	for _, s := range slice {
		if s == item {
			return true
		}
	}
	return false
}
