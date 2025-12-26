// Package knowledge - Discovery tracking for "Why?" chain explorations
package knowledge

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// DISCOVERY TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Discovery represents a user's "aha!" moment from observation → formalization
type Discovery struct {
	ID            string    `json:"id"`
	UserID        string    `json:"user_id"`
	Timestamp     time.Time `json:"timestamp"`

	// The journey from observation to formalization
	Anchor        string   `json:"anchor"`          // Starting observation (e.g., "Why does ice float?")
	WhyChain      []string `json:"why_chain"`       // Chain of "Why?" questions
	Insight       string   `json:"insight"`         // The "aha!" moment
	LeanTheorem   string   `json:"lean_theorem"`    // Formalized proof (optional)
	Verified      bool     `json:"verified"`        // Lean verification status

	// Context and connections
	Domains       []string `json:"domains"`         // Scientific domains touched
	Connections   []string `json:"connections"`     // Related concept/discovery IDs
	Tags          []string `json:"tags"`            // Searchable tags

	// Engagement metrics
	Celebrations  int      `json:"celebrations"`    // Times celebrated by community
	Shares        int      `json:"shares"`          // Times shared

	// Metadata
	Metadata      map[string]interface{} `json:"metadata"`
	CreatedAt     time.Time `json:"created_at"`
	UpdatedAt     time.Time `json:"updated_at"`
}

// WhyNode represents a single step in the "Why?" chain
type WhyNode struct {
	Question  string   `json:"question"`   // The "Why?" question
	Answer    string   `json:"answer"`     // The explanation
	Concepts  []string `json:"concepts"`   // Concepts introduced
	Depth     int      `json:"depth"`      // Depth in the chain
}

// Milestone represents a significant achievement in learning
type Milestone struct {
	ID          string                 `json:"id"`
	UserID      string                 `json:"user_id"`
	Type        MilestoneType          `json:"type"`
	Title       string                 `json:"title"`
	Description string                 `json:"description"`
	Achieved    time.Time              `json:"achieved"`
	Metadata    map[string]interface{} `json:"metadata"`
}

// MilestoneType categorizes learning achievements
type MilestoneType string

const (
	MilestoneFirstDiscovery    MilestoneType = "FIRST_DISCOVERY"
	MilestoneFirstProof        MilestoneType = "FIRST_PROOF"
	MilestoneCrossDomain       MilestoneType = "CROSS_DOMAIN"      // Connected multiple domains
	MilestoneDeepDive          MilestoneType = "DEEP_DIVE"         // Explored >10 levels deep
	MilestoneTeacher           MilestoneType = "TEACHER"           // Helped another learn
	MilestonePolymath          MilestoneType = "POLYMATH"          // Mastered multiple domains
)

// ═══════════════════════════════════════════════════════════════════════════
// DISCOVERY INTERFACE EXTENSION
// ═══════════════════════════════════════════════════════════════════════════

// DiscoveryGraph extends Graph with discovery tracking
type DiscoveryGraph interface {
	Graph

	// Discovery management
	RecordDiscovery(ctx context.Context, d *Discovery) error
	GetDiscovery(ctx context.Context, id string) (*Discovery, error)
	GetUserDiscoveries(ctx context.Context, userID string) ([]*Discovery, error)
	GetRelatedDiscoveries(ctx context.Context, conceptID string) ([]*Discovery, error)

	// Discovery search
	SearchDiscoveries(ctx context.Context, query string) ([]*Discovery, error)
	GetDiscoveriesByDomain(ctx context.Context, domain string) ([]*Discovery, error)
	GetDiscoveriesByTag(ctx context.Context, tag string) ([]*Discovery, error)

	// Engagement
	CelebrateDiscovery(ctx context.Context, discoveryID string) error
	ShareDiscovery(ctx context.Context, discoveryID, fromUserID, toUserID string) error

	// Analytics
	GetDiscoveryStats(ctx context.Context, userID string) (*DiscoveryStats, error)
	GetPopularDiscoveries(ctx context.Context, limit int) ([]*Discovery, error)
}

// DiscoveryStats provides analytics on user's discovery journey
type DiscoveryStats struct {
	TotalDiscoveries    int                `json:"total_discoveries"`
	ProofsVerified      int                `json:"proofs_verified"`
	DomainsExplored     []string           `json:"domains_explored"`
	AverageChainDepth   float64            `json:"average_chain_depth"`
	TotalCelebrations   int                `json:"total_celebrations"`
	CrossDomainLinks    int                `json:"cross_domain_links"`
	DomainBreakdown     map[string]int     `json:"domain_breakdown"`
	MostCelebratedID    string             `json:"most_celebrated_id"`
}

// ═══════════════════════════════════════════════════════════════════════════
// MEMORY IMPLEMENTATION - DISCOVERY
// ═══════════════════════════════════════════════════════════════════════════

// MemoryDiscoveryGraph extends MemoryGraph with discovery tracking
type MemoryDiscoveryGraph struct {
	*MemoryGraph
	discoveries map[string]*Discovery
	milestones  map[string][]*Milestone // userID -> milestones
	mu          sync.RWMutex
}

// NewMemoryDiscoveryGraph creates an in-memory discovery graph
func NewMemoryDiscoveryGraph() *MemoryDiscoveryGraph {
	return &MemoryDiscoveryGraph{
		MemoryGraph: NewMemoryGraph(),
		discoveries: make(map[string]*Discovery),
		milestones:  make(map[string][]*Milestone),
	}
}

// RecordDiscovery adds a new discovery to the graph
func (g *MemoryDiscoveryGraph) RecordDiscovery(ctx context.Context, d *Discovery) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	if d.ID == "" {
		d.ID = fmt.Sprintf("discovery_%d", time.Now().UnixNano())
	}

	now := time.Now()
	d.CreatedAt = now
	d.UpdatedAt = now

	if d.Timestamp.IsZero() {
		d.Timestamp = now
	}

	g.discoveries[d.ID] = d

	// Check for milestone achievements
	g.checkMilestones(ctx, d)

	return nil
}

// GetDiscovery retrieves a discovery by ID
func (g *MemoryDiscoveryGraph) GetDiscovery(ctx context.Context, id string) (*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	d, ok := g.discoveries[id]
	if !ok {
		return nil, fmt.Errorf("discovery not found: %s", id)
	}

	return d, nil
}

// GetUserDiscoveries retrieves all discoveries for a user
func (g *MemoryDiscoveryGraph) GetUserDiscoveries(ctx context.Context, userID string) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var results []*Discovery
	for _, d := range g.discoveries {
		if d.UserID == userID {
			results = append(results, d)
		}
	}

	return results, nil
}

// GetRelatedDiscoveries finds discoveries related to a concept
func (g *MemoryDiscoveryGraph) GetRelatedDiscoveries(ctx context.Context, conceptID string) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var results []*Discovery
	for _, d := range g.discoveries {
		for _, conn := range d.Connections {
			if conn == conceptID {
				results = append(results, d)
				break
			}
		}
	}

	return results, nil
}

// SearchDiscoveries searches discoveries by text
func (g *MemoryDiscoveryGraph) SearchDiscoveries(ctx context.Context, query string) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	query = strings.ToLower(query)
	var results []*Discovery

	for _, d := range g.discoveries {
		if strings.Contains(strings.ToLower(d.Anchor), query) ||
		   strings.Contains(strings.ToLower(d.Insight), query) {
			results = append(results, d)
		}
	}

	return results, nil
}

// GetDiscoveriesByDomain retrieves discoveries in a specific domain
func (g *MemoryDiscoveryGraph) GetDiscoveriesByDomain(ctx context.Context, domain string) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var results []*Discovery
	for _, d := range g.discoveries {
		for _, dm := range d.Domains {
			if strings.EqualFold(dm, domain) {
				results = append(results, d)
				break
			}
		}
	}

	return results, nil
}

// GetDiscoveriesByTag retrieves discoveries with a specific tag
func (g *MemoryDiscoveryGraph) GetDiscoveriesByTag(ctx context.Context, tag string) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	var results []*Discovery
	for _, d := range g.discoveries {
		for _, t := range d.Tags {
			if strings.EqualFold(t, tag) {
				results = append(results, d)
				break
			}
		}
	}

	return results, nil
}

// CelebrateDiscovery increments celebration count
func (g *MemoryDiscoveryGraph) CelebrateDiscovery(ctx context.Context, discoveryID string) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	d, ok := g.discoveries[discoveryID]
	if !ok {
		return fmt.Errorf("discovery not found: %s", discoveryID)
	}

	d.Celebrations++
	d.UpdatedAt = time.Now()

	return nil
}

// ShareDiscovery records sharing between users
func (g *MemoryDiscoveryGraph) ShareDiscovery(ctx context.Context, discoveryID, fromUserID, toUserID string) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	d, ok := g.discoveries[discoveryID]
	if !ok {
		return fmt.Errorf("discovery not found: %s", discoveryID)
	}

	d.Shares++
	d.UpdatedAt = time.Now()

	return nil
}

// GetDiscoveryStats computes analytics for a user
func (g *MemoryDiscoveryGraph) GetDiscoveryStats(ctx context.Context, userID string) (*DiscoveryStats, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	stats := &DiscoveryStats{
		DomainBreakdown: make(map[string]int),
	}

	domainSet := make(map[string]bool)
	totalDepth := 0
	maxCelebrations := 0

	for _, d := range g.discoveries {
		if d.UserID != userID {
			continue
		}

		stats.TotalDiscoveries++

		if d.Verified {
			stats.ProofsVerified++
		}

		// Track domains
		for _, domain := range d.Domains {
			domainSet[domain] = true
			stats.DomainBreakdown[domain]++
		}

		// Chain depth
		totalDepth += len(d.WhyChain)

		// Celebrations
		stats.TotalCelebrations += d.Celebrations
		if d.Celebrations > maxCelebrations {
			maxCelebrations = d.Celebrations
			stats.MostCelebratedID = d.ID
		}

		// Cross-domain links
		if len(d.Domains) > 1 {
			stats.CrossDomainLinks++
		}
	}

	// Convert domain set to slice
	for domain := range domainSet {
		stats.DomainsExplored = append(stats.DomainsExplored, domain)
	}

	// Average chain depth
	if stats.TotalDiscoveries > 0 {
		stats.AverageChainDepth = float64(totalDepth) / float64(stats.TotalDiscoveries)
	}

	return stats, nil
}

// GetPopularDiscoveries retrieves most celebrated discoveries
func (g *MemoryDiscoveryGraph) GetPopularDiscoveries(ctx context.Context, limit int) ([]*Discovery, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	// Convert map to slice
	var all []*Discovery
	for _, d := range g.discoveries {
		all = append(all, d)
	}

	// Simple bubble sort by celebrations (good enough for in-memory)
	for i := 0; i < len(all)-1; i++ {
		for j := 0; j < len(all)-i-1; j++ {
			if all[j].Celebrations < all[j+1].Celebrations {
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

// checkMilestones checks if discovery triggers any milestones
func (g *MemoryDiscoveryGraph) checkMilestones(ctx context.Context, d *Discovery) {
	userID := d.UserID

	// Check first discovery
	userDiscoveries := 0
	for _, disc := range g.discoveries {
		if disc.UserID == userID {
			userDiscoveries++
		}
	}

	if userDiscoveries == 1 {
		g.addMilestone(userID, &Milestone{
			Type:        MilestoneFirstDiscovery,
			Title:       "First Discovery!",
			Description: "Made your first discovery in the knowledge graph",
			Achieved:    time.Now(),
		})
	}

	// Check first proof
	if d.Verified && !g.hasVerifiedProof(userID, d.ID) {
		g.addMilestone(userID, &Milestone{
			Type:        MilestoneFirstProof,
			Title:       "First Proof Verified!",
			Description: "First Lean proof successfully verified",
			Achieved:    time.Now(),
		})
	}

	// Check cross-domain
	if len(d.Domains) >= 2 {
		g.addMilestone(userID, &Milestone{
			Type:        MilestoneCrossDomain,
			Title:       "Cross-Domain Explorer",
			Description: fmt.Sprintf("Connected %s and %s", d.Domains[0], d.Domains[1]),
			Achieved:    time.Now(),
		})
	}

	// Check deep dive (>10 why questions)
	if len(d.WhyChain) >= 10 {
		g.addMilestone(userID, &Milestone{
			Type:        MilestoneDeepDive,
			Title:       "Deep Diver",
			Description: fmt.Sprintf("Explored %d levels deep in the why chain", len(d.WhyChain)),
			Achieved:    time.Now(),
		})
	}
}

// hasVerifiedProof checks if user has other verified proofs
func (g *MemoryDiscoveryGraph) hasVerifiedProof(userID, excludeID string) bool {
	for _, d := range g.discoveries {
		if d.UserID == userID && d.ID != excludeID && d.Verified {
			return true
		}
	}
	return false
}

// addMilestone adds a milestone for a user
func (g *MemoryDiscoveryGraph) addMilestone(userID string, m *Milestone) {
	m.ID = fmt.Sprintf("milestone_%d", time.Now().UnixNano())
	m.UserID = userID

	if g.milestones[userID] == nil {
		g.milestones[userID] = []*Milestone{}
	}

	g.milestones[userID] = append(g.milestones[userID], m)
}

// GetUserMilestones retrieves all milestones for a user
func (g *MemoryDiscoveryGraph) GetUserMilestones(ctx context.Context, userID string) ([]*Milestone, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	milestones, ok := g.milestones[userID]
	if !ok {
		return []*Milestone{}, nil
	}

	return milestones, nil
}
