// Package knowledge - User learning journey tracking and analytics
package knowledge

import (
	"context"
	"fmt"
	"sort"
	"sync"
	"time"
)

// ═══════════════════════════════════════════════════════════════════════════
// JOURNEY TYPES
// ═══════════════════════════════════════════════════════════════════════════

// LearningJourney represents a user's complete learning experience
type LearningJourney struct {
	UserID      string      `json:"user_id"`
	StartTime   time.Time   `json:"start_time"`
	LastActive  time.Time   `json:"last_active"`

	// Discovery tracking
	Anchors     []string    `json:"anchors"`       // All starting observations
	Insights    []string    `json:"insights"`      // All insights gained
	Proofs      []string    `json:"proofs"`        // All theorems proven

	// Domain exploration
	Domains     []string    `json:"domains"`       // Domains explored
	DomainTime  map[string]int `json:"domain_time"` // Time spent per domain (minutes)

	// Achievements
	Milestones  []*Milestone `json:"milestones"`   // Special achievements

	// Progress metrics
	TotalTime       int     `json:"total_time"`        // Total learning time (minutes)
	ConceptsLearned int     `json:"concepts_learned"`  // Unique concepts visited
	DepthReached    int     `json:"depth_reached"`     // Deepest "why" chain

	// Social engagement
	Shared          int     `json:"shared"`            // Discoveries shared
	Helped          int     `json:"helped"`            // Times helped others
}

// JourneySnapshot represents a point-in-time view of progress
type JourneySnapshot struct {
	Timestamp       time.Time          `json:"timestamp"`
	ConceptsLearned int                `json:"concepts_learned"`
	DiscoveriesMade int                `json:"discoveries_made"`
	ProofsVerified  int                `json:"proofs_verified"`
	DomainLevels    map[string]int     `json:"domain_levels"`
}

// ProgressReport provides human-readable journey summary
type ProgressReport struct {
	UserID          string             `json:"user_id"`
	DaysActive      int                `json:"days_active"`
	TotalTime       int                `json:"total_time_minutes"`

	// Learning stats
	ConceptsLearned int                `json:"concepts_learned"`
	DiscoveriesMade int                `json:"discoveries_made"`
	ProofsVerified  int                `json:"proofs_verified"`

	// Domain breakdown
	DomainsExplored []string           `json:"domains_explored"`
	StrongestDomain string             `json:"strongest_domain"`

	// Achievements
	MilestoneCount  int                `json:"milestone_count"`
	RecentMilestones []*Milestone      `json:"recent_milestones"`

	// Engagement
	AverageDepth    float64            `json:"average_depth"`
	CrossDomainLinks int               `json:"cross_domain_links"`

	// Next steps
	SuggestedNext   []Suggestion       `json:"suggested_next"`
}

// WeeklyActivity tracks engagement over time
type WeeklyActivity struct {
	Week         int       `json:"week"`
	StartDate    time.Time `json:"start_date"`
	EndDate      time.Time `json:"end_date"`

	TimeSpent        int `json:"time_spent"`
	ConceptsVisited  int `json:"concepts_visited"`
	DiscoveriesMade  int `json:"discoveries_made"`
	ProofsCompleted  int `json:"proofs_completed"`
}

// ═══════════════════════════════════════════════════════════════════════════
// JOURNEY INTERFACE EXTENSION
// ═══════════════════════════════════════════════════════════════════════════

// JourneyGraph extends ConnectionGraph with journey tracking
type JourneyGraph interface {
	ConnectionGraph

	// Journey management
	CreateJourney(ctx context.Context, userID string) (*LearningJourney, error)
	GetJourney(ctx context.Context, userID string) (*LearningJourney, error)
	UpdateJourney(ctx context.Context, journey *LearningJourney) error

	// Milestones
	RecordMilestone(ctx context.Context, userID string, milestone *Milestone) error
	GetMilestones(ctx context.Context, userID string) ([]*Milestone, error)

	// Progress tracking
	RecordProgress(ctx context.Context, userID string, conceptID string, timeSpent int) error
	GetProgressReport(ctx context.Context, userID string) (*ProgressReport, error)
	GetWeeklyActivity(ctx context.Context, userID string, weeks int) ([]WeeklyActivity, error)

	// Snapshots
	TakeSnapshot(ctx context.Context, userID string) (*JourneySnapshot, error)
	GetSnapshots(ctx context.Context, userID string) ([]*JourneySnapshot, error)
}

// ═══════════════════════════════════════════════════════════════════════════
// MEMORY IMPLEMENTATION - JOURNEY
// ═══════════════════════════════════════════════════════════════════════════

// MemoryJourneyGraph extends MemoryConnectionGraph with journey tracking
type MemoryJourneyGraph struct {
	*MemoryConnectionGraph
	journeys  map[string]*LearningJourney
	snapshots map[string][]*JourneySnapshot // userID -> snapshots
	mu        sync.RWMutex
}

// NewMemoryJourneyGraph creates a complete in-memory knowledge graph
func NewMemoryJourneyGraph() *MemoryJourneyGraph {
	return &MemoryJourneyGraph{
		MemoryConnectionGraph: NewMemoryConnectionGraph(),
		journeys:              make(map[string]*LearningJourney),
		snapshots:             make(map[string][]*JourneySnapshot),
	}
}

// CreateJourney initializes a new learning journey
func (g *MemoryJourneyGraph) CreateJourney(ctx context.Context, userID string) (*LearningJourney, error) {
	g.mu.Lock()
	defer g.mu.Unlock()

	if _, exists := g.journeys[userID]; exists {
		return nil, fmt.Errorf("journey already exists for user: %s", userID)
	}

	now := time.Now()
	journey := &LearningJourney{
		UserID:      userID,
		StartTime:   now,
		LastActive:  now,
		Anchors:     []string{},
		Insights:    []string{},
		Proofs:      []string{},
		Domains:     []string{},
		DomainTime:  make(map[string]int),
		Milestones:  []*Milestone{},
	}

	g.journeys[userID] = journey

	// Also create UserJourney in base graph
	g.MemoryGraph.journeys[userID] = &UserJourney{
		UserID:          userID,
		ConceptsVisited: []ConceptVisit{},
		ProofsCompleted: []string{},
		CurrentLevel:    make(map[string]int),
		Interests:       make(map[string]float64),
	}

	return journey, nil
}

// GetJourney retrieves a learning journey
func (g *MemoryJourneyGraph) GetJourney(ctx context.Context, userID string) (*LearningJourney, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return nil, fmt.Errorf("no journey found for user: %s", userID)
	}

	return journey, nil
}

// UpdateJourney updates an existing journey
func (g *MemoryJourneyGraph) UpdateJourney(ctx context.Context, journey *LearningJourney) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	if _, exists := g.journeys[journey.UserID]; !exists {
		return fmt.Errorf("journey not found for user: %s", journey.UserID)
	}

	journey.LastActive = time.Now()
	g.journeys[journey.UserID] = journey

	return nil
}

// RecordMilestone adds a milestone to user's journey
func (g *MemoryJourneyGraph) RecordMilestone(ctx context.Context, userID string, milestone *Milestone) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return fmt.Errorf("no journey found for user: %s", userID)
	}

	milestone.ID = fmt.Sprintf("milestone_%d", time.Now().UnixNano())
	milestone.UserID = userID
	milestone.Achieved = time.Now()

	journey.Milestones = append(journey.Milestones, milestone)
	journey.LastActive = time.Now()

	return nil
}

// GetMilestones retrieves all milestones for a user
func (g *MemoryJourneyGraph) GetMilestones(ctx context.Context, userID string) ([]*Milestone, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return []*Milestone{}, nil
	}

	return journey.Milestones, nil
}

// RecordProgress logs learning progress
func (g *MemoryJourneyGraph) RecordProgress(ctx context.Context, userID string, conceptID string, timeSpent int) error {
	g.mu.Lock()
	defer g.mu.Unlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return fmt.Errorf("no journey found for user: %s", userID)
	}

	// Get concept to find domain
	concept, err := g.MemoryGraph.GetConcept(ctx, conceptID)
	if err != nil {
		return err
	}

	// Update domain time
	journey.DomainTime[concept.Domain] += timeSpent
	journey.TotalTime += timeSpent
	journey.LastActive = time.Now()

	// Add domain to list if not present
	if !contains(journey.Domains, concept.Domain) {
		journey.Domains = append(journey.Domains, concept.Domain)
	}

	// Increment concepts learned
	journey.ConceptsLearned++

	return nil
}

// GetProgressReport generates comprehensive progress report
func (g *MemoryJourneyGraph) GetProgressReport(ctx context.Context, userID string) (*ProgressReport, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return nil, fmt.Errorf("no journey found for user: %s", userID)
	}

	// Calculate days active
	daysActive := int(time.Since(journey.StartTime).Hours() / 24)
	if daysActive == 0 {
		daysActive = 1
	}

	// Get discovery stats
	discoveries, _ := g.GetUserDiscoveries(ctx, userID)
	stats, _ := g.GetDiscoveryStats(ctx, userID)

	// Find strongest domain
	strongestDomain := ""
	maxTime := 0
	for domain, t := range journey.DomainTime {
		if t > maxTime {
			maxTime = t
			strongestDomain = domain
		}
	}

	// Get recent milestones (last 5)
	recentMilestones := journey.Milestones
	if len(recentMilestones) > 5 {
		recentMilestones = recentMilestones[len(recentMilestones)-5:]
	}

	// Generate suggestions
	profile := UserProfile{
		UserID:         userID,
		Interests:      journey.Domains,
		TimeAvailable:  30,
		PreferredPace:  "medium",
	}

	var suggestions []Suggestion
	if len(discoveries) > 0 {
		lastDiscovery := discoveries[len(discoveries)-1]
		if len(lastDiscovery.Connections) > 0 {
			suggestions, _ = g.SuggestExplorations(ctx, lastDiscovery.Connections[0], profile)
		}
	}

	report := &ProgressReport{
		UserID:           userID,
		DaysActive:       daysActive,
		TotalTime:        journey.TotalTime,
		ConceptsLearned:  journey.ConceptsLearned,
		DiscoveriesMade:  len(discoveries),
		ProofsVerified:   stats.ProofsVerified,
		DomainsExplored:  journey.Domains,
		StrongestDomain:  strongestDomain,
		MilestoneCount:   len(journey.Milestones),
		RecentMilestones: recentMilestones,
		AverageDepth:     stats.AverageChainDepth,
		CrossDomainLinks: stats.CrossDomainLinks,
		SuggestedNext:    suggestions,
	}

	return report, nil
}

// GetWeeklyActivity calculates activity over past N weeks
func (g *MemoryJourneyGraph) GetWeeklyActivity(ctx context.Context, userID string, weeks int) ([]WeeklyActivity, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	_, exists := g.journeys[userID]
	if !exists {
		return nil, fmt.Errorf("no journey found for user: %s", userID)
	}

	// Get all user discoveries
	discoveries, _ := g.GetUserDiscoveries(ctx, userID)

	// Get base user journey for concept visits
	baseJourney, _ := g.MemoryGraph.GetUserJourney(ctx, userID)

	// Calculate weekly buckets
	now := time.Now()
	weeklyData := make(map[int]*WeeklyActivity)

	// Initialize weeks
	for i := 0; i < weeks; i++ {
		weekStart := now.AddDate(0, 0, -7*(i+1))
		weekEnd := now.AddDate(0, 0, -7*i)

		weeklyData[i] = &WeeklyActivity{
			Week:      i + 1,
			StartDate: weekStart,
			EndDate:   weekEnd,
		}
	}

	// Aggregate discoveries
	for _, discovery := range discoveries {
		weekNum := g.getWeekNumber(discovery.Timestamp, now, weeks)
		if weekNum >= 0 && weekNum < weeks {
			week := weeklyData[weekNum]
			week.DiscoveriesMade++
			if discovery.Verified {
				week.ProofsCompleted++
			}
		}
	}

	// Aggregate concept visits
	if baseJourney != nil {
		for _, visit := range baseJourney.ConceptsVisited {
			weekNum := g.getWeekNumber(visit.VisitedAt, now, weeks)
			if weekNum >= 0 && weekNum < weeks {
				week := weeklyData[weekNum]
				week.ConceptsVisited++
				week.TimeSpent += visit.TimeSpent
			}
		}
	}

	// Convert map to sorted slice
	var result []WeeklyActivity
	for i := weeks - 1; i >= 0; i-- {
		result = append(result, *weeklyData[i])
	}

	return result, nil
}

// TakeSnapshot creates a point-in-time progress snapshot
func (g *MemoryJourneyGraph) TakeSnapshot(ctx context.Context, userID string) (*JourneySnapshot, error) {
	g.mu.Lock()
	defer g.mu.Unlock()

	journey, exists := g.journeys[userID]
	if !exists {
		return nil, fmt.Errorf("no journey found for user: %s", userID)
	}

	// Get discovery count
	discoveries, _ := g.GetUserDiscoveries(ctx, userID)
	stats, _ := g.GetDiscoveryStats(ctx, userID)

	// Get base journey for concept count
	baseJourney, _ := g.MemoryGraph.GetUserJourney(ctx, userID)
	conceptsLearned := 0
	if baseJourney != nil {
		conceptsLearned = len(baseJourney.ConceptsVisited)
	}

	snapshot := &JourneySnapshot{
		Timestamp:       time.Now(),
		ConceptsLearned: conceptsLearned,
		DiscoveriesMade: len(discoveries),
		ProofsVerified:  stats.ProofsVerified,
		DomainLevels:    make(map[string]int),
	}

	// Copy domain levels
	if baseJourney != nil {
		for domain, level := range baseJourney.CurrentLevel {
			snapshot.DomainLevels[domain] = level
		}
	}

	// Store snapshot
	if g.snapshots[userID] == nil {
		g.snapshots[userID] = []*JourneySnapshot{}
	}
	g.snapshots[userID] = append(g.snapshots[userID], snapshot)

	journey.LastActive = time.Now()

	return snapshot, nil
}

// GetSnapshots retrieves all snapshots for a user
func (g *MemoryJourneyGraph) GetSnapshots(ctx context.Context, userID string) ([]*JourneySnapshot, error) {
	g.mu.RLock()
	defer g.mu.RUnlock()

	snapshots, exists := g.snapshots[userID]
	if !exists {
		return []*JourneySnapshot{}, nil
	}

	// Sort by timestamp
	sorted := make([]*JourneySnapshot, len(snapshots))
	copy(sorted, snapshots)

	sort.Slice(sorted, func(i, j int) bool {
		return sorted[i].Timestamp.Before(sorted[j].Timestamp)
	})

	return sorted, nil
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// getWeekNumber calculates which week a timestamp falls into
func (g *MemoryJourneyGraph) getWeekNumber(t time.Time, now time.Time, maxWeeks int) int {
	diff := now.Sub(t)
	weeks := int(diff.Hours() / 24 / 7)

	if weeks >= maxWeeks {
		return -1
	}

	return weeks
}

// GenerateJourneySummary creates human-readable summary
func (g *MemoryJourneyGraph) GenerateJourneySummary(ctx context.Context, userID string) (string, error) {
	report, err := g.GetProgressReport(ctx, userID)
	if err != nil {
		return "", err
	}

	summary := fmt.Sprintf(`
🌟 Learning Journey Summary for %s

📊 STATS:
  • Active for %d days
  • Total learning time: %d minutes
  • Concepts explored: %d
  • Discoveries made: %d
  • Proofs verified: %d

🎯 DOMAINS:
  • Explored: %v
  • Strongest: %s

🏆 ACHIEVEMENTS:
  • Milestones earned: %d
  • Cross-domain links: %d
  • Average "why" depth: %.1f

`,
		userID,
		report.DaysActive,
		report.TotalTime,
		report.ConceptsLearned,
		report.DiscoveriesMade,
		report.ProofsVerified,
		report.DomainsExplored,
		report.StrongestDomain,
		report.MilestoneCount,
		report.CrossDomainLinks,
		report.AverageDepth,
	)

	// Add recent milestones
	if len(report.RecentMilestones) > 0 {
		summary += "🎖️  RECENT MILESTONES:\n"
		for _, m := range report.RecentMilestones {
			summary += fmt.Sprintf("  • %s: %s\n", m.Title, m.Description)
		}
	}

	// Add suggestions
	if len(report.SuggestedNext) > 0 {
		summary += "\n💡 SUGGESTED NEXT:\n"
		for i, s := range report.SuggestedNext {
			if i >= 3 {
				break
			}
			concept, _ := g.MemoryGraph.GetConcept(ctx, s.ConceptID)
			if concept != nil {
				summary += fmt.Sprintf("  • %s (%s) - %s\n", concept.Name, concept.Domain, s.Reason)
			}
		}
	}

	return summary, nil
}
