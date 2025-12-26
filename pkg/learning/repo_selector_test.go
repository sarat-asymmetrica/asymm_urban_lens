package learning

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"
)

// TestCalculateStarsScore verifies logarithmic star scaling
func TestCalculateStarsScore(t *testing.T) {
	tests := []struct {
		name     string
		stars    int
		expected float64
		tolerance float64
	}{
		{"Zero stars", 0, 0.0, 0.01},
		{"One star", 1, 0.0, 0.01},
		{"1000 stars", 1000, 0.60, 0.01},
		{"10000 stars", 10000, 0.80, 0.01},
		{"100000 stars", 100000, 1.0, 0.01},
		{"Mega popular (1M stars)", 1000000, 1.0, 0.01}, // Capped at 1.0
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := CalculateStarsScore(tt.stars)
			if score < (tt.expected-tt.tolerance) || score > (tt.expected+tt.tolerance) {
				t.Errorf("CalculateStarsScore(%d) = %f; want %f (+/- %f)",
					tt.stars, score, tt.expected, tt.tolerance)
			}
		})
	}
}

// TestCalculateFreshnessScore verifies exponential decay based on update date
func TestCalculateFreshnessScore(t *testing.T) {
	now := time.Now()

	tests := []struct {
		name       string
		lastUpdate time.Time
		minScore   float64
		maxScore   float64
	}{
		{"Updated yesterday", now.Add(-24 * time.Hour), 0.99, 1.0},
		{"Updated 30 days ago", now.Add(-30 * 24 * time.Hour), 0.99, 1.0},
		{"Updated 90 days ago", now.Add(-90 * 24 * time.Hour), 0.99, 1.0},
		{"Updated 180 days ago", now.Add(-180 * 24 * time.Hour), 0.50, 0.90},
		{"Updated 365 days ago", now.Add(-365 * 24 * time.Hour), 0.30, 0.50},
		{"Updated 730 days ago", now.Add(-730 * 24 * time.Hour), 0.10, 0.20},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := CalculateFreshnessScore(tt.lastUpdate)
			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("CalculateFreshnessScore(%v) = %f; want between %f and %f",
					tt.lastUpdate, score, tt.minScore, tt.maxScore)
			}
		})
	}
}

// TestCalculateCIScore verifies binary CI scoring
func TestCalculateCIScore(t *testing.T) {
	tests := []struct {
		name     string
		hasCI    bool
		expected float64
	}{
		{"Has CI", true, 1.0},
		{"No CI", false, 0.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := CalculateCIScore(tt.hasCI)
			if score != tt.expected {
				t.Errorf("CalculateCIScore(%v) = %f; want %f",
					tt.hasCI, score, tt.expected)
			}
		})
	}
}

// TestCalculateDocsScore verifies documentation quality scoring
func TestCalculateDocsScore(t *testing.T) {
	tests := []struct {
		name       string
		hasReadme  bool
		hasDocsDir bool
		expected   float64
	}{
		{"README + docs/", true, true, 1.0},
		{"README only", true, false, 0.5},
		{"No docs", false, false, 0.0},
		{"docs/ without README (unusual)", false, true, 0.0},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := CalculateDocsScore(tt.hasReadme, tt.hasDocsDir)
			if score != tt.expected {
				t.Errorf("CalculateDocsScore(%v, %v) = %f; want %f",
					tt.hasReadme, tt.hasDocsDir, score, tt.expected)
			}
		})
	}
}

// TestScoreRepo verifies composite scoring formula
func TestScoreRepo(t *testing.T) {
	now := time.Now()

	tests := []struct {
		name       string
		stars      int
		lastUpdate time.Time
		hasCI      bool
		hasDocs    bool
		hasDocsDir bool
		minScore   float64
		maxScore   float64
	}{
		{
			name:       "Perfect repo",
			stars:      10000,
			lastUpdate: now.Add(-30 * 24 * time.Hour), // 30 days ago
			hasCI:      true,
			hasDocs:    true,
			hasDocsDir: true,
			minScore:   0.85,
			maxScore:   1.0,
		},
		{
			name:       "Popular but old",
			stars:      50000,
			lastUpdate: now.Add(-730 * 24 * time.Hour), // 2 years ago
			hasCI:      true,
			hasDocs:    true,
			hasDocsDir: true,
			minScore:   0.60,
			maxScore:   0.75,
		},
		{
			name:       "New but few stars",
			stars:      100,
			lastUpdate: now.Add(-7 * 24 * time.Hour), // 1 week ago
			hasCI:      true,
			hasDocs:    true,
			hasDocsDir: false,
			minScore:   0.68,
			maxScore:   0.73,
		},
		{
			name:       "No CI, poor docs",
			stars:      5000,
			lastUpdate: now.Add(-90 * 24 * time.Hour), // 90 days ago
			hasCI:      false,
			hasDocs:    true,
			hasDocsDir: false,
			minScore:   0.50,
			maxScore:   0.65,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			score := ScoreRepo(tt.stars, tt.lastUpdate, tt.hasCI, tt.hasDocs, tt.hasDocsDir)
			if score < tt.minScore || score > tt.maxScore {
				t.Errorf("ScoreRepo(...) = %f; want between %f and %f",
					score, tt.minScore, tt.maxScore)
			}
		})
	}
}

// TestRepoCache verifies cache CRUD operations
func TestRepoCache(t *testing.T) {
	// Create temporary database
	dbPath := "test_cache.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	// Test Set and Get
	now := time.Now()
	repo := &CachedRepo{
		FullName:    "spf13/cobra",
		Stars:       25000,
		LastUpdate:  now.AddDate(0, -1, 0),
		HasCI:       true,
		HasDocs:     true,
		HasDocsDir:  true,
		Score:       0.92,
		CachedAt:    now,
		Description: "A Commander for modern Go CLI applications",
		Language:    "Go",
	}

	if err := cache.Set(repo); err != nil {
		t.Fatalf("cache.Set failed: %v", err)
	}

	// Retrieve and verify
	ttl := 7 * 24 * time.Hour
	retrieved, err := cache.Get("spf13/cobra", ttl)
	if err != nil {
		t.Fatalf("cache.Get failed: %v", err)
	}
	if retrieved == nil {
		t.Fatal("cache.Get returned nil for existing entry")
	}

	if retrieved.FullName != repo.FullName {
		t.Errorf("Retrieved FullName = %s; want %s", retrieved.FullName, repo.FullName)
	}
	if retrieved.Stars != repo.Stars {
		t.Errorf("Retrieved Stars = %d; want %d", retrieved.Stars, repo.Stars)
	}
	if retrieved.Score != repo.Score {
		t.Errorf("Retrieved Score = %f; want %f", retrieved.Score, repo.Score)
	}
}

// TestCacheTTLExpiration verifies that expired entries are not returned
func TestCacheTTLExpiration(t *testing.T) {
	dbPath := "test_cache_ttl.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	// Add entry with old cached_at timestamp
	oldTime := time.Now().Add(-10 * 24 * time.Hour) // 10 days ago
	repo := &CachedRepo{
		FullName:   "old/repo",
		Stars:      1000,
		LastUpdate: time.Now(),
		HasCI:      true,
		HasDocs:    true,
		HasDocsDir: true,
		Score:      0.80,
		CachedAt:   oldTime,
		Language:   "Go",
	}

	if err := cache.Set(repo); err != nil {
		t.Fatalf("cache.Set failed: %v", err)
	}

	// Try to retrieve with 7-day TTL (should fail - entry is 10 days old)
	ttl := 7 * 24 * time.Hour
	retrieved, err := cache.Get("old/repo", ttl)
	if err != nil {
		t.Fatalf("cache.Get failed: %v", err)
	}
	if retrieved != nil {
		t.Errorf("cache.Get returned non-nil for expired entry: %+v", retrieved)
	}
}

// TestCacheInvalidate verifies cache entry removal
func TestCacheInvalidate(t *testing.T) {
	dbPath := "test_cache_invalidate.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	// Add entry
	repo := &CachedRepo{
		FullName:   "test/repo",
		Stars:      1000,
		LastUpdate: time.Now(),
		HasCI:      true,
		HasDocs:    true,
		HasDocsDir: true,
		Score:      0.80,
		CachedAt:   time.Now(),
		Language:   "Go",
	}

	if err := cache.Set(repo); err != nil {
		t.Fatalf("cache.Set failed: %v", err)
	}

	// Invalidate
	if err := cache.Invalidate("test/repo"); err != nil {
		t.Fatalf("cache.Invalidate failed: %v", err)
	}

	// Verify removal
	ttl := 7 * 24 * time.Hour
	retrieved, err := cache.Get("test/repo", ttl)
	if err != nil {
		t.Fatalf("cache.Get failed: %v", err)
	}
	if retrieved != nil {
		t.Error("cache.Get returned non-nil after invalidation")
	}
}

// TestRepoSelector verifies repository selection and filtering
func TestRepoSelector(t *testing.T) {
	dbPath := "test_selector.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	selector := NewRepoSelector(cache)

	// Seed cache with test data
	now := time.Now()
	testRepos := []ScoredRepo{
		{
			FullName:   "spf13/cobra",
			Stars:      25000,
			LastUpdate: now.AddDate(0, -1, 0),
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Language:   "Go",
		},
		{
			FullName:   "spf13/viper",
			Stars:      20000,
			LastUpdate: now.AddDate(0, -2, 0),
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Language:   "Go",
		},
		{
			FullName:   "gin-gonic/gin",
			Stars:      65000,
			LastUpdate: now.AddDate(0, -1, 0),
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Language:   "Go",
		},
		{
			FullName:   "labstack/echo",
			Stars:      24000,
			LastUpdate: now.AddDate(0, -1, 0),
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Language:   "Go",
		},
		{
			FullName:   "old/repo",
			Stars:      50000,
			LastUpdate: now.AddDate(-2, 0, 0), // 2 years old
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Language:   "Go",
		},
	}

	for _, repo := range testRepos {
		if err := selector.ScoreAndCacheRepo(repo); err != nil {
			t.Fatalf("ScoreAndCacheRepo failed: %v", err)
		}
	}

	// Test selection with criteria
	criteria := SelectionCriteria{
		MinStars:     10000,
		UpdatedAfter: now.AddDate(-1, 0, 0), // Within last year
		HasCI:        true,
		HasDocs:      true,
		Languages:    []string{"Go"},
		MaxResults:   3,
	}

	selected, err := selector.SelectRepos(context.Background(), criteria)
	if err != nil {
		t.Fatalf("SelectRepos failed: %v", err)
	}

	// Verify results
	if len(selected) != 3 {
		t.Errorf("Selected %d repos; want 3", len(selected))
	}

	// Verify ranking (highest score first)
	for i := 0; i < len(selected)-1; i++ {
		if selected[i].Score < selected[i+1].Score {
			t.Errorf("Repos not properly ranked: repo %d score (%f) < repo %d score (%f)",
				i, selected[i].Score, i+1, selected[i+1].Score)
		}
	}

	// Verify ranks are assigned
	for i, repo := range selected {
		expectedRank := i + 1
		if repo.Rank != expectedRank {
			t.Errorf("Repo %s has rank %d; want %d", repo.FullName, repo.Rank, expectedRank)
		}
	}
}

// TestExpectedReposSelection verifies that cobra, viper, gin, echo, chi are ranked highly for Go web frameworks
func TestExpectedReposSelection(t *testing.T) {
	dbPath := "test_expected_repos.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	selector := NewRepoSelector(cache)

	// Seed with well-known Go repos
	now := time.Now()
	wellKnownRepos := []ScoredRepo{
		{FullName: "spf13/cobra", Stars: 32000, LastUpdate: now.Add(-30 * 24 * time.Hour), HasCI: true, HasDocs: true, HasDocsDir: true, Language: "Go"},
		{FullName: "spf13/viper", Stars: 23000, LastUpdate: now.Add(-30 * 24 * time.Hour), HasCI: true, HasDocs: true, HasDocsDir: true, Language: "Go"},
		{FullName: "gin-gonic/gin", Stars: 72000, LastUpdate: now.Add(-30 * 24 * time.Hour), HasCI: true, HasDocs: true, HasDocsDir: true, Language: "Go"},
		{FullName: "labstack/echo", Stars: 27000, LastUpdate: now.Add(-30 * 24 * time.Hour), HasCI: true, HasDocs: true, HasDocsDir: true, Language: "Go"},
		{FullName: "go-chi/chi", Stars: 15000, LastUpdate: now.Add(-30 * 24 * time.Hour), HasCI: true, HasDocs: true, HasDocsDir: true, Language: "Go"},
	}

	for _, repo := range wellKnownRepos {
		if err := selector.ScoreAndCacheRepo(repo); err != nil {
			t.Fatalf("ScoreAndCacheRepo failed: %v", err)
		}
	}

	// Select top repos
	criteria := SelectionCriteria{
		MinStars:     1000,
		UpdatedAfter: now.AddDate(-1, 0, 0),
		Languages:    []string{"Go"},
		MaxResults:   20,
	}

	selected, err := selector.SelectRepos(context.Background(), criteria)
	if err != nil {
		t.Fatalf("SelectRepos failed: %v", err)
	}

	// Verify all expected repos are present
	expectedRepos := []string{"spf13/cobra", "spf13/viper", "gin-gonic/gin", "labstack/echo", "go-chi/chi"}
	foundRepos := make(map[string]bool)

	for _, repo := range selected {
		foundRepos[repo.FullName] = true
	}

	for _, expected := range expectedRepos {
		if !foundRepos[expected] {
			t.Errorf("Expected repo %s not found in selection", expected)
		}
	}

	// Verify gin is ranked highest (most stars)
	if len(selected) > 0 && selected[0].FullName != "gin-gonic/gin" {
		t.Errorf("Top ranked repo is %s; expected gin-gonic/gin", selected[0].FullName)
	}
}

// TestCacheStats verifies cache statistics calculation
func TestCacheStats(t *testing.T) {
	dbPath := "test_cache_stats.db"
	defer os.Remove(dbPath)

	cache, err := NewRepoCache(dbPath)
	if err != nil {
		t.Fatalf("NewRepoCache failed: %v", err)
	}
	defer cache.Close()

	selector := NewRepoSelector(cache)

	// Add some fresh entries
	now := time.Now()
	for i := 0; i < 5; i++ {
		repo := &CachedRepo{
			FullName:   fmt.Sprintf("fresh/repo%d", i),
			Stars:      1000,
			LastUpdate: now,
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Score:      0.8,
			CachedAt:   now,
			Language:   "Go",
		}
		if err := cache.Set(repo); err != nil {
			t.Fatalf("cache.Set failed: %v", err)
		}
	}

	// Add some expired entries
	oldTime := now.Add(-10 * 24 * time.Hour)
	for i := 0; i < 3; i++ {
		repo := &CachedRepo{
			FullName:   fmt.Sprintf("old/repo%d", i),
			Stars:      1000,
			LastUpdate: now,
			HasCI:      true,
			HasDocs:    true,
			HasDocsDir: true,
			Score:      0.8,
			CachedAt:   oldTime,
			Language:   "Go",
		}
		if err := cache.Set(repo); err != nil {
			t.Fatalf("cache.Set failed: %v", err)
		}
	}

	// Get stats
	stats, err := selector.GetCacheStats()
	if err != nil {
		t.Fatalf("GetCacheStats failed: %v", err)
	}

	if stats.TotalEntries != 8 {
		t.Errorf("TotalEntries = %d; want 8", stats.TotalEntries)
	}
	if stats.ValidEntries != 5 {
		t.Errorf("ValidEntries = %d; want 5", stats.ValidEntries)
	}
	if stats.ExpiredEntries != 3 {
		t.Errorf("ExpiredEntries = %d; want 3", stats.ExpiredEntries)
	}
}
