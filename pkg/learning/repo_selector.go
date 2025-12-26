package learning

import (
	"context"
	"fmt"
	"sort"
	"time"
)

// SelectionCriteria defines the parameters for selecting repositories.
// These criteria filter and rank repositories based on quality signals.
type SelectionCriteria struct {
	MinStars     int      // Minimum star count (e.g., 1000)
	UpdatedAfter time.Time // Only include repos updated after this date
	Domain       string   // Domain/topic (e.g., "web framework", "CLI tools")
	HasCI        bool     // Require CI/CD infrastructure
	HasDocs      bool     // Require documentation
	Languages    []string // Filter by programming language (e.g., ["Go", "Rust"])
	MaxResults   int      // Maximum number of repos to return
}

// ScoredRepo represents a repository with its computed quality score and metadata.
// Used for ranking repositories after scoring.
type ScoredRepo struct {
	FullName    string    // e.g., "spf13/cobra"
	Stars       int       // Star count
	LastUpdate  time.Time // When repo was last updated
	HasCI       bool      // Whether repo has CI/CD
	HasDocs     bool      // Whether repo has README
	HasDocsDir  bool      // Whether repo has docs/ directory
	Description string    // Repository description
	Language    string    // Primary programming language
	Score       float64   // Computed quality score (0.0-1.0)
	Rank        int       // Ranking among selected repos (1-indexed)
}

// RepoSelector provides repository selection and ranking functionality.
// It combines GitHub API access, caching, and scoring to select high-quality repositories.
type RepoSelector struct {
	cache    *RepoCache
	cacheTTL time.Duration
}

// NewRepoSelector creates a new repository selector with caching.
// The cache reduces GitHub API calls and improves performance.
//
// Default cache TTL: 7 days (GitHub repo metadata is relatively stable)
func NewRepoSelector(cache *RepoCache) *RepoSelector {
	return &RepoSelector{
		cache:    cache,
		cacheTTL: 7 * 24 * time.Hour, // 7 days default TTL
	}
}

// SelectRepos selects and ranks repositories based on the provided criteria.
// It uses the cache when possible to minimize GitHub API calls.
//
// Algorithm:
// 1. Check cache for existing scored repos
// 2. For cache misses, query GitHub API (via githubClient when integrated)
// 3. Score each repository using multi-dimensional scoring
// 4. Filter by criteria (stars, date, CI, docs, languages)
// 5. Rank by score (highest first)
// 6. Return top N repositories
//
// Note: This implementation prepares the structure for GitHub API integration.
// Once Agent 0.1 completes, we'll add the githubClient parameter and real API calls.
func (rs *RepoSelector) SelectRepos(ctx context.Context, criteria SelectionCriteria) ([]ScoredRepo, error) {
	// Step 1: Try to get cached results first
	cachedRepos, err := rs.cache.GetAll(rs.cacheTTL)
	if err != nil {
		return nil, fmt.Errorf("failed to query cache: %w", err)
	}

	// Convert cached repos to ScoredRepo format
	var scoredRepos []ScoredRepo
	for _, cached := range cachedRepos {
		scored := ScoredRepo{
			FullName:    cached.FullName,
			Stars:       cached.Stars,
			LastUpdate:  cached.LastUpdate,
			HasCI:       cached.HasCI,
			HasDocs:     cached.HasDocs,
			HasDocsDir:  cached.HasDocsDir,
			Description: cached.Description,
			Language:    cached.Language,
			Score:       cached.Score,
		}
		scoredRepos = append(scoredRepos, scored)
	}

	// Step 2: Filter by criteria
	filtered := rs.filterByCriteria(scoredRepos, criteria)

	// Step 3: Sort by score (highest first)
	sort.Slice(filtered, func(i, j int) bool {
		return filtered[i].Score > filtered[j].Score
	})

	// Step 4: Assign ranks
	for i := range filtered {
		filtered[i].Rank = i + 1
	}

	// Step 5: Limit to MaxResults
	if criteria.MaxResults > 0 && len(filtered) > criteria.MaxResults {
		filtered = filtered[:criteria.MaxResults]
	}

	return filtered, nil
}

// filterByCriteria filters repositories based on selection criteria.
func (rs *RepoSelector) filterByCriteria(repos []ScoredRepo, criteria SelectionCriteria) []ScoredRepo {
	var filtered []ScoredRepo

	for _, repo := range repos {
		// Filter by minimum stars
		if repo.Stars < criteria.MinStars {
			continue
		}

		// Filter by update date
		if !criteria.UpdatedAfter.IsZero() && repo.LastUpdate.Before(criteria.UpdatedAfter) {
			continue
		}

		// Filter by CI requirement
		if criteria.HasCI && !repo.HasCI {
			continue
		}

		// Filter by docs requirement
		if criteria.HasDocs && !repo.HasDocs {
			continue
		}

		// Filter by programming language
		if len(criteria.Languages) > 0 {
			langMatch := false
			for _, lang := range criteria.Languages {
				if repo.Language == lang {
					langMatch = true
					break
				}
			}
			if !langMatch {
				continue
			}
		}

		filtered = append(filtered, repo)
	}

	return filtered
}

// ScoreAndCacheRepo scores a single repository and caches the result.
// This is useful when integrating with Agent 0.1's GitHub client to cache new repos.
func (rs *RepoSelector) ScoreAndCacheRepo(repo ScoredRepo) error {
	// Calculate score if not already set
	if repo.Score == 0.0 {
		repo.Score = ScoreRepo(
			repo.Stars,
			repo.LastUpdate,
			repo.HasCI,
			repo.HasDocs,
			repo.HasDocsDir,
		)
	}

	// Cache the result
	cached := &CachedRepo{
		FullName:    repo.FullName,
		Stars:       repo.Stars,
		LastUpdate:  repo.LastUpdate,
		HasCI:       repo.HasCI,
		HasDocs:     repo.HasDocs,
		HasDocsDir:  repo.HasDocsDir,
		Score:       repo.Score,
		CachedAt:    time.Now(),
		Description: repo.Description,
		Language:    repo.Language,
	}

	return rs.cache.Set(cached)
}

// GetTopRepos returns the top N repositories from cache, ordered by score.
// This is a convenience method for quickly accessing highly-ranked repos.
func (rs *RepoSelector) GetTopRepos(n int) ([]ScoredRepo, error) {
	criteria := SelectionCriteria{
		MaxResults: n,
	}
	return rs.SelectRepos(context.Background(), criteria)
}

// InvalidateRepo removes a specific repository from the cache.
// Use this when you want to force a refresh of a repo's metadata.
func (rs *RepoSelector) InvalidateRepo(fullName string) error {
	return rs.cache.Invalidate(fullName)
}

// PurgeExpiredCache removes all expired cache entries.
// Returns the number of entries removed.
func (rs *RepoSelector) PurgeExpiredCache() (int64, error) {
	return rs.cache.PurgeExpired(rs.cacheTTL)
}

// UpdateCacheTTL changes the cache TTL setting.
// This affects future cache lookups but doesn't retroactively change existing entries.
func (rs *RepoSelector) UpdateCacheTTL(ttl time.Duration) {
	rs.cacheTTL = ttl
}

// GetCacheStats returns statistics about the repository cache.
// Useful for monitoring and debugging cache performance.
type CacheStats struct {
	TotalEntries   int
	ValidEntries   int
	ExpiredEntries int
}

// GetCacheStats calculates and returns cache statistics.
func (rs *RepoSelector) GetCacheStats() (CacheStats, error) {
	allRepos, err := rs.cache.GetAll(0) // Get all entries regardless of TTL
	if err != nil {
		return CacheStats{}, fmt.Errorf("failed to query cache: %w", err)
	}

	validRepos, err := rs.cache.GetAll(rs.cacheTTL) // Get only valid entries
	if err != nil {
		return CacheStats{}, fmt.Errorf("failed to query valid cache entries: %w", err)
	}

	stats := CacheStats{
		TotalEntries:   len(allRepos),
		ValidEntries:   len(validRepos),
		ExpiredEntries: len(allRepos) - len(validRepos),
	}

	return stats, nil
}
