package learning

import (
	"database/sql"
	"fmt"
	"time"

	_ "modernc.org/sqlite"
)

// RepoCache provides a SQLite-backed cache for repository metadata and scores.
// This minimizes GitHub API calls by storing previously fetched data with TTL-based expiration.
//
// Cache entries include:
// - Repository metadata (name, stars, last update, etc.)
// - Computed quality score
// - Timestamp of when cached
// - TTL for automatic expiration
type RepoCache struct {
	db *sql.DB
}

// CachedRepo represents a cached repository with its metadata and score.
type CachedRepo struct {
	FullName    string    // e.g., "spf13/cobra"
	Stars       int       // Star count at time of caching
	LastUpdate  time.Time // When repo was last updated
	HasCI       bool      // Whether repo has CI/CD
	HasDocs     bool      // Whether repo has README
	HasDocsDir  bool      // Whether repo has docs/ directory
	Score       float64   // Computed quality score
	CachedAt    time.Time // When this entry was cached
	Description string    // Repository description
	Language    string    // Primary language
}

// NewRepoCache creates a new repository cache backed by SQLite.
// The cache database is created at the specified path if it doesn't exist.
//
// Database schema:
// - repo_cache table: stores cached repository metadata and scores
// - Indexes on full_name and cached_at for fast lookups
//
// Default TTL: 7 days (GitHub metadata doesn't change rapidly)
func NewRepoCache(dbPath string) (*RepoCache, error) {
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open cache database: %w", err)
	}

	// Create cache table if it doesn't exist
	createTableSQL := `
	CREATE TABLE IF NOT EXISTS repo_cache (
		full_name TEXT PRIMARY KEY,
		stars INTEGER NOT NULL,
		last_update INTEGER NOT NULL, -- Unix timestamp
		has_ci INTEGER NOT NULL,       -- Boolean as INTEGER (0 or 1)
		has_docs INTEGER NOT NULL,     -- Boolean as INTEGER (0 or 1)
		has_docs_dir INTEGER NOT NULL, -- Boolean as INTEGER (0 or 1)
		score REAL NOT NULL,
		cached_at INTEGER NOT NULL,    -- Unix timestamp
		description TEXT,
		language TEXT
	);

	CREATE INDEX IF NOT EXISTS idx_repo_cache_cached_at ON repo_cache(cached_at);
	CREATE INDEX IF NOT EXISTS idx_repo_cache_score ON repo_cache(score DESC);
	`

	if _, err := db.Exec(createTableSQL); err != nil {
		db.Close()
		return nil, fmt.Errorf("failed to create cache table: %w", err)
	}

	return &RepoCache{db: db}, nil
}

// Get retrieves a cached repository entry by full name (e.g., "spf13/cobra").
// Returns nil if the entry doesn't exist or has expired based on TTL.
//
// TTL check: If cached_at + ttl < now, entry is considered expired and nil is returned.
func (c *RepoCache) Get(fullName string, ttl time.Duration) (*CachedRepo, error) {
	query := `
	SELECT full_name, stars, last_update, has_ci, has_docs, has_docs_dir,
	       score, cached_at, description, language
	FROM repo_cache
	WHERE full_name = ?
	`

	var repo CachedRepo
	var lastUpdateUnix, cachedAtUnix int64
	var hasCI, hasDocs, hasDocsDir int

	err := c.db.QueryRow(query, fullName).Scan(
		&repo.FullName,
		&repo.Stars,
		&lastUpdateUnix,
		&hasCI,
		&hasDocs,
		&hasDocsDir,
		&repo.Score,
		&cachedAtUnix,
		&repo.Description,
		&repo.Language,
	)

	if err == sql.ErrNoRows {
		return nil, nil // Cache miss
	}
	if err != nil {
		return nil, fmt.Errorf("failed to query cache: %w", err)
	}

	// Convert Unix timestamps back to time.Time
	repo.LastUpdate = time.Unix(lastUpdateUnix, 0)
	repo.CachedAt = time.Unix(cachedAtUnix, 0)
	repo.HasCI = hasCI == 1
	repo.HasDocs = hasDocs == 1
	repo.HasDocsDir = hasDocsDir == 1

	// Check TTL expiration
	expiresAt := repo.CachedAt.Add(ttl)
	if time.Now().After(expiresAt) {
		return nil, nil // Entry expired, treat as cache miss
	}

	return &repo, nil
}

// Set stores a repository in the cache with the specified TTL.
// If an entry already exists for this repository, it is replaced (upsert).
//
// The actual expiration is handled by Get() - we just store the cached_at timestamp.
func (c *RepoCache) Set(repo *CachedRepo) error {
	upsertSQL := `
	INSERT INTO repo_cache (
		full_name, stars, last_update, has_ci, has_docs, has_docs_dir,
		score, cached_at, description, language
	) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
	ON CONFLICT(full_name) DO UPDATE SET
		stars = excluded.stars,
		last_update = excluded.last_update,
		has_ci = excluded.has_ci,
		has_docs = excluded.has_docs,
		has_docs_dir = excluded.has_docs_dir,
		score = excluded.score,
		cached_at = excluded.cached_at,
		description = excluded.description,
		language = excluded.language
	`

	// Convert booleans to integers for SQLite
	hasCI := 0
	if repo.HasCI {
		hasCI = 1
	}
	hasDocs := 0
	if repo.HasDocs {
		hasDocs = 1
	}
	hasDocsDir := 0
	if repo.HasDocsDir {
		hasDocsDir = 1
	}

	_, err := c.db.Exec(
		upsertSQL,
		repo.FullName,
		repo.Stars,
		repo.LastUpdate.Unix(),
		hasCI,
		hasDocs,
		hasDocsDir,
		repo.Score,
		repo.CachedAt.Unix(),
		repo.Description,
		repo.Language,
	)

	if err != nil {
		return fmt.Errorf("failed to cache repository: %w", err)
	}

	return nil
}

// Invalidate removes a specific repository from the cache.
// This is useful when we want to force a refresh of a particular repo's data.
func (c *RepoCache) Invalidate(fullName string) error {
	deleteSQL := `DELETE FROM repo_cache WHERE full_name = ?`

	result, err := c.db.Exec(deleteSQL, fullName)
	if err != nil {
		return fmt.Errorf("failed to invalidate cache entry: %w", err)
	}

	rowsAffected, err := result.RowsAffected()
	if err != nil {
		return fmt.Errorf("failed to check deletion result: %w", err)
	}

	if rowsAffected == 0 {
		return fmt.Errorf("cache entry not found: %s", fullName)
	}

	return nil
}

// GetAll retrieves all cached repositories, ordered by score (highest first).
// This is useful for quickly getting top-ranked repos without re-querying GitHub.
//
// Optional TTL parameter: if provided, only non-expired entries are returned.
func (c *RepoCache) GetAll(ttl time.Duration) ([]*CachedRepo, error) {
	query := `
	SELECT full_name, stars, last_update, has_ci, has_docs, has_docs_dir,
	       score, cached_at, description, language
	FROM repo_cache
	ORDER BY score DESC
	`

	rows, err := c.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("failed to query all cached repos: %w", err)
	}
	defer rows.Close()

	var repos []*CachedRepo
	now := time.Now()

	for rows.Next() {
		var repo CachedRepo
		var lastUpdateUnix, cachedAtUnix int64
		var hasCI, hasDocs, hasDocsDir int

		err := rows.Scan(
			&repo.FullName,
			&repo.Stars,
			&lastUpdateUnix,
			&hasCI,
			&hasDocs,
			&hasDocsDir,
			&repo.Score,
			&cachedAtUnix,
			&repo.Description,
			&repo.Language,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan cached repo: %w", err)
		}

		// Convert Unix timestamps
		repo.LastUpdate = time.Unix(lastUpdateUnix, 0)
		repo.CachedAt = time.Unix(cachedAtUnix, 0)
		repo.HasCI = hasCI == 1
		repo.HasDocs = hasDocs == 1
		repo.HasDocsDir = hasDocsDir == 1

		// Check TTL expiration
		expiresAt := repo.CachedAt.Add(ttl)
		if now.After(expiresAt) {
			continue // Skip expired entries
		}

		repos = append(repos, &repo)
	}

	if err := rows.Err(); err != nil {
		return nil, fmt.Errorf("error iterating cached repos: %w", err)
	}

	return repos, nil
}

// Close closes the underlying SQLite database connection.
// This should be called when the cache is no longer needed.
func (c *RepoCache) Close() error {
	if c.db != nil {
		return c.db.Close()
	}
	return nil
}

// PurgeExpired removes all expired cache entries based on the provided TTL.
// This is useful for periodic cleanup to keep the database size manageable.
func (c *RepoCache) PurgeExpired(ttl time.Duration) (int64, error) {
	expirationThreshold := time.Now().Add(-ttl).Unix()

	deleteSQL := `DELETE FROM repo_cache WHERE cached_at < ?`

	result, err := c.db.Exec(deleteSQL, expirationThreshold)
	if err != nil {
		return 0, fmt.Errorf("failed to purge expired entries: %w", err)
	}

	rowsAffected, err := result.RowsAffected()
	if err != nil {
		return 0, fmt.Errorf("failed to check purge result: %w", err)
	}

	return rowsAffected, nil
}
