// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Database: SQLite operations for pattern storage and retrieval
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"database/sql"
	"encoding/json"
	"fmt"
	"time"

	_ "modernc.org/sqlite" // SQLite driver
)

// PatternDB wraps SQLite database connection for pattern operations
type PatternDB struct {
	db *sql.DB
}

// Repo represents a mature repository we learn patterns from
type Repo struct {
	ID           int64     `json:"id"`
	FullName     string    `json:"full_name"`     // e.g., "spf13/cobra"
	Description  string    `json:"description"`   // Brief description
	Language     string    `json:"language"`      // Primary language
	Stars        int       `json:"stars"`         // GitHub stars
	LastUpdated  time.Time `json:"last_updated"`  // Last commit/update
	CIPassing    bool      `json:"ci_passing"`    // Is CI green?
	HasDocs      bool      `json:"has_docs"`      // Has documentation?
	QualityScore float64   `json:"quality_score"` // Computed quality (0.0-1.0)
	ClonedAt     time.Time `json:"cloned_at"`     // When we cloned it
	ClonePath    string    `json:"clone_path"`    // Local filesystem path
	CreatedAt    time.Time `json:"created_at"`    // When added to DB
}

// Pattern represents a learned error-fixing pattern
type Pattern struct {
	ID            int64     `json:"id"`
	ErrorSig      string    `json:"error_signature"`  // "3:a1b2c3d4" format
	ErrorType     string    `json:"error_type"`       // compile, runtime, test, lint
	Language      string    `json:"language"`         // Go, Rust, etc.
	Category      string    `json:"category"`         // error_handling, crud, etc.
	SolutionCode  string    `json:"solution_code"`    // The fix
	SolutionHash  string    `json:"solution_hash"`    // Hash for grouping
	Confidence    float64   `json:"confidence"`       // 0.0-1.0
	Frequency     int       `json:"frequency"`        // Usage count
	LastApplied   time.Time `json:"last_applied"`     // Last use
	SuccessCount  int       `json:"success_count"`    // Successful applications
	FailureCount  int       `json:"failure_count"`    // Failed applications
	RepoSources   []int64   `json:"repo_sources"`     // Repo IDs (JSON array)
	CreatedAt     time.Time `json:"created_at"`
	UpdatedAt     time.Time `json:"updated_at"`
}

// Application tracks pattern application outcomes
type Application struct {
	ID                 int64     `json:"id"`
	PatternID          int64     `json:"pattern_id"`
	TargetFile         string    `json:"target_file"`
	AppliedAt          time.Time `json:"applied_at"`
	Outcome            string    `json:"outcome"`            // success, failure, rejected
	CompilationSuccess bool      `json:"compilation_success"`
	TestPass           bool      `json:"test_pass"`
	QualityScore       float64   `json:"quality_score"` // Harmonic mean (Five Timbres)
	Feedback           string    `json:"feedback"`      // Human or automated feedback
}

// LearningQueueEntry represents an error without a matching pattern
type LearningQueueEntry struct {
	ID            int64     `json:"id"`
	ErrorSig      string    `json:"error_signature"` // "3:a1b2c3d4"
	ErrorMessage  string    `json:"error_message"`   // Normalized error text
	ErrorType     string    `json:"error_type"`      // compile, runtime, test, lint
	Language      string    `json:"language"`
	FilePath      string    `json:"file_path"`
	LineNumber    int       `json:"line_number"`
	Context       string    `json:"context"`      // Surrounding code
	FlaggedAt     time.Time `json:"flagged_at"`
	Resolution    string    `json:"resolution"`   // Solution once learned
	ResolvedAt    time.Time `json:"resolved_at"`
}

// OpenDB opens or creates SQLite database at given path
//
// Example:
//
//	db, err := OpenDB("ananta_learning.db")
//	if err != nil {
//	    log.Fatal(err)
//	}
//	defer db.Close()
func OpenDB(dbPath string) (*PatternDB, error) {
	db, err := sql.Open("sqlite", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open database: %w", err)
	}

	// Test connection
	if err := db.Ping(); err != nil {
		return nil, fmt.Errorf("failed to connect to database: %w", err)
	}

	return &PatternDB{db: db}, nil
}

// RawDB returns the underlying sql.DB for migrations
// Use this carefully - prefer using PatternDB methods when possible
func (p *PatternDB) RawDB() *sql.DB {
	return p.db
}

// Close closes the database connection
func (p *PatternDB) Close() error {
	return p.db.Close()
}

// Migrate runs database migrations (schema creation)
//
// This function is IDEMPOTENT - safe to call multiple times.
// It reads the schema from pattern_db_schema.sql and applies it.
func (p *PatternDB) Migrate(schemaSQL string) error {
	_, err := p.db.Exec(schemaSQL)
	if err != nil {
		return fmt.Errorf("migration failed: %w", err)
	}
	return nil
}

// AddRepo inserts or updates a repository record
func (p *PatternDB) AddRepo(repo *Repo) error {
	query := `
		INSERT INTO repos (full_name, description, language, stars, last_updated, ci_passing, has_docs, quality_score, cloned_at, clone_path)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(full_name) DO UPDATE SET
			description = excluded.description,
			stars = excluded.stars,
			last_updated = excluded.last_updated,
			ci_passing = excluded.ci_passing,
			has_docs = excluded.has_docs,
			quality_score = excluded.quality_score,
			cloned_at = excluded.cloned_at,
			clone_path = excluded.clone_path
	`

	result, err := p.db.Exec(query,
		repo.FullName,
		repo.Description,
		repo.Language,
		repo.Stars,
		repo.LastUpdated.Format(time.RFC3339),
		repo.CIPassing,
		repo.HasDocs,
		repo.QualityScore,
		repo.ClonedAt.Format(time.RFC3339),
		repo.ClonePath,
	)
	if err != nil {
		return fmt.Errorf("failed to add repo: %w", err)
	}

	id, err := result.LastInsertId()
	if err == nil {
		repo.ID = id
	}

	return nil
}

// GetRepo retrieves a repository by full name
func (p *PatternDB) GetRepo(fullName string) (*Repo, error) {
	query := `SELECT id, full_name, description, language, stars, last_updated, ci_passing, has_docs, quality_score, cloned_at, clone_path, created_at FROM repos WHERE full_name = ?`

	var repo Repo
	var lastUpdated, clonedAt, createdAt string

	err := p.db.QueryRow(query, fullName).Scan(
		&repo.ID,
		&repo.FullName,
		&repo.Description,
		&repo.Language,
		&repo.Stars,
		&lastUpdated,
		&repo.CIPassing,
		&repo.HasDocs,
		&repo.QualityScore,
		&clonedAt,
		&repo.ClonePath,
		&createdAt,
	)
	if err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("repo not found: %s", fullName)
		}
		return nil, fmt.Errorf("failed to get repo: %w", err)
	}

	// Parse timestamps
	repo.LastUpdated, _ = time.Parse(time.RFC3339, lastUpdated)
	repo.ClonedAt, _ = time.Parse(time.RFC3339, clonedAt)
	repo.CreatedAt, _ = time.Parse(time.RFC3339, createdAt)

	return &repo, nil
}

// AddPattern inserts or updates a pattern
func (p *PatternDB) AddPattern(pattern *Pattern) error {
	// Marshal repo sources to JSON
	repoSourcesJSON, err := json.Marshal(pattern.RepoSources)
	if err != nil {
		return fmt.Errorf("failed to marshal repo sources: %w", err)
	}

	query := `
		INSERT INTO patterns (error_signature, error_type, language, category, solution_code, solution_hash, confidence, frequency, repo_sources)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(error_signature, language) DO UPDATE SET
			solution_code = excluded.solution_code,
			confidence = excluded.confidence,
			frequency = frequency + 1,
			updated_at = datetime('now')
	`

	result, err := p.db.Exec(query,
		pattern.ErrorSig,
		pattern.ErrorType,
		pattern.Language,
		pattern.Category,
		pattern.SolutionCode,
		pattern.SolutionHash,
		pattern.Confidence,
		pattern.Frequency,
		string(repoSourcesJSON),
	)
	if err != nil {
		return fmt.Errorf("failed to add pattern: %w", err)
	}

	id, err := result.LastInsertId()
	if err == nil {
		pattern.ID = id
	}

	return nil
}

// FindPatterns searches for patterns matching signature and language
//
// Args:
//   - signature: Error signature ("3:a1b2c3d4")
//   - language: Programming language ("Go", "Rust", etc.)
//   - minConfidence: Minimum confidence threshold (0.0-1.0)
//
// Returns patterns sorted by confidence DESC.
//
// Enhanced: Now supports fuzzy matching if exact match fails.
func (p *PatternDB) FindPatterns(signature, language string, minConfidence float64) ([]*Pattern, error) {
	// Try exact match first
	patterns, err := p.findPatternsExact(signature, language, minConfidence)
	if err != nil {
		return nil, err
	}

	// If exact match succeeded, return
	if len(patterns) > 0 {
		return patterns, nil
	}

	// Fall back to fuzzy matching
	return p.findPatternsFuzzy(signature, language, minConfidence)
}

// findPatternsExact performs exact signature matching
func (p *PatternDB) findPatternsExact(signature, language string, minConfidence float64) ([]*Pattern, error) {
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		WHERE error_signature = ? AND language = ? AND confidence >= ?
		ORDER BY confidence DESC, frequency DESC
	`

	return p.scanPatterns(query, signature, language, minConfidence)
}

// findPatternsFuzzy performs fuzzy signature matching
//
// Strategy:
//   1. Match by category (error class similarity)
//   2. Match by digital root (signature hash modulo 9)
//   3. Match by language only (broadest fallback)
func (p *PatternDB) findPatternsFuzzy(signature, language string, minConfidence float64) ([]*Pattern, error) {
	// Try category-based matching first
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		WHERE language = ? AND confidence >= ?
		ORDER BY confidence DESC, frequency DESC
		LIMIT 20
	`

	return p.scanPatterns(query, language, minConfidence*0.8) // Relax confidence by 20%
}

// scanPatterns is a helper to scan query results into Pattern slice
func (p *PatternDB) scanPatterns(query string, args ...interface{}) ([]*Pattern, error) {
	rows, err := p.db.Query(query, args...)
	if err != nil {
		return nil, fmt.Errorf("failed to query patterns: %w", err)
	}
	defer rows.Close()

	var patterns []*Pattern
	for rows.Next() {
		var pat Pattern
		var lastApplied, createdAt, updatedAt sql.NullString
		var repoSourcesJSON string

		err := rows.Scan(
			&pat.ID,
			&pat.ErrorSig,
			&pat.ErrorType,
			&pat.Language,
			&pat.Category,
			&pat.SolutionCode,
			&pat.SolutionHash,
			&pat.Confidence,
			&pat.Frequency,
			&lastApplied,
			&pat.SuccessCount,
			&pat.FailureCount,
			&repoSourcesJSON,
			&createdAt,
			&updatedAt,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan pattern: %w", err)
		}

		// Parse timestamps
		if lastApplied.Valid {
			pat.LastApplied, _ = time.Parse(time.RFC3339, lastApplied.String)
		}
		if createdAt.Valid {
			pat.CreatedAt, _ = time.Parse(time.RFC3339, createdAt.String)
		}
		if updatedAt.Valid {
			pat.UpdatedAt, _ = time.Parse(time.RFC3339, updatedAt.String)
		}

		// Parse repo sources
		if err := json.Unmarshal([]byte(repoSourcesJSON), &pat.RepoSources); err != nil {
			pat.RepoSources = []int64{} // Default to empty on parse error
		}

		patterns = append(patterns, &pat)
	}

	return patterns, nil
}

// GetPatternByID retrieves a pattern by its ID
func (p *PatternDB) GetPatternByID(id int64) (*Pattern, error) {
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		WHERE id = ?
	`

	var pattern Pattern
	var lastApplied, createdAt, updatedAt sql.NullString
	var repoSourcesJSON string

	err := p.db.QueryRow(query, id).Scan(
		&pattern.ID,
		&pattern.ErrorSig,
		&pattern.ErrorType,
		&pattern.Language,
		&pattern.Category,
		&pattern.SolutionCode,
		&pattern.SolutionHash,
		&pattern.Confidence,
		&pattern.Frequency,
		&lastApplied,
		&pattern.SuccessCount,
		&pattern.FailureCount,
		&repoSourcesJSON,
		&createdAt,
		&updatedAt,
	)
	if err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("pattern not found: %d", id)
		}
		return nil, fmt.Errorf("failed to get pattern: %w", err)
	}

	// Parse timestamps
	if lastApplied.Valid {
		pattern.LastApplied, _ = time.Parse(time.RFC3339, lastApplied.String)
	}
	if createdAt.Valid {
		pattern.CreatedAt, _ = time.Parse(time.RFC3339, createdAt.String)
	}
	if updatedAt.Valid {
		pattern.UpdatedAt, _ = time.Parse(time.RFC3339, updatedAt.String)
	}

	// Parse repo sources
	if err := json.Unmarshal([]byte(repoSourcesJSON), &pattern.RepoSources); err != nil {
		pattern.RepoSources = []int64{}
	}

	return &pattern, nil
}

// UpdatePattern updates an existing pattern
func (p *PatternDB) UpdatePattern(pattern *Pattern) error {
	repoSourcesJSON, err := json.Marshal(pattern.RepoSources)
	if err != nil {
		return fmt.Errorf("failed to marshal repo sources: %w", err)
	}

	query := `
		UPDATE patterns SET
			error_signature = ?,
			error_type = ?,
			language = ?,
			category = ?,
			solution_code = ?,
			solution_hash = ?,
			confidence = ?,
			frequency = ?,
			success_count = ?,
			failure_count = ?,
			repo_sources = ?,
			updated_at = datetime('now')
		WHERE id = ?
	`

	_, err = p.db.Exec(query,
		pattern.ErrorSig,
		pattern.ErrorType,
		pattern.Language,
		pattern.Category,
		pattern.SolutionCode,
		pattern.SolutionHash,
		pattern.Confidence,
		pattern.Frequency,
		pattern.SuccessCount,
		pattern.FailureCount,
		string(repoSourcesJSON),
		pattern.ID,
	)
	if err != nil {
		return fmt.Errorf("failed to update pattern: %w", err)
	}

	return nil
}

// UpdatePatternConfidence updates the confidence score for a pattern
func (p *PatternDB) UpdatePatternConfidence(id int64, newConfidence float64) error {
	query := `UPDATE patterns SET confidence = ?, updated_at = datetime('now') WHERE id = ?`
	_, err := p.db.Exec(query, newConfidence, id)
	if err != nil {
		return fmt.Errorf("failed to update confidence: %w", err)
	}
	return nil
}

// AddToLearningQueue adds an error without a match to the learning queue
func (p *PatternDB) AddToLearningQueue(entry *LearningQueueEntry) error {
	query := `
		INSERT INTO learning_queue (error_signature, error_message, error_type, language, file_path, line_number, context)
		VALUES (?, ?, ?, ?, ?, ?, ?)
	`

	result, err := p.db.Exec(query,
		entry.ErrorSig,
		entry.ErrorMessage,
		entry.ErrorType,
		entry.Language,
		entry.FilePath,
		entry.LineNumber,
		entry.Context,
	)
	if err != nil {
		return fmt.Errorf("failed to add to learning queue: %w", err)
	}

	id, err := result.LastInsertId()
	if err == nil {
		entry.ID = id
	}

	return nil
}

// RecordApplication records the outcome of applying a pattern
func (p *PatternDB) RecordApplication(app *Application) error {
	query := `
		INSERT INTO applications (pattern_id, target_file, outcome, compilation_success, test_pass, quality_score, feedback)
		VALUES (?, ?, ?, ?, ?, ?, ?)
	`

	result, err := p.db.Exec(query,
		app.PatternID,
		app.TargetFile,
		app.Outcome,
		app.CompilationSuccess,
		app.TestPass,
		app.QualityScore,
		app.Feedback,
	)
	if err != nil {
		return fmt.Errorf("failed to record application: %w", err)
	}

	id, err := result.LastInsertId()
	if err == nil {
		app.ID = id
	}

	// Update pattern success/failure counts
	if app.Outcome == "success" {
		p.db.Exec(`UPDATE patterns SET success_count = success_count + 1, last_applied = datetime('now') WHERE id = ?`, app.PatternID)
	} else if app.Outcome == "failure" {
		p.db.Exec(`UPDATE patterns SET failure_count = failure_count + 1 WHERE id = ?`, app.PatternID)
	}

	return nil
}

// GetPatternStats retrieves aggregated statistics for a pattern
func (p *PatternDB) GetPatternStats(patternID int64) (map[string]interface{}, error) {
	query := `SELECT * FROM pattern_stats WHERE id = ?`

	var stats map[string]interface{}
	row := p.db.QueryRow(query, patternID)

	var id int64
	var errorSig, language, category string
	var confidence float64
	var frequency, totalApps, successApps int
	var avgQuality sql.NullFloat64
	var lastUsed sql.NullString

	err := row.Scan(&id, &errorSig, &language, &category, &confidence, &frequency, &totalApps, &successApps, &avgQuality, &lastUsed)
	if err != nil {
		return nil, fmt.Errorf("failed to get pattern stats: %w", err)
	}

	stats = map[string]interface{}{
		"id":                     id,
		"error_signature":        errorSig,
		"language":               language,
		"category":               category,
		"confidence":             confidence,
		"frequency":              frequency,
		"total_applications":     totalApps,
		"successful_applications": successApps,
		"avg_quality_score":      avgQuality.Float64,
		"last_used":              lastUsed.String,
	}

	return stats, nil
}

// LoadAll loads all patterns from the database
//
// Returns all patterns sorted by confidence DESC, frequency DESC.
// Use this for batch operations like enhancement and merging.
func (p *PatternDB) LoadAll() ([]*Pattern, error) {
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		ORDER BY confidence DESC, frequency DESC
	`

	rows, err := p.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("failed to load all patterns: %w", err)
	}
	defer rows.Close()

	var patterns []*Pattern
	for rows.Next() {
		var p Pattern
		var lastApplied, createdAt, updatedAt sql.NullString
		var repoSourcesJSON string

		err := rows.Scan(
			&p.ID,
			&p.ErrorSig,
			&p.ErrorType,
			&p.Language,
			&p.Category,
			&p.SolutionCode,
			&p.SolutionHash,
			&p.Confidence,
			&p.Frequency,
			&lastApplied,
			&p.SuccessCount,
			&p.FailureCount,
			&repoSourcesJSON,
			&createdAt,
			&updatedAt,
		)
		if err != nil {
			return nil, fmt.Errorf("failed to scan pattern: %w", err)
		}

		// Parse timestamps
		if lastApplied.Valid {
			p.LastApplied, _ = time.Parse(time.RFC3339, lastApplied.String)
		}
		if createdAt.Valid {
			p.CreatedAt, _ = time.Parse(time.RFC3339, createdAt.String)
		}
		if updatedAt.Valid {
			p.UpdatedAt, _ = time.Parse(time.RFC3339, updatedAt.String)
		}

		// Parse repo sources
		if err := json.Unmarshal([]byte(repoSourcesJSON), &p.RepoSources); err != nil {
			p.RepoSources = []int64{} // Default to empty on parse error
		}

		patterns = append(patterns, &p)
	}

	if err := rows.Err(); err != nil {
		return nil, fmt.Errorf("error iterating patterns: %w", err)
	}

	return patterns, nil
}
