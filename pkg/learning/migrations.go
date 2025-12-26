// Package learning implements Ananta's self-healing pattern database and error classification
//
// Migrations: Schema versioning and evolution
// Author: Agent 0.3 (Dr. Amara Okafor)
// Created: 2025-11-07
package learning

import (
	"database/sql"
	"fmt"
)

// Migration represents a database schema migration
type Migration struct {
	Version     int    // Migration version number
	Name        string // Descriptive name
	Description string // What this migration does
	SQL         string // SQL to execute
}

// migrations is the ordered list of schema migrations
var migrations = []Migration{
	{
		Version:     1,
		Name:        "initial_schema",
		Description: "Create initial tables (repos, patterns, applications, learning_queue)",
		SQL: `
-- ANANTA SELF-HEALING PATTERN DATABASE SCHEMA
-- Version 1: Initial schema

-- Repos table
CREATE TABLE IF NOT EXISTS repos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    full_name TEXT UNIQUE NOT NULL,
    description TEXT,
    language TEXT NOT NULL,
    stars INTEGER NOT NULL,
    last_updated TEXT NOT NULL,
    ci_passing BOOLEAN DEFAULT 0,
    has_docs BOOLEAN DEFAULT 0,
    quality_score REAL DEFAULT 0.0,
    cloned_at TEXT,
    clone_path TEXT,
    created_at TEXT NOT NULL DEFAULT (datetime('now'))
);

-- Patterns table
CREATE TABLE IF NOT EXISTS patterns (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    error_signature TEXT NOT NULL,
    error_type TEXT NOT NULL,
    language TEXT NOT NULL,
    category TEXT NOT NULL,
    solution_code TEXT NOT NULL,
    solution_hash TEXT NOT NULL,
    confidence REAL NOT NULL DEFAULT 0.5,
    frequency INTEGER DEFAULT 1,
    last_applied TEXT,
    success_count INTEGER DEFAULT 0,
    failure_count INTEGER DEFAULT 0,
    repo_sources TEXT,
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    updated_at TEXT NOT NULL DEFAULT (datetime('now')),
    UNIQUE(error_signature, language)
);

-- Applications table
CREATE TABLE IF NOT EXISTS applications (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    pattern_id INTEGER NOT NULL,
    target_file TEXT NOT NULL,
    applied_at TEXT NOT NULL DEFAULT (datetime('now')),
    outcome TEXT NOT NULL,
    compilation_success BOOLEAN DEFAULT 0,
    test_pass BOOLEAN DEFAULT 0,
    quality_score REAL DEFAULT 0.0,
    feedback TEXT,
    FOREIGN KEY (pattern_id) REFERENCES patterns(id) ON DELETE CASCADE
);

-- Learning queue table
CREATE TABLE IF NOT EXISTS learning_queue (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    error_signature TEXT NOT NULL,
    error_message TEXT NOT NULL,
    error_type TEXT NOT NULL,
    language TEXT NOT NULL,
    file_path TEXT NOT NULL,
    line_number INTEGER,
    context TEXT,
    flagged_at TEXT NOT NULL DEFAULT (datetime('now')),
    resolution TEXT,
    resolved_at TEXT
);

-- Schema version table
CREATE TABLE IF NOT EXISTS schema_version (
    version INTEGER PRIMARY KEY,
    applied_at TEXT NOT NULL DEFAULT (datetime('now')),
    description TEXT
);

-- Indexes for repos
CREATE INDEX IF NOT EXISTS idx_repos_language ON repos(language);
CREATE INDEX IF NOT EXISTS idx_repos_quality ON repos(quality_score DESC, stars DESC);
CREATE INDEX IF NOT EXISTS idx_repos_updated ON repos(last_updated DESC);

-- Indexes for patterns
CREATE INDEX IF NOT EXISTS idx_patterns_signature_lang ON patterns(error_signature, language);
CREATE INDEX IF NOT EXISTS idx_patterns_confidence ON patterns(confidence DESC);
CREATE INDEX IF NOT EXISTS idx_patterns_category ON patterns(category, language);
CREATE INDEX IF NOT EXISTS idx_patterns_updated ON patterns(updated_at DESC);
CREATE INDEX IF NOT EXISTS idx_patterns_type ON patterns(error_type, language);

-- Indexes for applications
CREATE INDEX IF NOT EXISTS idx_applications_pattern ON applications(pattern_id, outcome);
CREATE INDEX IF NOT EXISTS idx_applications_outcome ON applications(outcome, compilation_success);
CREATE INDEX IF NOT EXISTS idx_applications_applied ON applications(applied_at DESC);

-- Indexes for learning queue
CREATE INDEX IF NOT EXISTS idx_learning_queue_signature ON learning_queue(error_signature);
CREATE INDEX IF NOT EXISTS idx_learning_queue_unresolved ON learning_queue(resolved_at) WHERE resolved_at IS NULL;
CREATE INDEX IF NOT EXISTS idx_learning_queue_lang ON learning_queue(language, error_type);

-- Statistics view
CREATE VIEW IF NOT EXISTS pattern_stats AS
SELECT
    p.id,
    p.error_signature,
    p.language,
    p.category,
    p.confidence,
    p.frequency,
    COUNT(a.id) AS total_applications,
    SUM(CASE WHEN a.outcome = 'success' THEN 1 ELSE 0 END) AS successful_applications,
    AVG(CASE WHEN a.outcome = 'success' THEN a.quality_score ELSE NULL END) AS avg_quality_score,
    MAX(a.applied_at) AS last_used
FROM patterns p
LEFT JOIN applications a ON p.id = a.pattern_id
GROUP BY p.id;
`,
	},
	// Future migrations go here:
	// {
	//     Version: 2,
	//     Name: "add_pattern_metadata",
	//     Description: "Add metadata fields to patterns table",
	//     SQL: "ALTER TABLE patterns ADD COLUMN metadata TEXT;",
	// },
}

// GetSchemaVersion retrieves the current schema version from database
func GetSchemaVersion(db *sql.DB) (int, error) {
	var version sql.NullInt64
	err := db.QueryRow("SELECT MAX(version) FROM schema_version").Scan(&version)
	if err != nil {
		if err == sql.ErrNoRows {
			return 0, nil // No migrations applied yet
		}
		return 0, fmt.Errorf("failed to get schema version: %w", err)
	}
	if !version.Valid {
		return 0, nil // Table exists but is empty
	}
	return int(version.Int64), nil
}

// SetSchemaVersion records a migration as applied
func SetSchemaVersion(db *sql.DB, version int, description string) error {
	_, err := db.Exec("INSERT INTO schema_version (version, description) VALUES (?, ?)", version, description)
	if err != nil {
		return fmt.Errorf("failed to set schema version: %w", err)
	}
	return nil
}

// ApplyMigrations applies all pending migrations
//
// This function is IDEMPOTENT - it checks which migrations have been applied
// and only runs the ones that haven't.
//
// Example:
//
//	db, _ := sql.Open("sqlite", "ananta_learning.db")
//	err := ApplyMigrations(db)
//	if err != nil {
//	    log.Fatal(err)
//	}
func ApplyMigrations(db *sql.DB) error {
	// Create schema_version table if it doesn't exist (bootstrap)
	_, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS schema_version (
			version INTEGER PRIMARY KEY,
			applied_at TEXT NOT NULL DEFAULT (datetime('now')),
			description TEXT
		)
	`)
	if err != nil {
		return fmt.Errorf("failed to create schema_version table: %w", err)
	}

	// Get current version
	currentVersion, err := GetSchemaVersion(db)
	if err != nil {
		return fmt.Errorf("failed to get current version: %w", err)
	}

	// Apply pending migrations
	for _, migration := range migrations {
		if migration.Version <= currentVersion {
			continue // Already applied
		}

		// Start transaction
		tx, err := db.Begin()
		if err != nil {
			return fmt.Errorf("failed to start transaction for migration %d: %w", migration.Version, err)
		}

		// Execute migration SQL
		_, err = tx.Exec(migration.SQL)
		if err != nil {
			tx.Rollback()
			return fmt.Errorf("migration %d (%s) failed: %w", migration.Version, migration.Name, err)
		}

		// Record migration
		_, err = tx.Exec("INSERT INTO schema_version (version, description) VALUES (?, ?)", migration.Version, migration.Description)
		if err != nil {
			tx.Rollback()
			return fmt.Errorf("failed to record migration %d: %w", migration.Version, err)
		}

		// Commit transaction
		if err := tx.Commit(); err != nil {
			return fmt.Errorf("failed to commit migration %d: %w", migration.Version, err)
		}

		fmt.Printf("Applied migration %d: %s\n", migration.Version, migration.Name)
	}

	return nil
}

// RollbackMigration rolls back a specific migration
// WARNING: This is destructive and should only be used in development
func RollbackMigration(db *sql.DB, version int) error {
	// SQLite doesn't support DROP IF EXISTS for views/indexes easily,
	// so rollback is manual for now.
	return fmt.Errorf("rollback not implemented - SQLite limitations")
}

// GetAppliedMigrations returns list of applied migrations
func GetAppliedMigrations(db *sql.DB) ([]Migration, error) {
	rows, err := db.Query("SELECT version, description, applied_at FROM schema_version ORDER BY version")
	if err != nil {
		return nil, fmt.Errorf("failed to get applied migrations: %w", err)
	}
	defer rows.Close()

	var applied []Migration
	for rows.Next() {
		var m Migration
		var appliedAt string
		if err := rows.Scan(&m.Version, &m.Description, &appliedAt); err != nil {
			return nil, fmt.Errorf("failed to scan migration: %w", err)
		}
		m.Name = appliedAt // Reuse Name field for applied_at timestamp
		applied = append(applied, m)
	}

	return applied, nil
}

// NeedsMigration checks if database needs migrations
func NeedsMigration(db *sql.DB) (bool, error) {
	currentVersion, err := GetSchemaVersion(db)
	if err != nil {
		return false, err
	}

	latestVersion := migrations[len(migrations)-1].Version
	return currentVersion < latestVersion, nil
}
