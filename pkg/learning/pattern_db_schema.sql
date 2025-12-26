-- ANANTA SELF-HEALING PATTERN DATABASE SCHEMA
-- ============================================
--
-- Purpose: Store learned error-fixing patterns from mature repos
-- Database: SQLite 3.x
-- Design: Optimized for fast pattern lookup using digital root classification
-- Author: Agent 0.3 (Dr. Amara Okafor) - Database Schema Architect
-- Created: 2025-11-07
--
-- VEDIC MATHEMATICS INTEGRATION:
-- - Error signatures use SHA256 → Digital Root for O(1) classification
-- - Indexes optimized for (signature, language) composite lookups
-- - Quality scores use harmonic mean (penalizes outliers)

-- =============================================================================
-- REPOS TABLE: Stores metadata about mature repositories we learn from
-- =============================================================================
CREATE TABLE IF NOT EXISTS repos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    full_name TEXT UNIQUE NOT NULL,           -- e.g., "spf13/cobra"
    description TEXT,                         -- Brief repo description
    language TEXT NOT NULL,                   -- Primary language (Go, Rust, etc.)
    stars INTEGER NOT NULL,                   -- GitHub stars (quality signal)
    last_updated TEXT NOT NULL,               -- ISO 8601 timestamp
    ci_passing BOOLEAN DEFAULT 0,             -- Is CI green?
    has_docs BOOLEAN DEFAULT 0,               -- Has README/docs?
    quality_score REAL DEFAULT 0.0,           -- Computed quality (0.0-1.0)
    cloned_at TEXT,                           -- When we cloned it
    clone_path TEXT,                          -- Local filesystem path
    created_at TEXT NOT NULL DEFAULT (datetime('now'))
);

-- Index for language-based queries
CREATE INDEX IF NOT EXISTS idx_repos_language ON repos(language);

-- Index for quality-based selection
CREATE INDEX IF NOT EXISTS idx_repos_quality ON repos(quality_score DESC, stars DESC);

-- Index for freshness checks
CREATE INDEX IF NOT EXISTS idx_repos_updated ON repos(last_updated DESC);

-- =============================================================================
-- PATTERNS TABLE: Stores learned error-fixing patterns
-- =============================================================================
CREATE TABLE IF NOT EXISTS patterns (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    error_signature TEXT NOT NULL,            -- SHA256 → Digital Root format "3:a1b2c3d4"
    error_type TEXT NOT NULL,                 -- compile, runtime, test, lint
    language TEXT NOT NULL,                   -- Go, Rust, Python, etc.
    category TEXT NOT NULL,                   -- error_handling, crud, testing, etc.
    solution_code TEXT NOT NULL,              -- The actual fix/pattern code
    solution_hash TEXT NOT NULL,              -- Hash of solution (for grouping similar fixes)
    confidence REAL NOT NULL DEFAULT 0.5,     -- 0.0-1.0 (updated via feedback)
    frequency INTEGER DEFAULT 1,              -- How many repos use this pattern
    last_applied TEXT,                        -- ISO 8601 of last successful application
    success_count INTEGER DEFAULT 0,          -- Number of successful applications
    failure_count INTEGER DEFAULT 0,          -- Number of failed applications
    repo_sources TEXT,                        -- JSON array of repo IDs that provided this pattern
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    updated_at TEXT NOT NULL DEFAULT (datetime('now')),
    UNIQUE(error_signature, language)         -- One pattern per (signature, language) pair
);

-- PRIMARY INDEX: Fast lookup by signature + language
-- This is the hot path for pattern matching
CREATE INDEX IF NOT EXISTS idx_patterns_signature_lang ON patterns(error_signature, language);

-- Index for confidence-based filtering (show best patterns first)
CREATE INDEX IF NOT EXISTS idx_patterns_confidence ON patterns(confidence DESC);

-- Index for category-based exploration
CREATE INDEX IF NOT EXISTS idx_patterns_category ON patterns(category, language);

-- Index for temporal queries (what patterns are being learned recently?)
CREATE INDEX IF NOT EXISTS idx_patterns_updated ON patterns(updated_at DESC);

-- Index for type-based filtering (compile errors vs runtime errors)
CREATE INDEX IF NOT EXISTS idx_patterns_type ON patterns(error_type, language);

-- =============================================================================
-- APPLICATIONS TABLE: Tracks pattern application outcomes
-- =============================================================================
CREATE TABLE IF NOT EXISTS applications (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    pattern_id INTEGER NOT NULL,              -- Foreign key to patterns table
    target_file TEXT NOT NULL,                -- File where pattern was applied
    applied_at TEXT NOT NULL DEFAULT (datetime('now')),
    outcome TEXT NOT NULL,                    -- success, failure, rejected
    compilation_success BOOLEAN DEFAULT 0,    -- Did code compile after?
    test_pass BOOLEAN DEFAULT 0,              -- Did tests pass after?
    quality_score REAL DEFAULT 0.0,           -- Harmonic mean quality (Five Timbres)
    feedback TEXT,                            -- Human or automated feedback
    FOREIGN KEY (pattern_id) REFERENCES patterns(id) ON DELETE CASCADE
);

-- Index for pattern-based queries (what outcomes did this pattern have?)
CREATE INDEX IF NOT EXISTS idx_applications_pattern ON applications(pattern_id, outcome);

-- Index for outcome analysis
CREATE INDEX IF NOT EXISTS idx_applications_outcome ON applications(outcome, compilation_success);

-- Index for temporal analysis (recent applications)
CREATE INDEX IF NOT EXISTS idx_applications_applied ON applications(applied_at DESC);

-- =============================================================================
-- LEARNING_QUEUE TABLE: Errors without matches, flagged for learning
-- =============================================================================
CREATE TABLE IF NOT EXISTS learning_queue (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    error_signature TEXT NOT NULL,            -- SHA256 → Digital Root format
    error_message TEXT NOT NULL,              -- Full error text (normalized)
    error_type TEXT NOT NULL,                 -- compile, runtime, test, lint
    language TEXT NOT NULL,                   -- Language where error occurred
    file_path TEXT NOT NULL,                  -- File with the error
    line_number INTEGER,                      -- Line number (if available)
    context TEXT,                             -- Surrounding code (±5 lines)
    flagged_at TEXT NOT NULL DEFAULT (datetime('now')),
    resolution TEXT,                          -- Once learned, store solution
    resolved_at TEXT                          -- When resolved
);

-- Index for signature-based deduplication
CREATE INDEX IF NOT EXISTS idx_learning_queue_signature ON learning_queue(error_signature);

-- Index for unresolved items (the work queue)
CREATE INDEX IF NOT EXISTS idx_learning_queue_unresolved ON learning_queue(resolved_at) WHERE resolved_at IS NULL;

-- Index for language-based filtering
CREATE INDEX IF NOT EXISTS idx_learning_queue_lang ON learning_queue(language, error_type);

-- =============================================================================
-- SCHEMA VERSION TABLE: Track migrations
-- =============================================================================
CREATE TABLE IF NOT EXISTS schema_version (
    version INTEGER PRIMARY KEY,
    applied_at TEXT NOT NULL DEFAULT (datetime('now')),
    description TEXT
);

-- Insert initial version
INSERT OR IGNORE INTO schema_version (version, description) VALUES (1, 'Initial schema with repos, patterns, applications, learning_queue');

-- =============================================================================
-- STATISTICS VIEW: Aggregated pattern performance metrics
-- =============================================================================
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

-- =============================================================================
-- END OF SCHEMA
-- =============================================================================
--
-- TOTAL TABLES: 4 (repos, patterns, applications, learning_queue)
-- TOTAL INDEXES: 14 (optimized for read-heavy pattern matching workload)
-- TOTAL VIEWS: 1 (pattern_stats for analytics)
--
-- VEDIC OPTIMIZATION:
-- - Digital root signatures enable O(1) classification into 9 buckets
-- - Composite indexes (signature, language) for fast exact matches
-- - Harmonic mean quality scores penalize outliers (Five Timbres)
--
-- QUERY PERFORMANCE:
-- - Pattern lookup by signature + language: O(log n) via index
-- - Digital root bucketing: O(1) classification → O(log n/9) search
-- - Confidence filtering: O(log n) via confidence index
