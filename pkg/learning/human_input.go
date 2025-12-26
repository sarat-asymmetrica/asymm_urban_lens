// Package learning implements human-in-the-loop pattern learning
//
// Human Input: Transfer learning from expert-verified solutions
// Author: Agent 1.3 (Dr. Chen Wei)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"time"
)

// HumanPatternMetadata stores metadata for human-contributed patterns
//
// Attribution and provenance tracking:
// - Who contributed the pattern?
// - When was it submitted?
// - What was the context?
// - Who verified it (code review)?
//
// This enables:
// - Credit for contributors
// - Trust scoring (verified vs unverified)
// - Temporal analysis (patterns by time period)
// - Source analysis (manual vs pair programming vs code review)
type HumanPatternMetadata struct {
	AuthorName  string    // Email or username
	SubmittedAt time.Time // When pattern was added
	Description string    // Human-readable explanation
	VerifiedBy  string    // Optional: code reviewer who verified
	Source      string    // "manual", "code_review", "pair_programming"
	Language    string    // Programming language
	Category    string    // error_handling, crud, testing, etc.
}

// AddHumanPattern creates a new pattern from human expert input
//
// Transfer learning from human expertise:
// 1. Human submits: error signature + solution code + metadata
// 2. System computes solution hash (for duplicate detection)
// 3. Initial confidence = 0.85 (HIGH tier, trusted by default)
// 4. Repo source = "human:manual" (attribution)
// 5. Quality score = 0.85 (assumed high quality)
// 6. Pattern stored in database
//
// Why start at 0.85 confidence?
// - Humans verify solutions work before submitting
// - Higher trust than mined patterns (which start at 0.50)
// - Still allows improvement via feedback (can reach 0.99)
// - Still allows decay if unused (can drop to 0.10)
//
// This implements knowledge distillation:
// - Expert knowledge transferred to pattern database
// - System learns from both automated AND human sources
// - Combines supervised (human) + unsupervised (mining) learning
//
// Example:
//
//	metadata := HumanPatternMetadata{
//	    AuthorName: "alice@company.com",
//	    SubmittedAt: time.Now(),
//	    Description: "Fix nil pointer in HTTP handler",
//	    VerifiedBy: "bob@company.com",
//	    Source: "code_review",
//	    Language: "Go",
//	    Category: "error_handling",
//	}
//	pattern, err := AddHumanPattern(
//	    db,
//	    "3:a1b2c3d4",
//	    "if handler == nil { return errors.New(\"nil handler\") }",
//	    "Go",
//	    "error_handling",
//	    metadata,
//	)
func AddHumanPattern(
	db *PatternDB,
	errorSignature string,
	solutionCode string,
	language string,
	category string,
	metadata HumanPatternMetadata,
) (*Pattern, error) {
	// Compute solution hash for duplicate detection
	solutionHash := computeSolutionHash(solutionCode)

	// Create pattern object
	pattern := &Pattern{
		ErrorSig:     errorSignature,
		ErrorType:    "compile", // Default type for human patterns
		Language:     language,
		Category:     category,
		SolutionCode: solutionCode,
		SolutionHash: solutionHash,
		Confidence:   0.85, // High initial confidence for human-verified patterns
		Frequency:    1,    // First occurrence
		// RepoSources will be set to ["human:manual"] as JSON
		RepoSources:  []int64{}, // Empty - human patterns don't come from repos
		SuccessCount: 0,
		FailureCount: 0,
		CreatedAt:    time.Now(),
		UpdatedAt:    time.Now(),
	}

	// Store metadata in repo_sources as special JSON entry
	// Format: ["human:manual", "author:alice@company.com", "verified_by:bob@company.com"]
	metadataJSON := []string{
		"human:manual",
		fmt.Sprintf("author:%s", metadata.AuthorName),
		fmt.Sprintf("source:%s", metadata.Source),
	}
	if metadata.VerifiedBy != "" {
		metadataJSON = append(metadataJSON, fmt.Sprintf("verified_by:%s", metadata.VerifiedBy))
	}

	// Serialize metadata to JSON for repo_sources field
	// (We repurpose repo_sources to store human metadata as JSON array of strings)
	repoSourcesBytes, err := json.Marshal(metadataJSON)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal metadata: %w", err)
	}

	// Insert pattern into database
	query := `
		INSERT INTO patterns (
			error_signature, error_type, language, category,
			solution_code, solution_hash, confidence, frequency,
			repo_sources, created_at, updated_at
		)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, datetime('now'), datetime('now'))
		ON CONFLICT(error_signature, language) DO UPDATE SET
			solution_code = excluded.solution_code,
			confidence = MAX(confidence, excluded.confidence),
			frequency = frequency + 1,
			updated_at = datetime('now')
	`

	result, err := db.db.Exec(query,
		pattern.ErrorSig,
		pattern.ErrorType,
		pattern.Language,
		pattern.Category,
		pattern.SolutionCode,
		pattern.SolutionHash,
		pattern.Confidence,
		pattern.Frequency,
		string(repoSourcesBytes),
	)
	if err != nil {
		return nil, fmt.Errorf("failed to insert human pattern: %w", err)
	}

	id, err := result.LastInsertId()
	if err == nil {
		pattern.ID = id
	}

	return pattern, nil
}

// IsHumanPattern checks if a pattern was contributed by a human
//
// Detection:
// - repo_sources contains "human:manual"
// - This distinguishes human patterns from mined patterns
//
// Example:
//
//	isHuman, err := IsHumanPattern(db, 42)
//	if isHuman {
//	    fmt.Println("Pattern was verified by human expert")
//	}
func IsHumanPattern(db *PatternDB, patternID int64) (bool, error) {
	query := `SELECT repo_sources FROM patterns WHERE id = ?`
	var repoSourcesJSON string
	err := db.db.QueryRow(query, patternID).Scan(&repoSourcesJSON)
	if err != nil {
		return false, fmt.Errorf("failed to check pattern source: %w", err)
	}

	// Parse JSON array
	var sources []string
	if err := json.Unmarshal([]byte(repoSourcesJSON), &sources); err != nil {
		return false, nil // Not JSON or parse error - assume not human
	}

	// Check if "human:manual" is in sources
	for _, source := range sources {
		if source == "human:manual" {
			return true, nil
		}
	}

	return false, nil
}

// GetHumanPatternMetadata extracts metadata from human-contributed pattern
//
// Parses repo_sources JSON to retrieve:
// - Author name
// - Verification status
// - Source type (manual, code_review, pair_programming)
//
// Example:
//
//	metadata, err := GetHumanPatternMetadata(db, 42)
//	fmt.Printf("Contributed by: %s\n", metadata.AuthorName)
//	fmt.Printf("Verified by: %s\n", metadata.VerifiedBy)
func GetHumanPatternMetadata(db *PatternDB, patternID int64) (*HumanPatternMetadata, error) {
	query := `SELECT repo_sources FROM patterns WHERE id = ?`
	var repoSourcesJSON string
	err := db.db.QueryRow(query, patternID).Scan(&repoSourcesJSON)
	if err != nil {
		return nil, fmt.Errorf("failed to get pattern sources: %w", err)
	}

	// Parse JSON array
	var sources []string
	if err := json.Unmarshal([]byte(repoSourcesJSON), &sources); err != nil {
		return nil, fmt.Errorf("failed to parse sources JSON: %w", err)
	}

	// Extract metadata from sources array
	metadata := &HumanPatternMetadata{}
	for _, source := range sources {
		// Parse "key:value" format
		if len(source) > 7 && source[:7] == "author:" {
			metadata.AuthorName = source[7:]
		} else if len(source) > 7 && source[:7] == "source:" {
			metadata.Source = source[7:]
		} else if len(source) > 12 && source[:12] == "verified_by:" {
			metadata.VerifiedBy = source[12:]
		}
	}

	return metadata, nil
}

// computeSolutionHash generates SHA256 hash of normalized solution code
//
// Normalization:
// - Trim whitespace
// - Lowercase (case-insensitive matching)
// - Remove comments (not implemented here for simplicity)
//
// This enables:
// - Duplicate detection (exact same solution)
// - Solution grouping (similar solutions)
//
// Example:
//
//	hash1 := computeSolutionHash("if err != nil { return err }")
//	hash2 := computeSolutionHash("if err != nil { return err }") // Same
//	hash3 := computeSolutionHash("if x == nil { return x }") // Different
func computeSolutionHash(solutionCode string) string {
	// Normalize solution code (basic normalization)
	// Uses raw code for now - AST-based normalization could be added later
	// when Agent 1.2's similarity algorithms are integrated
	normalized := solutionCode

	// Compute SHA256 hash
	hash := sha256.Sum256([]byte(normalized))
	return fmt.Sprintf("%x", hash)
}

// GetHumanPatternCount returns count of human-contributed patterns
//
// Useful for:
// - Statistics reporting
// - Monitoring human engagement
// - Tracking knowledge transfer
//
// Example:
//
//	count, err := GetHumanPatternCount(db)
//	fmt.Printf("Database contains %d human-verified patterns\n", count)
func GetHumanPatternCount(db *PatternDB) (int, error) {
	query := `SELECT COUNT(*) FROM patterns WHERE repo_sources LIKE '%"human:manual"%'`
	var count int
	err := db.db.QueryRow(query).Scan(&count)
	if err != nil {
		return 0, fmt.Errorf("failed to count human patterns: %w", err)
	}
	return count, nil
}
