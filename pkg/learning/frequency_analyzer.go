// Package learning implements Ananta's self-healing pattern database and error classification
//
// Frequency Analyzer: Groups similar patterns and calculates confidence scores
// Author: Agent 1.2 (Dr. Sofia Hernandez - Statistician)
// Created: 2025-11-07
package learning

import (
	"context"
	"database/sql"
	"encoding/json"
	"fmt"
	"time"
)

// FrequencyAnalyzer analyzes pattern frequency and calculates confidence
type FrequencyAnalyzer struct {
	db *PatternDB
}

// NewFrequencyAnalyzer creates a frequency analyzer
func NewFrequencyAnalyzer(db *PatternDB) *FrequencyAnalyzer {
	return &FrequencyAnalyzer{db: db}
}

// PatternGroup represents a cluster of similar patterns
type PatternGroup struct {
	Representative *Pattern   // Canonical pattern (highest confidence)
	Members        []*Pattern // All patterns in group
	Similarity     float64    // Average similarity within group
	TotalRepos     int        // Combined repo coverage
}

// AnalyzeAllPatterns analyzes ALL patterns in database
//
// Steps:
//  1. Load all patterns from database
//  2. Group similar patterns (exact duplicates + structural similarity)
//  3. Calculate confidence for each pattern/group
//  4. Update database with new confidence scores
//
// Returns: error if analysis fails
func (a *FrequencyAnalyzer) AnalyzeAllPatterns(ctx context.Context) error {
	// Get total repo count for frequency calculation
	totalRepos, err := a.getTotalRepoCount()
	if err != nil {
		return fmt.Errorf("failed to get repo count: %w", err)
	}

	// Load all patterns
	patterns, err := a.getAllPatterns()
	if err != nil {
		return fmt.Errorf("failed to load patterns: %w", err)
	}

	if len(patterns) == 0 {
		return fmt.Errorf("no patterns found in database")
	}

	// Group similar patterns
	groups, err := a.GroupSimilarPatterns(patterns)
	if err != nil {
		return fmt.Errorf("failed to group patterns: %w", err)
	}

	// Calculate confidence for each pattern
	for _, group := range groups {
		for _, pattern := range group.Members {
			// Calculate confidence
			confidence := CalculateConfidence(pattern, totalRepos)
			pattern.Confidence = confidence

			// Update database
			if err := a.updatePatternConfidence(pattern.ID, confidence); err != nil {
				return fmt.Errorf("failed to update pattern %d: %w", pattern.ID, err)
			}
		}
	}

	return nil
}

// AnalyzePatterns analyzes patterns for specific category/language
//
// Args:
//   - category: Pattern category (error_handling, crud, etc.)
//   - language: Programming language (Go, TypeScript, etc.)
//
// Returns: error if analysis fails
func (a *FrequencyAnalyzer) AnalyzePatterns(category, language string) error {
	// Get total repo count
	totalRepos, err := a.getTotalRepoCount()
	if err != nil {
		return fmt.Errorf("failed to get repo count: %w", err)
	}

	// Load patterns for category/language
	patterns, err := a.getPatternsForCategory(category, language)
	if err != nil {
		return fmt.Errorf("failed to load patterns: %w", err)
	}

	if len(patterns) == 0 {
		return nil // No patterns to analyze
	}

	// Group similar patterns
	groups, err := a.GroupSimilarPatterns(patterns)
	if err != nil {
		return fmt.Errorf("failed to group patterns: %w", err)
	}

	// Calculate confidence for each pattern
	for _, group := range groups {
		for _, pattern := range group.Members {
			confidence := CalculateConfidence(pattern, totalRepos)
			pattern.Confidence = confidence

			if err := a.updatePatternConfidence(pattern.ID, confidence); err != nil {
				return fmt.Errorf("failed to update pattern %d: %w", pattern.ID, err)
			}
		}
	}

	return nil
}

// GroupSimilarPatterns groups patterns by structural similarity
//
// Algorithm:
//  1. PHASE 1: Group by exact hash (exact duplicates)
//  2. PHASE 2: Group by structural similarity (≥85% match)
//  3. For each group, select representative (highest confidence)
//
// Returns: list of pattern groups
func (a *FrequencyAnalyzer) GroupSimilarPatterns(patterns []*Pattern) ([]PatternGroup, error) {
	if len(patterns) == 0 {
		return nil, nil
	}

	// PHASE 1: Group by hash (exact duplicates)
	hashGroups := GroupByHash(patterns)

	// PHASE 2: Merge similar groups (structural similarity)
	var finalGroups []PatternGroup

	processed := make(map[*Pattern]bool)

	for hash, members := range hashGroups {
		// Skip if all members already processed
		allProcessed := true
		for _, m := range members {
			if !processed[m] {
				allProcessed = false
				break
			}
		}
		if allProcessed {
			continue
		}

		// Create group
		group := PatternGroup{
			Members:    members,
			TotalRepos: countUniqueRepos(members),
		}

		// Mark as processed
		for _, m := range members {
			processed[m] = true
		}

		// Try to merge with existing groups (structural similarity)
		merged := false
		for i := range finalGroups {
			if a.canMergeGroups(&group, &finalGroups[i]) {
				// Merge groups
				finalGroups[i].Members = append(finalGroups[i].Members, group.Members...)
				finalGroups[i].TotalRepos = countUniqueRepos(finalGroups[i].Members)
				merged = true
				break
			}
		}

		if !merged {
			finalGroups = append(finalGroups, group)
		}

		// Update hash if missing
		if hash == "" {
			for _, m := range members {
				if m.SolutionHash == "" {
					m.SolutionHash = HashSolution(m.SolutionCode)
				}
			}
		}
	}

	// Select representative for each group (highest confidence)
	for i := range finalGroups {
		finalGroups[i].Representative = selectRepresentative(finalGroups[i].Members)
		finalGroups[i].Similarity = calculateGroupSimilarity(finalGroups[i].Members)
	}

	return finalGroups, nil
}

// canMergeGroups checks if two groups can be merged (similar patterns)
func (a *FrequencyAnalyzer) canMergeGroups(g1, g2 *PatternGroup) bool {
	// Compare representatives or first members
	p1 := g1.Representative
	if p1 == nil && len(g1.Members) > 0 {
		p1 = g1.Members[0]
	}

	p2 := g2.Representative
	if p2 == nil && len(g2.Members) > 0 {
		p2 = g2.Members[0]
	}

	if p1 == nil || p2 == nil {
		return false
	}

	// Check if patterns are similar (≥85% threshold)
	similar, _ := AreSimilar(p1, p2)
	return similar
}

// selectRepresentative chooses the best pattern from group
// (highest confidence, most repo sources)
func selectRepresentative(patterns []*Pattern) *Pattern {
	if len(patterns) == 0 {
		return nil
	}

	best := patterns[0]
	for _, p := range patterns[1:] {
		// Prefer higher confidence
		if p.Confidence > best.Confidence {
			best = p
		} else if p.Confidence == best.Confidence {
			// Tiebreak: more repo sources
			if len(p.RepoSources) > len(best.RepoSources) {
				best = p
			}
		}
	}

	return best
}

// calculateGroupSimilarity computes average pairwise similarity
func calculateGroupSimilarity(patterns []*Pattern) float64 {
	if len(patterns) <= 1 {
		return 1.0 // Single pattern is perfectly similar to itself
	}

	var totalSimilarity float64
	var comparisons int

	for i := 0; i < len(patterns); i++ {
		for j := i + 1; j < len(patterns); j++ {
			_, sim := AreSimilar(patterns[i], patterns[j])
			totalSimilarity += sim
			comparisons++
		}
	}

	if comparisons == 0 {
		return 1.0
	}

	return totalSimilarity / float64(comparisons)
}

// countUniqueRepos counts unique repos across patterns
func countUniqueRepos(patterns []*Pattern) int {
	seen := make(map[int64]bool)

	for _, p := range patterns {
		for _, repoID := range p.RepoSources {
			seen[repoID] = true
		}
	}

	return len(seen)
}

// getTotalRepoCount gets total number of repos in database
func (a *FrequencyAnalyzer) getTotalRepoCount() (int, error) {
	query := `SELECT COUNT(*) FROM repos`

	var count int
	err := a.db.db.QueryRow(query).Scan(&count)
	if err != nil {
		return 0, fmt.Errorf("failed to count repos: %w", err)
	}

	return count, nil
}

// getAllPatterns loads all patterns from database
func (a *FrequencyAnalyzer) getAllPatterns() ([]*Pattern, error) {
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		ORDER BY category, language
	`

	rows, err := a.db.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("failed to query patterns: %w", err)
	}
	defer rows.Close()

	return a.scanPatterns(rows)
}

// getPatternsForCategory loads patterns for specific category/language
func (a *FrequencyAnalyzer) getPatternsForCategory(category, language string) ([]*Pattern, error) {
	query := `
		SELECT id, error_signature, error_type, language, category, solution_code, solution_hash,
		       confidence, frequency, last_applied, success_count, failure_count, repo_sources,
		       created_at, updated_at
		FROM patterns
		WHERE category = ? AND language = ?
		ORDER BY confidence DESC
	`

	rows, err := a.db.db.Query(query, category, language)
	if err != nil {
		return nil, fmt.Errorf("failed to query patterns: %w", err)
	}
	defer rows.Close()

	return a.scanPatterns(rows)
}

// scanPatterns scans SQL rows into Pattern structs
func (a *FrequencyAnalyzer) scanPatterns(rows *sql.Rows) ([]*Pattern, error) {
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

	return patterns, nil
}

// updatePatternConfidence updates confidence in database
func (a *FrequencyAnalyzer) updatePatternConfidence(id int64, confidence float64) error {
	query := `UPDATE patterns SET confidence = ?, updated_at = datetime('now') WHERE id = ?`
	_, err := a.db.db.Exec(query, confidence, id)
	if err != nil {
		return fmt.Errorf("failed to update confidence: %w", err)
	}
	return nil
}

// GetConfidenceDistribution calculates distribution statistics
//
// Returns:
//   - Counts for HIGH, MEDIUM, LOW tiers
//   - Average confidence (harmonic mean)
func (a *FrequencyAnalyzer) GetConfidenceDistribution() (*ConfidenceDistribution, error) {
	patterns, err := a.getAllPatterns()
	if err != nil {
		return nil, fmt.Errorf("failed to load patterns: %w", err)
	}

	dist := CalculateDistribution(patterns)
	return dist, nil
}

// GetCategoryStats returns stats grouped by category
type CategoryStats struct {
	Category      string  `json:"category"`
	Language      string  `json:"language"`
	Count         int     `json:"count"`
	AvgConfidence float64 `json:"avg_confidence"`
	AvgFrequency  float64 `json:"avg_frequency"`
}

// GetStatsByCategory retrieves aggregated stats by category
func (a *FrequencyAnalyzer) GetStatsByCategory() ([]CategoryStats, error) {
	query := `
		SELECT category, language, COUNT(*) as count,
		       AVG(confidence) as avg_confidence,
		       AVG(frequency) as avg_frequency
		FROM patterns
		GROUP BY category, language
		ORDER BY avg_confidence DESC
	`

	rows, err := a.db.db.Query(query)
	if err != nil {
		return nil, fmt.Errorf("failed to query stats: %w", err)
	}
	defer rows.Close()

	var stats []CategoryStats
	for rows.Next() {
		var s CategoryStats
		if err := rows.Scan(&s.Category, &s.Language, &s.Count, &s.AvgConfidence, &s.AvgFrequency); err != nil {
			return nil, fmt.Errorf("failed to scan stats: %w", err)
		}
		stats = append(stats, s)
	}

	return stats, nil
}
