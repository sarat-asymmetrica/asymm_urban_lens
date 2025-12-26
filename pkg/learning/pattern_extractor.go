// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Extractor: Extract code patterns from open-source repositories
// Author: Agent 1.1 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/learning/parsers"
)

// PatternExtractor extracts patterns from source repositories
type PatternExtractor struct {
	db          *PatternDB
	goParser    *parsers.GoParser
	maxPatterns int // Limit to prevent memory issues
}

// NewPatternExtractor creates a new pattern extractor
func NewPatternExtractor(db *PatternDB) *PatternExtractor {
	return &PatternExtractor{
		db:          db,
		goParser:    parsers.NewGoParser(),
		maxPatterns: 10000, // Safety limit
	}
}

// ExtractFromRepo extracts patterns from a repository
//
// Args:
//   - repoPath: Path to cloned repository
//   - language: Primary language ("Go", "TypeScript", etc.)
//
// Returns:
//   - Extracted patterns
//   - Error if extraction fails
//
// Process:
//  1. Find source files for language
//  2. Parse each file using language-specific parser
//  3. Extract patterns from AST
//  4. Classify error signature for each pattern
//  5. Store in database
func (e *PatternExtractor) ExtractFromRepo(repoPath, language string) ([]*Pattern, error) {
	// Find source files
	files, err := e.FindSourceFiles(repoPath, language)
	if err != nil {
		return nil, fmt.Errorf("failed to find source files: %w", err)
	}

	if len(files) == 0 {
		return nil, fmt.Errorf("no %s source files found in %s", language, repoPath)
	}

	// Williams batching: process files in batches of sqrt(n) * log2(n)
	batchSize := WilliamsBatchSize(len(files))
	if batchSize == 0 {
		batchSize = 1
	}

	var allPatterns []*Pattern
	processedFiles := 0

	for i := 0; i < len(files); i += batchSize {
		end := i + batchSize
		if end > len(files) {
			end = len(files)
		}

		batch := files[i:end]
		for _, filePath := range batch {
			patterns, err := e.ExtractFromFile(filePath, language)
			if err != nil {
				// Log error but continue processing
				continue
			}

			allPatterns = append(allPatterns, patterns...)
			processedFiles++

			// Safety check: prevent memory overflow
			if len(allPatterns) >= e.maxPatterns {
				break
			}
		}

		if len(allPatterns) >= e.maxPatterns {
			break
		}
	}

	return allPatterns, nil
}

// ExtractFromFile extracts patterns from a single source file
func (e *PatternExtractor) ExtractFromFile(filePath, language string) ([]*Pattern, error) {
	var extractedPatterns []*parsers.ExtractedPattern
	var err error

	switch language {
	case "Go":
		extractedPatterns, err = e.goParser.ExtractPatterns(filePath)
	case "TypeScript", "JavaScript":
		// TODO: Implement TypeScript parser
		return nil, fmt.Errorf("TypeScript parser not yet implemented")
	case "Python":
		// TODO: Implement Python parser
		return nil, fmt.Errorf("Python parser not yet implemented")
	case "Rust":
		// TODO: Implement Rust parser
		return nil, fmt.Errorf("Rust parser not yet implemented")
	default:
		return nil, fmt.Errorf("unsupported language: %s", language)
	}

	if err != nil {
		return nil, err
	}

	// Convert extracted patterns to database patterns
	var patterns []*Pattern
	for _, ep := range extractedPatterns {
		// Read actual code from file
		code, err := e.readCodeSnippet(ep.FilePath, ep.StartLine, ep.EndLine)
		if err != nil {
			// Skip if can't read code
			continue
		}

		// Normalize code for signature
		normalized := NormalizeCodePattern(code)

		// Compute solution hash for grouping
		hash := sha256.Sum256([]byte(normalized))
		solutionHash := hex.EncodeToString(hash[:])

		// Classify error signature (use code as "error" for signature)
		classification := ClassifyFullError(normalized)

		pattern := &Pattern{
			ErrorSig:     classification.Signature,
			ErrorType:    "pattern", // Special type for learned patterns
			Language:     ep.Language,
			Category:     string(ep.Category),
			SolutionCode: code,
			SolutionHash: solutionHash,
			Confidence:   0.50, // Initial confidence (will be updated by frequency analyzer)
			Frequency:    1,
			CreatedAt:    time.Now(),
			UpdatedAt:    time.Now(),
		}

		patterns = append(patterns, pattern)
	}

	return patterns, nil
}

// FindSourceFiles finds source files in repository for given language
func (e *PatternExtractor) FindSourceFiles(repoPath, language string) ([]string, error) {
	extensions := LanguageExtensions(language)
	if len(extensions) == 0 {
		return nil, fmt.Errorf("unknown language: %s", language)
	}

	var files []string

	err := filepath.WalkDir(repoPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil // Skip errors, continue walking
		}

		// Skip hidden directories and vendor/node_modules
		if d.IsDir() {
			name := d.Name()
			if strings.HasPrefix(name, ".") || name == "vendor" || name == "node_modules" || name == "__pycache__" {
				return fs.SkipDir
			}
			return nil
		}

		// Check if file has matching extension
		for _, ext := range extensions {
			if strings.HasSuffix(path, ext) {
				// Skip test files for now (focus on production code patterns)
				if !strings.Contains(path, "_test.") && !strings.Contains(path, ".test.") && !strings.Contains(path, ".spec.") {
					files = append(files, path)
					break
				}
			}
		}

		return nil
	})

	if err != nil {
		return nil, err
	}

	return files, nil
}

// readCodeSnippet reads code between startLine and endLine from file
func (e *PatternExtractor) readCodeSnippet(filePath string, startLine, endLine int) (string, error) {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return "", err
	}

	lines := strings.Split(string(content), "\n")
	if startLine < 1 || startLine > len(lines) {
		return "", fmt.Errorf("invalid start line: %d", startLine)
	}
	if endLine < startLine || endLine > len(lines) {
		endLine = len(lines)
	}

	// Extract lines (1-indexed to 0-indexed)
	snippet := strings.Join(lines[startLine-1:endLine], "\n")
	return snippet, nil
}

// LanguageExtensions returns file extensions for language
func LanguageExtensions(language string) []string {
	extensions := map[string][]string{
		"Go":         {".go"},
		"TypeScript": {".ts", ".tsx"},
		"JavaScript": {".js", ".jsx"},
		"Python":     {".py"},
		"Rust":       {".rs"},
	}
	return extensions[language]
}

// NormalizeCodePattern normalizes code for pattern matching
func NormalizeCodePattern(code string) string {
	// Remove leading/trailing whitespace
	code = strings.TrimSpace(code)

	// Normalize variable names to placeholders
	// This is simplified - a full implementation would use AST
	code = strings.ReplaceAll(code, "\t", "  ")

	return code
}

// WilliamsBatchSize computes optimal batch size using Williams' algorithm
// Formula: floor(sqrt(n) * log2(n))
func WilliamsBatchSize(n int) int {
	if n <= 1 {
		return 1
	}

	sqrt := 1
	for sqrt*sqrt < n {
		sqrt++
	}
	if sqrt*sqrt > n {
		sqrt--
	}

	log2 := 0
	temp := n
	for temp > 1 {
		temp /= 2
		log2++
	}

	batch := sqrt * log2
	if batch == 0 {
		return 1
	}
	return batch
}

// ExtractAndStore extracts patterns from repo and stores in database
func (e *PatternExtractor) ExtractAndStore(repoPath, repoName, language string) (int, error) {
	patterns, err := e.ExtractFromRepo(repoPath, language)
	if err != nil {
		return 0, err
	}

	// Get repo ID from database
	repo, err := e.db.GetRepo(repoName)
	if err != nil {
		// Repo not in DB, skip for now
		return 0, fmt.Errorf("repo not found in database: %s", repoName)
	}

	stored := 0
	for _, pattern := range patterns {
		// Add repo ID to sources
		pattern.RepoSources = []int64{repo.ID}

		// Store in database
		err := e.db.AddPattern(pattern)
		if err != nil {
			// Log error but continue
			continue
		}
		stored++
	}

	return stored, nil
}
