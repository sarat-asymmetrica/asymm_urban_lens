// Package verification implements compilation verification and regression detection
//
// Verification Cache: Cache compilation results to avoid redundant builds
// Author: Agent 4.1 (Dr. Liam O'Connor - Formal Verification, Oxford)
// Created: 2025-11-07
// Ported: 2025-12-26 (Urban Lens Integration)
package verification

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"sync"
)

// VerificationCache stores build results keyed by file hash
type VerificationCache struct {
	results map[string]*VerificationResult
	mu      sync.RWMutex // Thread-safe access
}

// NewVerificationCache creates a new cache
func NewVerificationCache() *VerificationCache {
	return &VerificationCache{
		results: make(map[string]*VerificationResult),
	}
}

// Get retrieves cached result for file hash
func (vc *VerificationCache) Get(fileHash string) (*VerificationResult, bool) {
	vc.mu.RLock()
	defer vc.mu.RUnlock()

	result, exists := vc.results[fileHash]
	return result, exists
}

// Set stores verification result
func (vc *VerificationCache) Set(fileHash string, result *VerificationResult) {
	vc.mu.Lock()
	defer vc.mu.Unlock()

	vc.results[fileHash] = result
}

// Clear removes all cached results
func (vc *VerificationCache) Clear() {
	vc.mu.Lock()
	defer vc.mu.Unlock()

	vc.results = make(map[string]*VerificationResult)
}

// Size returns number of cached results
func (vc *VerificationCache) Size() int {
	vc.mu.RLock()
	defer vc.mu.RUnlock()

	return len(vc.results)
}

// CalculateFileHash computes hash of project state
// This walks all Go files and creates a deterministic hash
func CalculateFileHash(projectPath string) (string, error) {
	// Collect all relevant files
	var files []string
	err := filepath.WalkDir(projectPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}

		// Skip directories and non-Go files
		if d.IsDir() {
			// Skip common directories
			name := d.Name()
			if name == ".git" || name == "vendor" || name == "node_modules" {
				return filepath.SkipDir
			}
			return nil
		}

		// Include only Go source files
		if filepath.Ext(path) == ".go" {
			files = append(files, path)
		}

		return nil
	})
	if err != nil {
		return "", fmt.Errorf("failed to walk directory: %w", err)
	}

	// Sort files for deterministic hashing
	sort.Strings(files)

	// Create hash from all file contents
	hasher := sha256.New()

	for _, filePath := range files {
		// Read file content
		content, err := os.ReadFile(filePath)
		if err != nil {
			return "", fmt.Errorf("failed to read file %s: %w", filePath, err)
		}

		// Hash filename and content
		hasher.Write([]byte(filePath))
		hasher.Write(content)
	}

	// Return hex-encoded hash
	hashBytes := hasher.Sum(nil)
	return hex.EncodeToString(hashBytes), nil
}

// CalculateFileHashFast computes fast hash using only file metadata
// Useful for quick cache checks (trades accuracy for speed)
func CalculateFileHashFast(projectPath string) (string, error) {
	var files []string
	var sizes []int64
	var modTimes []int64

	err := filepath.WalkDir(projectPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}

		if d.IsDir() {
			name := d.Name()
			if name == ".git" || name == "vendor" || name == "node_modules" {
				return filepath.SkipDir
			}
			return nil
		}

		if filepath.Ext(path) == ".go" {
			info, err := d.Info()
			if err != nil {
				return err
			}

			files = append(files, path)
			sizes = append(sizes, info.Size())
			modTimes = append(modTimes, info.ModTime().Unix())
		}

		return nil
	})
	if err != nil {
		return "", fmt.Errorf("failed to walk directory: %w", err)
	}

	// Sort for determinism
	sort.Strings(files)

	// Hash file paths, sizes, and modification times
	hasher := sha256.New()
	for i, file := range files {
		hasher.Write([]byte(file))
		hasher.Write([]byte(fmt.Sprintf("%d:%d", sizes[i], modTimes[i])))
	}

	hashBytes := hasher.Sum(nil)
	return hex.EncodeToString(hashBytes), nil
}
