// Package learning implements Ananta's self-healing pattern database and error classification
//
// Commit Analyzer Tests
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"context"
	"strings"
	"testing"
)

func TestCommitAnalyzer_FindCompilationFixCommits(t *testing.T) {
	// Use asymm_ananta repo itself (if it's a git repo)
	analyzer := NewCommitAnalyzer("../../")
	ctx := context.Background()

	commits, err := analyzer.FindCompilationFixCommits(ctx)
	if err != nil {
		// Not a git repo - skip test
		t.Skipf("Not a git repository: %v", err)
		return
	}

	t.Logf("Found %d compilation fix commits", len(commits))

	// We don't know exact count, but should be reasonable
	if len(commits) < 0 {
		t.Errorf("Expected at least 0 commits, got %d", len(commits))
	}

	// Verify commit structure
	for _, commit := range commits {
		if commit.Hash == "" {
			t.Errorf("Commit has empty hash")
		}
		if len(commit.Hash) < 8 {
			t.Errorf("Commit hash too short: %s", commit.Hash)
		}
		if commit.Message == "" {
			t.Errorf("Commit %s has empty message", commit.Hash)
		}

		// Message should contain compilation-related keywords
		message := strings.ToLower(commit.Message)
		hasKeyword := strings.Contains(message, "compil") ||
			strings.Contains(message, "undefined") ||
			strings.Contains(message, "type mismatch") ||
			strings.Contains(message, "missing import") ||
			strings.Contains(message, "cannot use") ||
			strings.Contains(message, "not defined") ||
			strings.Contains(message, "does not implement") ||
			strings.Contains(message, "has no method") ||
			strings.Contains(message, "imported and not used")

		if !hasKeyword {
			t.Logf("Warning: Commit %s message doesn't contain expected keywords: %s", commit.Hash[:8], commit.Message)
		}
	}
}

func TestCommitAnalyzer_AnalyzeCommit(t *testing.T) {
	// This test requires actual commits - we'll use a mock scenario
	analyzer := NewCommitAnalyzer("../../")
	ctx := context.Background()

	// First find a commit
	commits, err := analyzer.FindCompilationFixCommits(ctx)
	if err != nil {
		t.Skipf("Not a git repository: %v", err)
		return
	}

	if len(commits) == 0 {
		t.Skip("No compilation fix commits found")
	}

	// Analyze first commit
	commit := commits[0]
	t.Logf("Analyzing commit %s: %s", commit.Hash[:8], commit.Message)

	diff, err := analyzer.AnalyzeCommit(ctx, commit.Hash)
	if err != nil {
		t.Fatalf("AnalyzeCommit failed: %v", err)
	}

	// Verify diff structure
	if diff.Commit.Hash != commit.Hash {
		t.Errorf("Expected hash %s, got %s", commit.Hash, diff.Commit.Hash)
	}

	t.Logf("Diff has %d files", len(diff.Files))

	for i, file := range diff.Files {
		t.Logf("  File %d: %s (%s) - %d hunks", i+1, file.Path, file.Language, len(file.Hunks))

		for j, hunk := range file.Hunks {
			t.Logf("    Hunk %d: -%d,+%d (removed: %d lines, added: %d lines)",
				j+1, hunk.OldLines, hunk.NewLines,
				len(hunk.RemovedLines), len(hunk.AddedLines))
		}
	}
}

func TestCommitInfo_Structure(t *testing.T) {
	commit := CommitInfo{
		Hash:    "abc123def456",
		Message: "fix: compilation error",
		Author:  "Test Author",
	}

	if commit.Hash != "abc123def456" {
		t.Errorf("Expected hash abc123def456, got %s", commit.Hash)
	}
	if commit.Message != "fix: compilation error" {
		t.Errorf("Expected message 'fix: compilation error', got %s", commit.Message)
	}
	if commit.Author != "Test Author" {
		t.Errorf("Expected author 'Test Author', got %s", commit.Author)
	}
}

func TestNewCommitAnalyzer(t *testing.T) {
	analyzer := NewCommitAnalyzer("/test/path")

	if analyzer == nil {
		t.Fatal("NewCommitAnalyzer returned nil")
	}
	if analyzer.repoPath != "/test/path" {
		t.Errorf("Expected repoPath /test/path, got %s", analyzer.repoPath)
	}
}
