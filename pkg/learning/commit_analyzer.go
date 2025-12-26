// Package learning implements Ananta's self-healing pattern database and error classification
//
// Commit Analyzer: Mines Git history for compilation error fix commits
// Author: Agent 6.1 (Dr. Isabella Romano - Mining Software Repositories)
// Created: 2025-11-07
package learning

import (
	"context"
	"fmt"
	"os/exec"
	"strings"
	"time"
)

// CommitAnalyzer extracts patterns from Git commits
type CommitAnalyzer struct {
	repoPath string
}

// NewCommitAnalyzer creates analyzer for a repository
func NewCommitAnalyzer(repoPath string) *CommitAnalyzer {
	return &CommitAnalyzer{
		repoPath: repoPath,
	}
}

// CommitInfo represents a commit that likely fixes compilation errors
type CommitInfo struct {
	Hash         string
	Message      string
	Author       string
	Date         time.Time
	FilesChanged []string
}

// FindCompilationFixCommits finds commits that fix compilation errors
//
// Searches git log for commits with messages containing compilation-related keywords:
// - "fix: compilation"
// - "fix compilation error"
// - "undefined:"
// - "type mismatch"
// - "missing import"
// - "cannot use"
// - "not defined"
//
// Returns commits ordered by date (newest first).
func (ca *CommitAnalyzer) FindCompilationFixCommits(ctx context.Context) ([]CommitInfo, error) {
	// Compilation error keywords to search for
	keywords := []string{
		"compilation",
		"compile",
		"undefined",
		"type mismatch",
		"missing import",
		"cannot use",
		"not defined",
		"does not implement",
		"has no method",
		"imported and not used",
	}

	// Build git log command with grep patterns
	args := []string{"log", "--all", "--format=%H|%s|%an|%ai"}

	// Add grep patterns for each keyword
	for _, keyword := range keywords {
		args = append(args, "--grep="+keyword)
	}

	// Use --regexp-ignore-case for case-insensitive matching
	args = append(args, "-i")

	cmd := exec.CommandContext(ctx, "git", args...)
	cmd.Dir = ca.repoPath

	output, err := cmd.CombinedOutput()
	if err != nil {
		return nil, fmt.Errorf("git log failed: %w (output: %s)", err, string(output))
	}

	// Parse output
	var commits []CommitInfo
	lines := strings.Split(string(output), "\n")

	for _, line := range lines {
		if line == "" {
			continue
		}

		parts := strings.SplitN(line, "|", 4)
		if len(parts) < 4 {
			continue
		}

		hash := parts[0]
		message := parts[1]
		author := parts[2]
		dateStr := parts[3]

		// Parse date
		date, err := time.Parse("2006-01-02 15:04:05 -0700", dateStr)
		if err != nil {
			// Try RFC3339 format as fallback
			date, _ = time.Parse(time.RFC3339, dateStr)
		}

		commits = append(commits, CommitInfo{
			Hash:    hash,
			Message: message,
			Author:  author,
			Date:    date,
		})
	}

	return commits, nil
}

// AnalyzeCommit extracts before/after code from a commit
//
// Runs git show to get the diff and parses it into structured format.
func (ca *CommitAnalyzer) AnalyzeCommit(ctx context.Context, hash string) (*CommitDiff, error) {
	cmd := exec.CommandContext(ctx, "git", "show", "--format=%H|%s|%an|%ai", hash)
	cmd.Dir = ca.repoPath

	output, err := cmd.CombinedOutput()
	if err != nil {
		return nil, fmt.Errorf("git show failed: %w", err)
	}

	diffText := string(output)

	// Parse commit info from first line
	lines := strings.Split(diffText, "\n")
	if len(lines) == 0 {
		return nil, fmt.Errorf("empty git show output")
	}

	parts := strings.SplitN(lines[0], "|", 4)
	if len(parts) < 4 {
		return nil, fmt.Errorf("invalid git show format")
	}

	date, _ := time.Parse("2006-01-02 15:04:05 -0700", parts[3])

	commitInfo := CommitInfo{
		Hash:    parts[0],
		Message: parts[1],
		Author:  parts[2],
		Date:    date,
	}

	// Parse diff (everything after first line)
	parser := &DiffParser{}
	files, err := parser.ParseDiff(strings.Join(lines[1:], "\n"))
	if err != nil {
		return nil, fmt.Errorf("failed to parse diff: %w", err)
	}

	return &CommitDiff{
		Commit: commitInfo,
		Files:  files,
	}, nil
}

// CommitDiff represents a commit's changes
type CommitDiff struct {
	Commit CommitInfo
	Files  []FileDiff
}

// FileDiff represents changes to one file
type FileDiff struct {
	Path     string
	Language string
	Hunks    []DiffHunk
}

// DiffHunk represents one change block in a diff
type DiffHunk struct {
	OldStart     int
	OldLines     int
	NewStart     int
	NewLines     int
	RemovedLines []string
	AddedLines   []string
	Context      []string // Surrounding unchanged lines
}
