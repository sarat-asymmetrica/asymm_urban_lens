// Package learning implements Ananta's self-healing pattern database and error classification
//
// Diff Parser: Parses Git diff output into structured data
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"fmt"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
)

// DiffParser parses git diff output into structured FileDiff objects
type DiffParser struct{}

// ParseDiff converts git diff text to structured data
//
// Parses standard git diff format:
//
//	diff --git a/file.go b/file.go
//	@@ -10,5 +10,5 @@ func Foo() {
//	-    old line
//	+    new line
//	     context line
func (dp *DiffParser) ParseDiff(diffText string) ([]FileDiff, error) {
	var files []FileDiff
	var currentFile *FileDiff
	var currentHunk *DiffHunk

	lines := strings.Split(diffText, "\n")

	for i := 0; i < len(lines); i++ {
		line := lines[i]

		// New file diff
		if strings.HasPrefix(line, "diff --git") {
			// Save previous file if exists
			if currentFile != nil && currentHunk != nil {
				currentFile.Hunks = append(currentFile.Hunks, *currentHunk)
			}
			if currentFile != nil {
				files = append(files, *currentFile)
			}

			// Parse file path
			// Format: diff --git a/path/to/file.go b/path/to/file.go
			parts := strings.Fields(line)
			if len(parts) >= 4 {
				path := strings.TrimPrefix(parts[3], "b/")
				currentFile = &FileDiff{
					Path:     path,
					Language: detectLanguage(path),
					Hunks:    []DiffHunk{},
				}
			}
			currentHunk = nil
			continue
		}

		// Hunk header
		if strings.HasPrefix(line, "@@") {
			// Save previous hunk
			if currentFile != nil && currentHunk != nil {
				currentFile.Hunks = append(currentFile.Hunks, *currentHunk)
			}

			// Parse hunk header: @@ -10,5 +10,5 @@
			hunk, err := dp.parseHunkHeader(line)
			if err != nil {
				continue // Skip malformed hunks
			}
			currentHunk = hunk
			continue
		}

		// Skip if no current hunk
		if currentHunk == nil {
			continue
		}

		// Parse hunk content
		if strings.HasPrefix(line, "-") && !strings.HasPrefix(line, "---") {
			// Removed line
			currentHunk.RemovedLines = append(currentHunk.RemovedLines, strings.TrimPrefix(line, "-"))
		} else if strings.HasPrefix(line, "+") && !strings.HasPrefix(line, "+++") {
			// Added line
			currentHunk.AddedLines = append(currentHunk.AddedLines, strings.TrimPrefix(line, "+"))
		} else if strings.HasPrefix(line, " ") {
			// Context line
			currentHunk.Context = append(currentHunk.Context, strings.TrimPrefix(line, " "))
		}
	}

	// Save final file and hunk
	if currentFile != nil && currentHunk != nil {
		currentFile.Hunks = append(currentFile.Hunks, *currentHunk)
	}
	if currentFile != nil {
		files = append(files, *currentFile)
	}

	return files, nil
}

// parseHunkHeader parses hunk header line
// Format: @@ -10,5 +10,5 @@ optional context
func (dp *DiffParser) parseHunkHeader(line string) (*DiffHunk, error) {
	// Regex: @@ -(\d+),(\d+) \+(\d+),(\d+) @@
	re := regexp.MustCompile(`@@\s+-(\d+),(\d+)\s+\+(\d+),(\d+)\s+@@`)
	matches := re.FindStringSubmatch(line)

	if len(matches) < 5 {
		return nil, fmt.Errorf("invalid hunk header: %s", line)
	}

	oldStart, _ := strconv.Atoi(matches[1])
	oldLines, _ := strconv.Atoi(matches[2])
	newStart, _ := strconv.Atoi(matches[3])
	newLines, _ := strconv.Atoi(matches[4])

	return &DiffHunk{
		OldStart:     oldStart,
		OldLines:     oldLines,
		NewStart:     newStart,
		NewLines:     newLines,
		RemovedLines: []string{},
		AddedLines:   []string{},
		Context:      []string{},
	}, nil
}

// ExtractErrorContext extracts error-triggering code from a hunk
//
// The removed lines likely contained the error.
// Returns them with surrounding context.
func (dp *DiffParser) ExtractErrorContext(hunk DiffHunk) string {
	var lines []string

	// Add context before error
	if len(hunk.Context) > 0 {
		// Take last 3 context lines before removal
		start := len(hunk.Context) - 3
		if start < 0 {
			start = 0
		}
		for i := start; i < len(hunk.Context); i++ {
			lines = append(lines, hunk.Context[i])
		}
	}

	// Add removed lines (the error)
	for _, line := range hunk.RemovedLines {
		lines = append(lines, line)
	}

	return strings.Join(lines, "\n")
}

// ExtractFix extracts the fix from a hunk
//
// The added lines are the solution.
func (dp *DiffParser) ExtractFix(hunk DiffHunk) string {
	return strings.Join(hunk.AddedLines, "\n")
}

// detectLanguage determines programming language from file extension
func detectLanguage(path string) string {
	ext := strings.ToLower(filepath.Ext(path))

	switch ext {
	case ".go":
		return "Go"
	case ".rs":
		return "Rust"
	case ".py":
		return "Python"
	case ".js":
		return "JavaScript"
	case ".ts":
		return "TypeScript"
	case ".java":
		return "Java"
	case ".c":
		return "C"
	case ".cpp", ".cc", ".cxx":
		return "C++"
	case ".h", ".hpp":
		return "C/C++ Header"
	case ".rb":
		return "Ruby"
	case ".php":
		return "PHP"
	default:
		return "Unknown"
	}
}
