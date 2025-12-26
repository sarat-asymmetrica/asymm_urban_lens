// Package learning implements Ananta's self-healing pattern database and error classification
//
// Diff Parser Tests
// Author: Agent 6.1 (Dr. Isabella Romano)
// Created: 2025-11-07
package learning

import (
	"strings"
	"testing"
)

func TestDiffParser_ParseSimpleDiff(t *testing.T) {
	diffText := `diff --git a/file.go b/file.go
--- a/file.go
+++ b/file.go
@@ -10,5 +10,5 @@ func Foo() {
 	// context line
-	old := "removed"
+	new := "added"
 	// more context
`

	parser := &DiffParser{}
	files, err := parser.ParseDiff(diffText)

	if err != nil {
		t.Fatalf("ParseDiff failed: %v", err)
	}

	if len(files) != 1 {
		t.Fatalf("Expected 1 file, got %d", len(files))
	}

	file := files[0]
	if file.Path != "file.go" {
		t.Errorf("Expected path file.go, got %s", file.Path)
	}
	if file.Language != "Go" {
		t.Errorf("Expected language Go, got %s", file.Language)
	}

	if len(file.Hunks) != 1 {
		t.Fatalf("Expected 1 hunk, got %d", len(file.Hunks))
	}

	hunk := file.Hunks[0]
	if hunk.OldStart != 10 {
		t.Errorf("Expected OldStart 10, got %d", hunk.OldStart)
	}
	if hunk.OldLines != 5 {
		t.Errorf("Expected OldLines 5, got %d", hunk.OldLines)
	}
	if hunk.NewStart != 10 {
		t.Errorf("Expected NewStart 10, got %d", hunk.NewStart)
	}
	if hunk.NewLines != 5 {
		t.Errorf("Expected NewLines 5, got %d", hunk.NewLines)
	}

	if len(hunk.RemovedLines) != 1 {
		t.Fatalf("Expected 1 removed line, got %d", len(hunk.RemovedLines))
	}
	if !strings.Contains(hunk.RemovedLines[0], "old") {
		t.Errorf("Expected removed line to contain 'old', got %s", hunk.RemovedLines[0])
	}

	if len(hunk.AddedLines) != 1 {
		t.Fatalf("Expected 1 added line, got %d", len(hunk.AddedLines))
	}
	if !strings.Contains(hunk.AddedLines[0], "new") {
		t.Errorf("Expected added line to contain 'new', got %s", hunk.AddedLines[0])
	}
}

func TestDiffParser_ParseMultiFileDiff(t *testing.T) {
	diffText := `diff --git a/file1.go b/file1.go
@@ -1,3 +1,3 @@
-old line 1
+new line 1
 context
diff --git a/file2.rs b/file2.rs
@@ -5,2 +5,2 @@
-old line 2
+new line 2
`

	parser := &DiffParser{}
	files, err := parser.ParseDiff(diffText)

	if err != nil {
		t.Fatalf("ParseDiff failed: %v", err)
	}

	if len(files) != 2 {
		t.Fatalf("Expected 2 files, got %d", len(files))
	}

	// Verify first file
	if files[0].Path != "file1.go" {
		t.Errorf("Expected path file1.go, got %s", files[0].Path)
	}
	if files[0].Language != "Go" {
		t.Errorf("Expected language Go, got %s", files[0].Language)
	}

	// Verify second file
	if files[1].Path != "file2.rs" {
		t.Errorf("Expected path file2.rs, got %s", files[1].Path)
	}
	if files[1].Language != "Rust" {
		t.Errorf("Expected language Rust, got %s", files[1].Language)
	}
}

func TestDiffParser_ExtractErrorContext(t *testing.T) {
	hunk := DiffHunk{
		Context:      []string{"line 1", "line 2", "line 3"},
		RemovedLines: []string{"undefined: Foo", "Bar()"},
	}

	parser := &DiffParser{}
	context := parser.ExtractErrorContext(hunk)

	if !strings.Contains(context, "line 3") {
		t.Errorf("Expected context to contain 'line 3', got %s", context)
	}
	if !strings.Contains(context, "undefined: Foo") {
		t.Errorf("Expected context to contain 'undefined: Foo', got %s", context)
	}
}

func TestDiffParser_ExtractFix(t *testing.T) {
	hunk := DiffHunk{
		AddedLines: []string{"import \"foo\"", "func Bar() {}"},
	}

	parser := &DiffParser{}
	fix := parser.ExtractFix(hunk)

	if !strings.Contains(fix, "import") {
		t.Errorf("Expected fix to contain 'import', got %s", fix)
	}
	if !strings.Contains(fix, "Bar") {
		t.Errorf("Expected fix to contain 'Bar', got %s", fix)
	}
}

func TestDetectLanguage(t *testing.T) {
	tests := []struct {
		path     string
		expected string
	}{
		{"main.go", "Go"},
		{"lib.rs", "Rust"},
		{"script.py", "Python"},
		{"app.js", "JavaScript"},
		{"component.ts", "TypeScript"},
		{"App.java", "Java"},
		{"program.c", "C"},
		{"program.cpp", "C++"},
		{"header.h", "C/C++ Header"},
		{"script.rb", "Ruby"},
		{"index.php", "PHP"},
		{"unknown.xyz", "Unknown"},
	}

	for _, test := range tests {
		result := detectLanguage(test.path)
		if result != test.expected {
			t.Errorf("detectLanguage(%s) = %s, expected %s", test.path, result, test.expected)
		}
	}
}

func TestDiffParser_ParseHunkHeader(t *testing.T) {
	tests := []struct {
		line     string
		oldStart int
		oldLines int
		newStart int
		newLines int
	}{
		{"@@ -10,5 +10,5 @@ func Foo() {", 10, 5, 10, 5},
		{"@@ -1,3 +1,4 @@ package main", 1, 3, 1, 4},
		{"@@ -100,20 +100,15 @@", 100, 20, 100, 15},
	}

	parser := &DiffParser{}

	for _, test := range tests {
		hunk, err := parser.parseHunkHeader(test.line)
		if err != nil {
			t.Fatalf("parseHunkHeader(%s) failed: %v", test.line, err)
		}

		if hunk.OldStart != test.oldStart {
			t.Errorf("OldStart = %d, expected %d", hunk.OldStart, test.oldStart)
		}
		if hunk.OldLines != test.oldLines {
			t.Errorf("OldLines = %d, expected %d", hunk.OldLines, test.oldLines)
		}
		if hunk.NewStart != test.newStart {
			t.Errorf("NewStart = %d, expected %d", hunk.NewStart, test.newStart)
		}
		if hunk.NewLines != test.newLines {
			t.Errorf("NewLines = %d, expected %d", hunk.NewLines, test.newLines)
		}
	}
}

func TestDiffParser_ParseMultiHunkDiff(t *testing.T) {
	diffText := `diff --git a/file.go b/file.go
@@ -10,3 +10,3 @@
-line 1
+line 1 modified
 context
@@ -20,2 +20,2 @@
-line 2
+line 2 modified
`

	parser := &DiffParser{}
	files, err := parser.ParseDiff(diffText)

	if err != nil {
		t.Fatalf("ParseDiff failed: %v", err)
	}

	if len(files) != 1 {
		t.Fatalf("Expected 1 file, got %d", len(files))
	}

	if len(files[0].Hunks) != 2 {
		t.Fatalf("Expected 2 hunks, got %d", len(files[0].Hunks))
	}

	// Verify first hunk
	hunk1 := files[0].Hunks[0]
	if hunk1.OldStart != 10 {
		t.Errorf("Hunk1 OldStart = %d, expected 10", hunk1.OldStart)
	}

	// Verify second hunk
	hunk2 := files[0].Hunks[1]
	if hunk2.OldStart != 20 {
		t.Errorf("Hunk2 OldStart = %d, expected 20", hunk2.OldStart)
	}
}
