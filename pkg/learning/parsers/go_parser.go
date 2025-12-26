// Package parsers implements language-specific AST parsing for pattern extraction
//
// Go Parser: Extract patterns from Go source code using go/ast
// Author: Agent 1.1 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package parsers

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strings"
)

// GoParser parses Go source files and extracts patterns
type GoParser struct {
	fset *token.FileSet
}

// NewGoParser creates a new Go parser
func NewGoParser() *GoParser {
	return &GoParser{
		fset: token.NewFileSet(),
	}
}

// ParseFile parses a Go source file and returns AST
func (p *GoParser) ParseFile(filePath string) (*ast.File, error) {
	file, err := parser.ParseFile(p.fset, filePath, nil, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("failed to parse %s: %w", filePath, err)
	}
	return file, nil
}

// ExtractPatterns extracts all patterns from a Go file
func (p *GoParser) ExtractPatterns(filePath string) ([]*ExtractedPattern, error) {
	file, err := p.ParseFile(filePath)
	if err != nil {
		return nil, err
	}

	var patterns []*ExtractedPattern

	// Extract error handling patterns
	errorPatterns, err := p.ExtractErrorHandling(file, filePath)
	if err == nil {
		patterns = append(patterns, errorPatterns...)
	}

	// Extract CRUD patterns
	crudPatterns, err := p.ExtractCRUDPatterns(file, filePath)
	if err == nil {
		patterns = append(patterns, crudPatterns...)
	}

	// Extract test patterns
	testPatterns, err := p.ExtractTestPatterns(file, filePath)
	if err == nil {
		patterns = append(patterns, testPatterns...)
	}

	// Extract async patterns
	asyncPatterns, err := p.ExtractAsyncPatterns(file, filePath)
	if err == nil {
		patterns = append(patterns, asyncPatterns...)
	}

	// Extract logging patterns
	loggingPatterns, err := p.ExtractLoggingPatterns(file, filePath)
	if err == nil {
		patterns = append(patterns, loggingPatterns...)
	}

	return patterns, nil
}

// ExtractErrorHandling finds error handling patterns in Go code
func (p *GoParser) ExtractErrorHandling(file *ast.File, filePath string) ([]*ExtractedPattern, error) {
	var patterns []*ExtractedPattern

	ast.Inspect(file, func(n ast.Node) bool {
		// Look for if err != nil blocks
		ifStmt, ok := n.(*ast.IfStmt)
		if !ok {
			return true
		}

		// Check if condition is "err != nil" or "err == nil"
		binExpr, ok := ifStmt.Cond.(*ast.BinaryExpr)
		if !ok {
			return true
		}

		// Check if left side is "err" identifier
		ident, ok := binExpr.X.(*ast.Ident)
		if !ok || ident.Name != "err" {
			return true
		}

		// Check if comparing to nil
		nilIdent, ok := binExpr.Y.(*ast.Ident)
		if !ok || nilIdent.Name != "nil" {
			return true
		}

		// Extract the code for this pattern
		startPos := p.fset.Position(ifStmt.Pos())
		endPos := p.fset.Position(ifStmt.End())

		// Create pattern (we'll read file content to extract actual code)
		pattern := &ExtractedPattern{
			Category:    ErrorHandling,
			Language:    "Go",
			FilePath:    filePath,
			StartLine:   startPos.Line,
			EndLine:     endPos.Line,
			Description: "Go error handling: if err != nil",
			Keywords:    []string{"if", "err", "!=", "nil"},
		}

		patterns = append(patterns, pattern)
		return true
	})

	return patterns, nil
}

// ExtractCRUDPatterns finds HTTP handler and database operation patterns
func (p *GoParser) ExtractCRUDPatterns(file *ast.File, filePath string) ([]*ExtractedPattern, error) {
	var patterns []*ExtractedPattern

	ast.Inspect(file, func(n ast.Node) bool {
		// Look for function declarations
		funcDecl, ok := n.(*ast.FuncDecl)
		if !ok {
			return true
		}

		// Check if function signature matches HTTP handler pattern
		// func(w http.ResponseWriter, r *http.Request)
		if funcDecl.Type != nil && funcDecl.Type.Params != nil {
			params := funcDecl.Type.Params.List
			if len(params) >= 2 {
				// Check for http.ResponseWriter and *http.Request
				firstParam := formatType(params[0].Type)
				secondParam := formatType(params[1].Type)

				if strings.Contains(firstParam, "ResponseWriter") && strings.Contains(secondParam, "Request") {
					startPos := p.fset.Position(funcDecl.Pos())
					endPos := p.fset.Position(funcDecl.End())

					pattern := &ExtractedPattern{
						Category:    CRUDOperations,
						Language:    "Go",
						FilePath:    filePath,
						StartLine:   startPos.Line,
						EndLine:     endPos.Line,
						Description: "Go HTTP handler function",
						Keywords:    []string{"http", "Handler", "ResponseWriter", "Request"},
					}
					patterns = append(patterns, pattern)
				}
			}
		}

		return true
	})

	return patterns, nil
}

// ExtractTestPatterns finds test function patterns
func (p *GoParser) ExtractTestPatterns(file *ast.File, filePath string) ([]*ExtractedPattern, error) {
	var patterns []*ExtractedPattern

	ast.Inspect(file, func(n ast.Node) bool {
		funcDecl, ok := n.(*ast.FuncDecl)
		if !ok {
			return true
		}

		// Check if function name starts with "Test"
		if !strings.HasPrefix(funcDecl.Name.Name, "Test") {
			return true
		}

		// Check if it takes *testing.T parameter
		if funcDecl.Type == nil || funcDecl.Type.Params == nil || len(funcDecl.Type.Params.List) == 0 {
			return true
		}

		firstParam := formatType(funcDecl.Type.Params.List[0].Type)
		if strings.Contains(firstParam, "testing.T") {
			startPos := p.fset.Position(funcDecl.Pos())
			endPos := p.fset.Position(funcDecl.End())

			pattern := &ExtractedPattern{
				Category:    Testing,
				Language:    "Go",
				FilePath:    filePath,
				StartLine:   startPos.Line,
				EndLine:     endPos.Line,
				Description: "Go test function",
				Keywords:    []string{"Test", "testing.T"},
			}
			patterns = append(patterns, pattern)
		}

		return true
	})

	return patterns, nil
}

// ExtractAsyncPatterns finds goroutine and channel patterns
func (p *GoParser) ExtractAsyncPatterns(file *ast.File, filePath string) ([]*ExtractedPattern, error) {
	var patterns []*ExtractedPattern

	ast.Inspect(file, func(n ast.Node) bool {
		// Look for go statements
		goStmt, ok := n.(*ast.GoStmt)
		if ok {
			startPos := p.fset.Position(goStmt.Pos())
			endPos := p.fset.Position(goStmt.End())

			pattern := &ExtractedPattern{
				Category:    Async,
				Language:    "Go",
				FilePath:    filePath,
				StartLine:   startPos.Line,
				EndLine:     endPos.Line,
				Description: "Go goroutine launch",
				Keywords:    []string{"go", "goroutine"},
			}
			patterns = append(patterns, pattern)
		}

		// Look for select statements (channel operations)
		selectStmt, ok := n.(*ast.SelectStmt)
		if ok {
			startPos := p.fset.Position(selectStmt.Pos())
			endPos := p.fset.Position(selectStmt.End())

			pattern := &ExtractedPattern{
				Category:    Async,
				Language:    "Go",
				FilePath:    filePath,
				StartLine:   startPos.Line,
				EndLine:     endPos.Line,
				Description: "Go select statement for channels",
				Keywords:    []string{"select", "chan"},
			}
			patterns = append(patterns, pattern)
		}

		return true
	})

	return patterns, nil
}

// ExtractLoggingPatterns finds logging call patterns
func (p *GoParser) ExtractLoggingPatterns(file *ast.File, filePath string) ([]*ExtractedPattern, error) {
	var patterns []*ExtractedPattern

	ast.Inspect(file, func(n ast.Node) bool {
		// Look for function calls
		callExpr, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}

		// Check if it's a logging function
		funName := formatExpr(callExpr.Fun)
		loggingFunctions := []string{
			"log.Print", "log.Printf", "log.Fatal", "log.Error",
			"logger.Info", "logger.Error", "logger.Debug", "logger.Warn",
			"slog.Info", "slog.Error", "slog.Debug",
		}

		for _, logFunc := range loggingFunctions {
			if strings.Contains(funName, logFunc) {
				startPos := p.fset.Position(callExpr.Pos())
				endPos := p.fset.Position(callExpr.End())

				pattern := &ExtractedPattern{
					Category:    Logging,
					Language:    "Go",
					FilePath:    filePath,
					StartLine:   startPos.Line,
					EndLine:     endPos.Line,
					Description: "Go logging call",
					Keywords:    []string{"log", "logger", "slog"},
				}
				patterns = append(patterns, pattern)
				break
			}
		}

		return true
	})

	return patterns, nil
}

// formatType converts ast.Expr to string representation
func formatType(expr ast.Expr) string {
	switch t := expr.(type) {
	case *ast.Ident:
		return t.Name
	case *ast.SelectorExpr:
		return formatExpr(t.X) + "." + t.Sel.Name
	case *ast.StarExpr:
		return "*" + formatType(t.X)
	default:
		return ""
	}
}

// formatExpr converts ast.Expr to string
func formatExpr(expr ast.Expr) string {
	switch e := expr.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.SelectorExpr:
		return formatExpr(e.X) + "." + e.Sel.Name
	default:
		return ""
	}
}
