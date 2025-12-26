// Package learning implements Ananta's self-healing pattern database and error classification
//
// Pattern Categories: Classification and templates for extracted patterns
// Author: Agent 1.1 (Dr. Yuki Tanaka)
// Created: 2025-11-07
package learning

import "github.com/asymmetrica/urbanlens/pkg/learning/parsers"

// AllCategories returns all pattern categories
func AllCategories() []parsers.PatternCategory {
	return []parsers.PatternCategory{
		parsers.ErrorHandling,
		parsers.CRUDOperations,
		parsers.Testing,
		parsers.Imports,
		parsers.NullSafety,
		parsers.Async,
		parsers.TypeGuards,
		parsers.Logging,
	}
}

// CategoryDescription returns human-readable description
func CategoryDescription(cat parsers.PatternCategory) string {
	descriptions := map[parsers.PatternCategory]string{
		parsers.ErrorHandling:  "Error checking, panic/recover, error wrapping patterns",
		parsers.CRUDOperations: "HTTP handlers, database queries, REST API patterns",
		parsers.Testing:        "Test functions, assertions, test setup/teardown",
		parsers.Imports:        "Common library imports and dependency patterns",
		parsers.NullSafety:     "Null checks, optional chaining, safe navigation",
		parsers.Async:          "Goroutines, channels, async/await, concurrency",
		parsers.TypeGuards:     "Type assertions, interface checks, type safety",
		parsers.Logging:        "Structured logging, log levels, context propagation",
	}
	return descriptions[cat]
}

// IsValidCategory checks if category string is valid
func IsValidCategory(cat string) bool {
	for _, valid := range AllCategories() {
		if string(valid) == cat {
			return true
		}
	}
	return false
}

// ErrorHandling patterns by language
var ErrorHandlingKeywords = map[string][]string{
	"Go": {
		"if err != nil",
		"return err",
		"fmt.Errorf",
		"errors.New",
		"panic(",
		"recover()",
		"defer",
	},
	"TypeScript": {
		"try {",
		"catch (",
		"throw new Error",
		"Promise.reject",
		"?.catch",
	},
	"Python": {
		"try:",
		"except ",
		"raise ",
		"finally:",
		"with ",
	},
	"Rust": {
		"Result<",
		"Option<",
		"unwrap()",
		"expect(",
		"match ",
		"if let Some",
		"if let Err",
		"?",
	},
}

// CRUD operation keywords by language
var CRUDKeywords = map[string][]string{
	"Go": {
		"http.HandleFunc",
		"http.Handler",
		"db.Query",
		"db.Exec",
		"db.QueryRow",
		"r.Get(",
		"r.Post(",
		"r.Put(",
		"r.Delete(",
	},
	"TypeScript": {
		"app.get(",
		"app.post(",
		"router.get(",
		"fetch(",
		"axios.get",
		"prisma.create",
		"prisma.findMany",
	},
	"Python": {
		"@app.route(",
		"@api_view",
		"def get(",
		"def post(",
		"session.query(",
		"db.session.add",
	},
	"Rust": {
		"get(",
		"post(",
		"sqlx::query",
		"query!",
		"execute(",
	},
}

// Testing keywords by language
var TestingKeywords = map[string][]string{
	"Go": {
		"func Test",
		"t.Run(",
		"t.Error(",
		"t.Fatal(",
		"assert.",
		"require.",
	},
	"TypeScript": {
		"describe(",
		"it(",
		"test(",
		"expect(",
		"toBe(",
		"toEqual(",
	},
	"Python": {
		"def test_",
		"class Test",
		"assert ",
		"self.assert",
		"@pytest",
	},
	"Rust": {
		"#[test]",
		"assert_eq!",
		"assert_ne!",
		"assert!",
	},
}

// Async keywords by language
var AsyncKeywords = map[string][]string{
	"Go": {
		"go func(",
		"<-chan",
		"chan<-",
		"select {",
		"goroutine",
	},
	"TypeScript": {
		"async ",
		"await ",
		"Promise<",
		"Promise.all",
		".then(",
	},
	"Python": {
		"async def",
		"await ",
		"asyncio.",
		"async with",
	},
	"Rust": {
		"async fn",
		".await",
		"tokio::",
		"async_trait",
	},
}

// Logging keywords by language
var LoggingKeywords = map[string][]string{
	"Go": {
		"log.Print",
		"log.Fatal",
		"log.Error",
		"logger.Info",
		"slog.",
	},
	"TypeScript": {
		"console.log",
		"logger.info",
		"logger.error",
		"winston.",
	},
	"Python": {
		"logger.info",
		"logger.error",
		"logging.info",
		"print(",
	},
	"Rust": {
		"log::info",
		"log::error",
		"tracing::",
		"println!",
	},
}

// DetectCategory determines pattern category from code snippet
func DetectCategory(code, language string) parsers.PatternCategory {
	// Check error handling first (most specific)
	for _, keyword := range ErrorHandlingKeywords[language] {
		if containsKeyword(code, keyword) {
			return parsers.ErrorHandling
		}
	}

	// Check testing patterns
	for _, keyword := range TestingKeywords[language] {
		if containsKeyword(code, keyword) {
			return parsers.Testing
		}
	}

	// Check CRUD operations
	for _, keyword := range CRUDKeywords[language] {
		if containsKeyword(code, keyword) {
			return parsers.CRUDOperations
		}
	}

	// Check async patterns
	for _, keyword := range AsyncKeywords[language] {
		if containsKeyword(code, keyword) {
			return parsers.Async
		}
	}

	// Check logging
	for _, keyword := range LoggingKeywords[language] {
		if containsKeyword(code, keyword) {
			return parsers.Logging
		}
	}

	// Default: check for imports
	if containsKeyword(code, "import ") || containsKeyword(code, "use ") {
		return parsers.Imports
	}

	// Fallback
	return parsers.ErrorHandling
}

// containsKeyword checks if code contains keyword (case-sensitive)
func containsKeyword(code, keyword string) bool {
	// Simple substring search
	// Could be enhanced with AST-based detection for higher precision
	return len(code) > 0 && len(keyword) > 0 && contains(code, keyword)
}

// contains is a simple helper (avoiding strings import for now)
func contains(s, substr string) bool {
	return len(s) >= len(substr) && findSubstring(s, substr) >= 0
}

// findSubstring returns index of substr in s, or -1 if not found
func findSubstring(s, substr string) int {
	if len(substr) == 0 {
		return 0
	}
	if len(substr) > len(s) {
		return -1
	}

	for i := 0; i <= len(s)-len(substr); i++ {
		match := true
		for j := 0; j < len(substr); j++ {
			if s[i+j] != substr[j] {
				match = false
				break
			}
		}
		if match {
			return i
		}
	}
	return -1
}
