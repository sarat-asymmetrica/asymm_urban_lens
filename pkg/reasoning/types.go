package reasoning

// CompilationError represents a compilation error found during verification
type CompilationError struct {
	FilePath     string // File where error occurred
	LineNumber   int    // Line number (1-indexed)
	Column       int    // Column number (1-indexed)
	ErrorMessage string // Full error message
	ErrorType    string // Type of error (compile, runtime, etc)
}
