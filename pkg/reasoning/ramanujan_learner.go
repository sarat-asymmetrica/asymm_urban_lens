package reasoning

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"time"
)

// RamanujanFormula represents a mathematical formula extracted from Ramanujan's work
type RamanujanFormula struct {
	ID              string                 `json:"id"`
	Source          string                 `json:"source"`
	Page            int                    `json:"page"`
	Type            string                 `json:"type"` // continued_fraction, infinite_series, modular_form, etc
	LaTeX           string                 `json:"latex"`
	PlainText       string                 `json:"plain_text"`
	Variables       []string               `json:"variables"`
	Constants       []float64              `json:"constants"`
	Context         string                 `json:"context"`
	RamanujanNotes  string                 `json:"ramanujan_notes"`
	ThoughtPattern  string                 `json:"thought_pattern"`
	Metadata        map[string]interface{} `json:"metadata"`
	ExtractedAt     time.Time              `json:"extracted_at"`
}

// NotationPattern represents Ramanujan's unique notation style
type NotationPattern struct {
	Pattern     string   `json:"pattern"`
	Meaning     string   `json:"meaning"`
	Examples    []string `json:"examples"`
	Frequency   int      `json:"frequency"`
	Contexts    []string `json:"contexts"`
}

// ThoughtSignature captures Ramanujan's thinking patterns
type ThoughtSignature struct {
	Type        string   `json:"type"` // intuitive_leap, pattern_recognition, divine_inspiration
	Indicators  []string `json:"indicators"`
	Examples    []string `json:"examples"`
	Confidence  float64  `json:"confidence"`
}

// RamanujanLearner processes and learns from Ramanujan's mathematical works
type RamanujanLearner struct {
	formulas         []RamanujanFormula
	notations        map[string]*NotationPattern
	thoughtPatterns  []ThoughtSignature
	bookPaths        []string
	outputDir        string
	tesseractPath    string
	mu               sync.RWMutex
	logger           *log.Logger

	// Pattern recognition
	continuedFractionRegex *regexp.Regexp
	infiniteSeriesRegex    *regexp.Regexp
	modularFormRegex       *regexp.Regexp
	partitionRegex         *regexp.Regexp
	thetaFunctionRegex     *regexp.Regexp

	// Extraction statistics
	totalPages       int
	processedPages   int
	formulasFound    int
	patternsDetected int
	errors           []error
}

// NewRamanujanLearner creates a new learner instance
func NewRamanujanLearner(outputDir string) *RamanujanLearner {
	return &RamanujanLearner{
		formulas:        make([]RamanujanFormula, 0),
		notations:       make(map[string]*NotationPattern),
		thoughtPatterns: make([]ThoughtSignature, 0),
		outputDir:       outputDir,
		tesseractPath:   "tesseract", // Assumes tesseract is in PATH
		logger:          log.New(os.Stdout, "[RAMANUJAN_LEARNER] ", log.LstdFlags),

		// Initialize regex patterns for formula detection
		continuedFractionRegex: regexp.MustCompile(`\d+\s*/\s*\(\s*\d+\s*\+\s*.*\)`),
		infiniteSeriesRegex:    regexp.MustCompile(`\sum|∑|\s+\+\s+\.\.\.\s+`),
		modularFormRegex:       regexp.MustCompile(`q\^|τ|eta|η|modular`),
		partitionRegex:         regexp.MustCompile(`p\(\d+\)|partition|P\(\d+\)`),
		thetaFunctionRegex:     regexp.MustCompile(`θ|theta|ϑ|vartheta`),
	}
}

// ProcessBook processes a single Ramanujan book
func (rl *RamanujanLearner) ProcessBook(bookPath string) error {
	rl.logger.Printf("Processing book: %s", filepath.Base(bookPath))

	// Convert PDF to images for OCR
	imageDir, err := rl.convertPDFToImages(bookPath)
	if err != nil {
		return fmt.Errorf("failed to convert PDF to images: %v", err)
	}
	defer os.RemoveAll(imageDir) // Clean up temp images

	// Process each page
	images, err := filepath.Glob(filepath.Join(imageDir, "*.png"))
	if err != nil {
		return fmt.Errorf("failed to list images: %v", err)
	}

	rl.mu.Lock()
	rl.totalPages += len(images)
	rl.mu.Unlock()

	// Process pages in parallel (but controlled)
	sem := make(chan struct{}, 4) // Process 4 pages concurrently
	var wg sync.WaitGroup

	for i, imagePath := range images {
		wg.Add(1)
		go func(img string, pageNum int) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()

			if err := rl.processPage(img, filepath.Base(bookPath), pageNum+1); err != nil {
				rl.logger.Printf("Error processing page %d: %v", pageNum+1, err)
				rl.mu.Lock()
				rl.errors = append(rl.errors, err)
				rl.mu.Unlock()
			}

			rl.mu.Lock()
			rl.processedPages++
			if rl.processedPages%10 == 0 {
				rl.logger.Printf("Progress: %d/%d pages processed", rl.processedPages, rl.totalPages)
			}
			rl.mu.Unlock()
		}(imagePath, i)
	}

	wg.Wait()

	rl.logger.Printf("Completed processing book: %s (%d formulas found)",
		filepath.Base(bookPath), rl.formulasFound)

	return nil
}

// convertPDFToImages converts PDF pages to PNG images for OCR
func (rl *RamanujanLearner) convertPDFToImages(pdfPath string) (string, error) {
	// Create temporary directory for images
	tempDir, err := os.MkdirTemp("", "ramanujan_ocr_*")
	if err != nil {
		return "", err
	}

	// Try pdftoppm first (fastest, best quality)
	cmd := exec.Command("pdftoppm",
		"-png",
		"-r", "300", // 300 DPI for mathematical symbols
		pdfPath,
		filepath.Join(tempDir, "page"))

	if err := cmd.Run(); err != nil {
		// Fallback to ImageMagick if pdftoppm not available
		cmd = exec.Command("magick",
			"convert",
			"-density", "300",
			pdfPath,
			filepath.Join(tempDir, "page-%04d.png"))

		if err := cmd.Run(); err != nil {
			// Final fallback: Use Python pdf2image
			pythonScript := filepath.Join(filepath.Dir(os.Args[0]), "convert_pdf.py")
			cmd = exec.Command("python", pythonScript, pdfPath, tempDir)
			output, pyErr := cmd.CombinedOutput()
			if pyErr != nil {
				return "", fmt.Errorf("failed to convert PDF to images (tried pdftoppm, magick, python): %v\nPython output: %s", pyErr, string(output))
			}
			rl.logger.Printf("Used Python pdf2image for conversion")
		} else {
			rl.logger.Printf("Used ImageMagick for conversion")
		}
	} else {
		rl.logger.Printf("Used pdftoppm for conversion")
	}

	return tempDir, nil
}

// processPage performs OCR and formula extraction on a single page
func (rl *RamanujanLearner) processPage(imagePath, source string, pageNum int) error {
	// Run Tesseract OCR with math-specific configuration
	text, err := rl.runTesseract(imagePath)
	if err != nil {
		return fmt.Errorf("OCR failed for page %d: %v", pageNum, err)
	}

	// Extract formulas from OCR text
	formulas := rl.extractFormulas(text, source, pageNum)

	// Detect notation patterns
	rl.detectNotationPatterns(text)

	// Analyze thought patterns
	rl.analyzeThoughtPatterns(text)

	// Store extracted formulas
	rl.mu.Lock()
	rl.formulas = append(rl.formulas, formulas...)
	rl.formulasFound += len(formulas)
	rl.mu.Unlock()

	return nil
}

// runTesseract performs OCR using Python pytesseract wrapper
// (Same approach as Books 2 & 3 - works reliably across all platforms)
func (rl *RamanujanLearner) runTesseract(imagePath string) (string, error) {
	// Use Python script approach (proven to work with pytesseract)
	pythonScript := filepath.Join(filepath.Dir(os.Args[0]), "ocr_page.py")

	cmd := exec.Command("python", pythonScript, imagePath)

	output, err := cmd.Output()
	if err != nil {
		// Provide more context in error
		stderr := ""
		if exitErr, ok := err.(*exec.ExitError); ok {
			stderr = string(exitErr.Stderr)
		}
		return "", fmt.Errorf("OCR command failed for %s: %v\nStderr: %s", imagePath, err, stderr)
	}

	return string(output), nil
}

// extractFormulas identifies and extracts mathematical formulas
func (rl *RamanujanLearner) extractFormulas(text, source string, pageNum int) []RamanujanFormula {
	formulas := make([]RamanujanFormula, 0)
	lines := strings.Split(text, "\n")

	for i, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		// Check for various formula types
		formulaType := rl.detectFormulaType(line)
		if formulaType == "" {
			continue
		}

		// Create formula object
		formula := RamanujanFormula{
			ID:          fmt.Sprintf("%s_p%d_l%d", source, pageNum, i),
			Source:      source,
			Page:        pageNum,
			Type:        formulaType,
			PlainText:   line,
			LaTeX:       rl.convertToLaTeX(line),
			Variables:   rl.extractVariables(line),
			Constants:   rl.extractConstants(line),
			Context:     rl.extractContext(lines, i),
			ExtractedAt: time.Now(),
			Metadata:    make(map[string]interface{}),
		}

		// Detect Ramanujan's notes or comments
		if i > 0 && strings.Contains(strings.ToLower(lines[i-1]), "note") {
			formula.RamanujanNotes = lines[i-1]
		}

		// Detect thought patterns
		formula.ThoughtPattern = rl.detectThoughtPattern(line, formula.Context)

		formulas = append(formulas, formula)
	}

	return formulas
}

// detectFormulaType determines the type of mathematical formula
func (rl *RamanujanLearner) detectFormulaType(text string) string {
	if rl.continuedFractionRegex.MatchString(text) {
		return "continued_fraction"
	}
	if rl.infiniteSeriesRegex.MatchString(text) {
		return "infinite_series"
	}
	if rl.modularFormRegex.MatchString(text) {
		return "modular_form"
	}
	if rl.partitionRegex.MatchString(text) {
		return "partition_function"
	}
	if rl.thetaFunctionRegex.MatchString(text) {
		return "theta_function"
	}

	// Check for equations (contains = sign with math symbols)
	if strings.Contains(text, "=") && containsMathSymbols(text) {
		return "equation"
	}

	return ""
}

// convertToLaTeX converts plain text formula to LaTeX
func (rl *RamanujanLearner) convertToLaTeX(text string) string {
	latex := text

	// Basic conversions
	replacements := map[string]string{
		"sum":      "\\sum",
		"Sum":      "\\sum",
		"prod":     "\\prod",
		"sqrt":     "\\sqrt",
		"infinity": "\\infty",
		"inf":      "\\infty",
		"pi":       "\\pi",
		"theta":    "\\theta",
		"phi":      "\\phi",
		"tau":      "\\tau",
		"eta":      "\\eta",
		"<=":       "\\leq",
		">=":       "\\geq",
		"!=":       "\\neq",
		"...":      "\\dots",
	}

	for old, new := range replacements {
		latex = strings.ReplaceAll(latex, old, new)
	}

	// Handle fractions
	fractionRegex := regexp.MustCompile(`(\d+)\s*/\s*(\d+)`)
	latex = fractionRegex.ReplaceAllString(latex, "\\frac{$1}{$2}")

	// Handle superscripts
	superscriptRegex := regexp.MustCompile(`\^(\d+|\w)`)
	latex = superscriptRegex.ReplaceAllString(latex, "^{$1}")

	// Handle subscripts
	subscriptRegex := regexp.MustCompile(`_(\d+|\w)`)
	latex = subscriptRegex.ReplaceAllString(latex, "_{$1}")

	return latex
}

// extractVariables identifies variables in the formula
func (rl *RamanujanLearner) extractVariables(text string) []string {
	variableRegex := regexp.MustCompile(`\b[a-zA-Z]\b`)
	matches := variableRegex.FindAllString(text, -1)

	// Deduplicate
	seen := make(map[string]bool)
	vars := make([]string, 0)
	for _, v := range matches {
		if !seen[v] {
			seen[v] = true
			vars = append(vars, v)
		}
	}

	return vars
}

// extractConstants identifies numerical constants in the formula
func (rl *RamanujanLearner) extractConstants(text string) []float64 {
	constantRegex := regexp.MustCompile(`\b\d+\.?\d*\b`)
	matches := constantRegex.FindAllString(text, -1)

	constants := make([]float64, 0)
	for _, m := range matches {
		if val, err := parseFloat(m); err == nil {
			constants = append(constants, val)
		}
	}

	return constants
}

// extractContext gets surrounding context for a formula
func (rl *RamanujanLearner) extractContext(lines []string, index int) string {
	context := ""

	// Get 2 lines before and after
	start := max(0, index-2)
	end := min(len(lines), index+3)

	contextLines := lines[start:end]
	context = strings.Join(contextLines, " ")

	return strings.TrimSpace(context)
}

// detectThoughtPattern identifies Ramanujan's thinking patterns
func (rl *RamanujanLearner) detectThoughtPattern(formula, context string) string {
	contextLower := strings.ToLower(context)

	// Intuitive leap indicators
	if strings.Contains(contextLower, "it is clear") ||
		strings.Contains(contextLower, "obviously") ||
		strings.Contains(contextLower, "we have") ||
		strings.Contains(contextLower, "hence") {
		return "intuitive_leap"
	}

	// Divine inspiration indicators
	if strings.Contains(contextLower, "goddess") ||
		strings.Contains(contextLower, "namagiri") ||
		strings.Contains(contextLower, "dream") ||
		strings.Contains(contextLower, "revealed") {
		return "divine_inspiration"
	}

	// Pattern recognition indicators
	if strings.Contains(contextLower, "pattern") ||
		strings.Contains(contextLower, "observe") ||
		strings.Contains(contextLower, "notice") ||
		strings.Contains(contextLower, "similar") {
		return "pattern_recognition"
	}

	// Empirical discovery
	if strings.Contains(contextLower, "found") ||
		strings.Contains(contextLower, "discovered") ||
		strings.Contains(contextLower, "computed") ||
		strings.Contains(contextLower, "calculated") {
		return "empirical_discovery"
	}

	// Generalization
	if strings.Contains(contextLower, "general") ||
		strings.Contains(contextLower, "extends") ||
		strings.Contains(contextLower, "follows from") {
		return "generalization"
	}

	return "unknown"
}

// detectNotationPatterns identifies unique notation patterns
func (rl *RamanujanLearner) detectNotationPatterns(text string) {
	// Look for repeated unusual notations
	notationRegex := regexp.MustCompile(`[^\s\w]{2,}|\b\w+\([^)]+\)|\w+_\w+`)
	matches := notationRegex.FindAllString(text, -1)

	rl.mu.Lock()
	defer rl.mu.Unlock()

	for _, match := range matches {
		if pattern, exists := rl.notations[match]; exists {
			pattern.Frequency++
		} else {
			rl.notations[match] = &NotationPattern{
				Pattern:   match,
				Frequency: 1,
				Examples:  []string{text},
			}
		}
	}
}

// analyzeThoughtPatterns detects and categorizes thought patterns
func (rl *RamanujanLearner) analyzeThoughtPatterns(text string) {
	// This would be expanded with more sophisticated NLP
	// For now, basic keyword detection

	indicators := map[string][]string{
		"intuitive_leap": {
			"suddenly", "clearly", "obviously", "must be", "it follows",
		},
		"pattern_recognition": {
			"pattern", "similar", "like", "resembles", "analogy",
		},
		"divine_inspiration": {
			"goddess", "dream", "vision", "revealed", "shown",
		},
		"empirical_testing": {
			"tested", "verified", "computed", "calculated", "checked",
		},
	}

	textLower := strings.ToLower(text)

	for patternType, keywords := range indicators {
		for _, keyword := range keywords {
			if strings.Contains(textLower, keyword) {
				// Update or create thought signature
				rl.updateThoughtSignature(patternType, text)
				break
			}
		}
	}
}

// updateThoughtSignature updates the thought pattern database
func (rl *RamanujanLearner) updateThoughtSignature(patternType, example string) {
	rl.mu.Lock()
	defer rl.mu.Unlock()

	// Find existing signature or create new one
	var signature *ThoughtSignature
	for i := range rl.thoughtPatterns {
		if rl.thoughtPatterns[i].Type == patternType {
			signature = &rl.thoughtPatterns[i]
			break
		}
	}

	if signature == nil {
		rl.thoughtPatterns = append(rl.thoughtPatterns, ThoughtSignature{
			Type:     patternType,
			Examples: []string{example},
		})
	} else {
		signature.Examples = append(signature.Examples, example)
		signature.Confidence = float64(len(signature.Examples)) / 100.0 // Simple confidence metric
		if signature.Confidence > 1.0 {
			signature.Confidence = 1.0
		}
	}
}

// SaveResults saves all extracted data to files
func (rl *RamanujanLearner) SaveResults() error {
	// Create output directory structure
	dirs := []string{
		filepath.Join(rl.outputDir, "formulas_extracted"),
		filepath.Join(rl.outputDir, "thought_patterns"),
		filepath.Join(rl.outputDir, "notation_analysis"),
	}

	for _, dir := range dirs {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return err
		}
	}

	// Save formulas by type
	formulasByType := rl.categorizeFormulas()
	for formulaType, formulas := range formulasByType {
		filename := filepath.Join(rl.outputDir, "formulas_extracted",
			fmt.Sprintf("%s.json", formulaType))
		if err := rl.saveJSON(filename, formulas); err != nil {
			return err
		}
	}

	// Save thought patterns
	thoughtFile := filepath.Join(rl.outputDir, "thought_patterns", "patterns.json")
	if err := rl.saveJSON(thoughtFile, rl.thoughtPatterns); err != nil {
		return err
	}

	// Save notation analysis
	notationFile := filepath.Join(rl.outputDir, "notation_analysis", "notations.json")
	if err := rl.saveJSON(notationFile, rl.notations); err != nil {
		return err
	}

	// Generate summary report
	if err := rl.generateSummaryReport(); err != nil {
		return err
	}

	rl.logger.Printf("Results saved to %s", rl.outputDir)
	return nil
}

// categorizeFormulas groups formulas by type
func (rl *RamanujanLearner) categorizeFormulas() map[string][]RamanujanFormula {
	categories := make(map[string][]RamanujanFormula)

	for _, formula := range rl.formulas {
		if _, exists := categories[formula.Type]; !exists {
			categories[formula.Type] = make([]RamanujanFormula, 0)
		}
		categories[formula.Type] = append(categories[formula.Type], formula)
	}

	return categories
}

// saveJSON saves data to JSON file
func (rl *RamanujanLearner) saveJSON(filename string, data interface{}) error {
	file, err := os.Create(filename)
	if err != nil {
		return err
	}
	defer file.Close()

	encoder := json.NewEncoder(file)
	encoder.SetIndent("", "  ")
	return encoder.Encode(data)
}

// generateSummaryReport creates a comprehensive summary
func (rl *RamanujanLearner) generateSummaryReport() error {
	report := fmt.Sprintf(`# Ramanujan Knowledge Extraction Report

## Summary Statistics
- Total Pages Processed: %d
- Total Formulas Extracted: %d
- Unique Notation Patterns: %d
- Thought Pattern Types: %d
- Processing Errors: %d

## Formula Distribution
`, rl.processedPages, rl.formulasFound, len(rl.notations),
		len(rl.thoughtPatterns), len(rl.errors))

	// Add formula type distribution
	formulasByType := rl.categorizeFormulas()
	for formulaType, formulas := range formulasByType {
		report += fmt.Sprintf("- %s: %d formulas\n", formulaType, len(formulas))
	}

	// Add thought pattern analysis
	report += "\n## Thought Pattern Analysis\n"
	for _, pattern := range rl.thoughtPatterns {
		report += fmt.Sprintf("- %s: %.2f confidence (%d examples)\n",
			pattern.Type, pattern.Confidence, len(pattern.Examples))
	}

	// Add top notation patterns
	report += "\n## Most Frequent Notation Patterns\n"
	// Would sort and display top patterns here

	// Save report
	reportFile := filepath.Join(rl.outputDir, "extraction_summary.md")
	return os.WriteFile(reportFile, []byte(report), 0644)
}

// Helper functions

func containsMathSymbols(text string) bool {
	mathSymbols := []string{"+", "-", "*", "/", "^", "=", "<", ">",
		"π", "φ", "θ", "Σ", "∑", "∏", "∫", "√"}
	for _, symbol := range mathSymbols {
		if strings.Contains(text, symbol) {
			return true
		}
	}
	return false
}

func parseFloat(s string) (float64, error) {
	var f float64
	_, err := fmt.Sscanf(s, "%f", &f)
	return f, err
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}