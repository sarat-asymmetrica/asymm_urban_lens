// Package urban provides pandoc integration for document conversion
// Supports conversion between PDF, DOCX, HTML, Markdown, LaTeX, etc.
package urban

import (
	"bytes"
	"fmt"
	"os/exec"
	"path/filepath"
	"strings"
)

// PandocConverter handles document format conversion via pandoc
type PandocConverter struct {
	Available bool
	Version   string
}

// NewPandocConverter creates a new pandoc converter and checks availability
func NewPandocConverter() *PandocConverter {
	pc := &PandocConverter{}
	pc.checkAvailability()
	return pc
}

// checkAvailability checks if pandoc is installed
func (p *PandocConverter) checkAvailability() {
	cmd := exec.Command("pandoc", "--version")
	output, err := cmd.Output()
	if err != nil {
		p.Available = false
		return
	}
	p.Available = true
	lines := strings.Split(string(output), "\n")
	if len(lines) > 0 {
		p.Version = strings.TrimSpace(lines[0])
	}
}

// SupportedFormats returns list of supported input/output formats
func (p *PandocConverter) SupportedFormats() map[string][]string {
	return map[string][]string{
		"input": {
			"markdown", "md", "html", "htm", "docx", "odt", "rtf",
			"latex", "tex", "rst", "org", "epub", "json", "csv",
		},
		"output": {
			"markdown", "md", "html", "docx", "odt", "rtf", "pdf",
			"latex", "tex", "rst", "org", "epub", "json", "plain",
		},
	}
}

// ConversionRequest represents a document conversion request
type ConversionRequest struct {
	InputPath    string
	InputFormat  string // Auto-detected if empty
	OutputFormat string
	OutputPath   string // Auto-generated if empty
	Options      ConversionOptions
}

// ConversionOptions holds pandoc conversion options
type ConversionOptions struct {
	Standalone      bool   // Produce standalone document
	TableOfContents bool   // Include table of contents
	NumberSections  bool   // Number sections
	Template        string // Custom template path
	CSSPath         string // CSS for HTML output
	Metadata        map[string]string
}

// ConversionResult represents the result of a conversion
type ConversionResult struct {
	Success      bool
	InputPath    string
	OutputPath   string
	InputFormat  string
	OutputFormat string
	BytesWritten int64
	Error        string
}

// Convert converts a document from one format to another
func (p *PandocConverter) Convert(req ConversionRequest) (*ConversionResult, error) {
	if !p.Available {
		return nil, fmt.Errorf("pandoc is not installed. Install from https://pandoc.org/installing.html")
	}

	// Auto-detect input format from extension
	if req.InputFormat == "" {
		req.InputFormat = p.detectFormat(req.InputPath)
	}

	// Generate output path if not provided
	if req.OutputPath == "" {
		ext := p.formatToExtension(req.OutputFormat)
		base := strings.TrimSuffix(req.InputPath, filepath.Ext(req.InputPath))
		req.OutputPath = base + ext
	}

	// Build pandoc command
	args := []string{
		req.InputPath,
		"-f", req.InputFormat,
		"-t", req.OutputFormat,
		"-o", req.OutputPath,
	}

	// Add options
	if req.Options.Standalone {
		args = append(args, "--standalone")
	}
	if req.Options.TableOfContents {
		args = append(args, "--toc")
	}
	if req.Options.NumberSections {
		args = append(args, "--number-sections")
	}
	if req.Options.Template != "" {
		args = append(args, "--template", req.Options.Template)
	}
	if req.Options.CSSPath != "" {
		args = append(args, "--css", req.Options.CSSPath)
	}
	for key, value := range req.Options.Metadata {
		args = append(args, "-M", fmt.Sprintf("%s=%s", key, value))
	}

	// Execute pandoc
	cmd := exec.Command("pandoc", args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err := cmd.Run()
	if err != nil {
		return &ConversionResult{
			Success:      false,
			InputPath:    req.InputPath,
			OutputPath:   req.OutputPath,
			InputFormat:  req.InputFormat,
			OutputFormat: req.OutputFormat,
			Error:        stderr.String(),
		}, fmt.Errorf("pandoc conversion failed: %s", stderr.String())
	}

	return &ConversionResult{
		Success:      true,
		InputPath:    req.InputPath,
		OutputPath:   req.OutputPath,
		InputFormat:  req.InputFormat,
		OutputFormat: req.OutputFormat,
	}, nil
}

// ConvertString converts a string from one format to another
func (p *PandocConverter) ConvertString(content, inputFormat, outputFormat string) (string, error) {
	if !p.Available {
		return "", fmt.Errorf("pandoc is not installed")
	}

	args := []string{
		"-f", inputFormat,
		"-t", outputFormat,
	}

	cmd := exec.Command("pandoc", args...)
	cmd.Stdin = strings.NewReader(content)

	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	err := cmd.Run()
	if err != nil {
		return "", fmt.Errorf("pandoc conversion failed: %s", stderr.String())
	}

	return stdout.String(), nil
}

// MarkdownToHTML converts markdown to HTML
func (p *PandocConverter) MarkdownToHTML(markdown string) (string, error) {
	return p.ConvertString(markdown, "markdown", "html")
}

// HTMLToMarkdown converts HTML to markdown
func (p *PandocConverter) HTMLToMarkdown(html string) (string, error) {
	return p.ConvertString(html, "html", "markdown")
}

// MarkdownToDocx converts markdown file to DOCX
func (p *PandocConverter) MarkdownToDocx(inputPath, outputPath string) (*ConversionResult, error) {
	return p.Convert(ConversionRequest{
		InputPath:    inputPath,
		InputFormat:  "markdown",
		OutputFormat: "docx",
		OutputPath:   outputPath,
		Options: ConversionOptions{
			Standalone: true,
		},
	})
}

// DocxToMarkdown converts DOCX file to markdown
func (p *PandocConverter) DocxToMarkdown(inputPath, outputPath string) (*ConversionResult, error) {
	return p.Convert(ConversionRequest{
		InputPath:    inputPath,
		InputFormat:  "docx",
		OutputFormat: "markdown",
		OutputPath:   outputPath,
	})
}

// detectFormat detects format from file extension
func (p *PandocConverter) detectFormat(path string) string {
	ext := strings.ToLower(filepath.Ext(path))
	formats := map[string]string{
		".md":       "markdown",
		".markdown": "markdown",
		".html":     "html",
		".htm":      "html",
		".docx":     "docx",
		".odt":      "odt",
		".rtf":      "rtf",
		".tex":      "latex",
		".latex":    "latex",
		".rst":      "rst",
		".org":      "org",
		".epub":     "epub",
		".json":     "json",
		".csv":      "csv",
		".txt":      "plain",
	}
	if format, ok := formats[ext]; ok {
		return format
	}
	return "markdown" // Default
}

// formatToExtension returns file extension for format
func (p *PandocConverter) formatToExtension(format string) string {
	extensions := map[string]string{
		"markdown": ".md",
		"html":     ".html",
		"docx":     ".docx",
		"odt":      ".odt",
		"rtf":      ".rtf",
		"pdf":      ".pdf",
		"latex":    ".tex",
		"rst":      ".rst",
		"org":      ".org",
		"epub":     ".epub",
		"json":     ".json",
		"plain":    ".txt",
	}
	if ext, ok := extensions[format]; ok {
		return ext
	}
	return ".txt"
}

// GetStatus returns pandoc availability status
func (p *PandocConverter) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available": p.Available,
		"version":   p.Version,
		"formats":   p.SupportedFormats(),
	}
}
