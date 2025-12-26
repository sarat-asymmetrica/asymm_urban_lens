// Package media - Document Processing Pipeline
// Unified interface for document and media transformations
package media

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/asymmetrica/urbanlens/pkg/urban"
)

// DocumentPipeline provides unified document/media processing
type DocumentPipeline struct {
	Pandoc *urban.PandocConverter
	FFmpeg *FFmpegProcessor
}

// NewDocumentPipeline creates a new document processing pipeline
func NewDocumentPipeline() *DocumentPipeline {
	return &DocumentPipeline{
		Pandoc: urban.NewPandocConverter(),
		FFmpeg: NewFFmpegProcessor(),
	}
}

// PipelineStatus returns status of all processing tools
type PipelineStatus struct {
	Pandoc struct {
		Available bool   `json:"available"`
		Version   string `json:"version"`
	} `json:"pandoc"`
	FFmpeg struct {
		Available bool   `json:"available"`
		Version   string `json:"version"`
	} `json:"ffmpeg"`
	Capabilities []string `json:"capabilities"`
}

// GetStatus returns the status of all pipeline components
func (p *DocumentPipeline) GetStatus() *PipelineStatus {
	status := &PipelineStatus{}

	status.Pandoc.Available = p.Pandoc.Available
	status.Pandoc.Version = p.Pandoc.Version

	status.FFmpeg.Available = p.FFmpeg.Available
	status.FFmpeg.Version = p.FFmpeg.Version

	// Build capabilities list
	caps := []string{}
	if p.Pandoc.Available {
		caps = append(caps,
			"markdown_to_html",
			"markdown_to_docx",
			"markdown_to_pdf",
			"docx_to_markdown",
			"html_to_markdown",
			"latex_to_pdf",
		)
	}
	if p.FFmpeg.Available {
		caps = append(caps,
			"video_to_audio",
			"audio_transcription_prep",
			"audio_format_conversion",
			"video_trimming",
			"media_compression",
		)
	}
	status.Capabilities = caps

	return status
}

// ProcessRequest represents a unified processing request
type ProcessRequest struct {
	InputPath  string                 `json:"input_path"`
	OutputPath string                 `json:"output_path,omitempty"`
	Operation  string                 `json:"operation"`
	Options    map[string]interface{} `json:"options,omitempty"`
}

// ProcessResult represents a unified processing result
type ProcessResult struct {
	Success    bool   `json:"success"`
	InputPath  string `json:"input_path"`
	OutputPath string `json:"output_path"`
	Operation  string `json:"operation"`
	Message    string `json:"message,omitempty"`
	Error      string `json:"error,omitempty"`
}

// Process handles a unified processing request
func (p *DocumentPipeline) Process(req ProcessRequest) (*ProcessResult, error) {
	switch req.Operation {
	// Document operations (Pandoc)
	case "markdown_to_html":
		return p.markdownToHTML(req)
	case "markdown_to_docx":
		return p.markdownToDocx(req)
	case "docx_to_markdown":
		return p.docxToMarkdown(req)
	case "html_to_markdown":
		return p.htmlToMarkdown(req)
	case "convert_document":
		return p.convertDocument(req)

	// Media operations (FFmpeg)
	case "extract_audio":
		return p.extractAudio(req)
	case "prepare_transcription":
		return p.prepareTranscription(req)
	case "convert_audio":
		return p.convertAudio(req)
	case "trim_media":
		return p.trimMedia(req)

	default:
		return nil, fmt.Errorf("unknown operation: %s", req.Operation)
	}
}

// Document operations

func (p *DocumentPipeline) markdownToHTML(req ProcessRequest) (*ProcessResult, error) {
	if !p.Pandoc.Available {
		return nil, fmt.Errorf("pandoc not available")
	}

	result, err := p.Pandoc.Convert(urban.ConversionRequest{
		InputPath:    req.InputPath,
		OutputPath:   req.OutputPath,
		InputFormat:  "markdown",
		OutputFormat: "html",
		Options: urban.ConversionOptions{
			Standalone: true,
		},
	})

	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    "Converted markdown to HTML",
	}, nil
}

func (p *DocumentPipeline) markdownToDocx(req ProcessRequest) (*ProcessResult, error) {
	if !p.Pandoc.Available {
		return nil, fmt.Errorf("pandoc not available")
	}

	result, err := p.Pandoc.MarkdownToDocx(req.InputPath, req.OutputPath)
	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    "Converted markdown to DOCX",
	}, nil
}

func (p *DocumentPipeline) docxToMarkdown(req ProcessRequest) (*ProcessResult, error) {
	if !p.Pandoc.Available {
		return nil, fmt.Errorf("pandoc not available")
	}

	result, err := p.Pandoc.DocxToMarkdown(req.InputPath, req.OutputPath)
	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    "Converted DOCX to markdown",
	}, nil
}

func (p *DocumentPipeline) htmlToMarkdown(req ProcessRequest) (*ProcessResult, error) {
	if !p.Pandoc.Available {
		return nil, fmt.Errorf("pandoc not available")
	}

	result, err := p.Pandoc.Convert(urban.ConversionRequest{
		InputPath:    req.InputPath,
		OutputPath:   req.OutputPath,
		InputFormat:  "html",
		OutputFormat: "markdown",
	})

	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    "Converted HTML to markdown",
	}, nil
}

func (p *DocumentPipeline) convertDocument(req ProcessRequest) (*ProcessResult, error) {
	if !p.Pandoc.Available {
		return nil, fmt.Errorf("pandoc not available")
	}

	outputFormat := "markdown"
	if fmt, ok := req.Options["output_format"].(string); ok {
		outputFormat = fmt
	}

	result, err := p.Pandoc.Convert(urban.ConversionRequest{
		InputPath:    req.InputPath,
		OutputPath:   req.OutputPath,
		OutputFormat: outputFormat,
	})

	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    fmt.Sprintf("Converted to %s", outputFormat),
	}, nil
}

// Media operations

func (p *DocumentPipeline) extractAudio(req ProcessRequest) (*ProcessResult, error) {
	if !p.FFmpeg.Available {
		return nil, fmt.Errorf("ffmpeg not available")
	}

	format := "mp3"
	if f, ok := req.Options["format"].(string); ok {
		format = f
	}

	result, err := p.FFmpeg.ExtractAudio(req.InputPath, req.OutputPath, format)
	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    fmt.Sprintf("Extracted audio as %s", format),
	}, nil
}

func (p *DocumentPipeline) prepareTranscription(req ProcessRequest) (*ProcessResult, error) {
	if !p.FFmpeg.Available {
		return nil, fmt.Errorf("ffmpeg not available")
	}

	result, err := p.FFmpeg.ExtractAudioForTranscription(req.InputPath, req.OutputPath)
	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    "Prepared audio for transcription (16kHz mono WAV)",
	}, nil
}

func (p *DocumentPipeline) convertAudio(req ProcessRequest) (*ProcessResult, error) {
	if !p.FFmpeg.Available {
		return nil, fmt.Errorf("ffmpeg not available")
	}

	format := "mp3"
	if f, ok := req.Options["format"].(string); ok {
		format = f
	}

	bitrate := "192k"
	if b, ok := req.Options["bitrate"].(string); ok {
		bitrate = b
	}

	outputPath := req.OutputPath
	if outputPath == "" {
		base := strings.TrimSuffix(req.InputPath, filepath.Ext(req.InputPath))
		outputPath = base + "." + format
	}

	var result *ConversionResult
	var err error

	switch format {
	case "opus":
		result, err = p.FFmpeg.ConvertToOpus(req.InputPath, outputPath, bitrate)
	default:
		result, err = p.FFmpeg.ConvertToMP3(req.InputPath, outputPath, bitrate)
	}

	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    fmt.Sprintf("Converted to %s at %s", format, bitrate),
	}, nil
}

func (p *DocumentPipeline) trimMedia(req ProcessRequest) (*ProcessResult, error) {
	if !p.FFmpeg.Available {
		return nil, fmt.Errorf("ffmpeg not available")
	}

	startTime := "00:00:00"
	if s, ok := req.Options["start"].(string); ok {
		startTime = s
	}

	duration := ""
	if d, ok := req.Options["duration"].(string); ok {
		duration = d
	}

	result, err := p.FFmpeg.TrimMedia(req.InputPath, req.OutputPath, startTime, duration)
	if err != nil {
		return &ProcessResult{
			Success:   false,
			InputPath: req.InputPath,
			Operation: req.Operation,
			Error:     err.Error(),
		}, err
	}

	return &ProcessResult{
		Success:    result.Success,
		InputPath:  result.InputPath,
		OutputPath: result.OutputPath,
		Operation:  req.Operation,
		Message:    fmt.Sprintf("Trimmed from %s", startTime),
	}, nil
}
