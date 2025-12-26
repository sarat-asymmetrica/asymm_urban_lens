// Package research provides integrated research tools for IIHS Urban Lens
// A comprehensive toolkit for urban researchers
package research

import (
	"bytes"
	"fmt"
	"image"
	_ "image/gif"
	_ "image/jpeg"
	_ "image/png"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// RESEARCH TOOLKIT - External Dependencies
// ═══════════════════════════════════════════════════════════════════════════

// Toolkit manages external research tools
type Toolkit struct {
	Pandoc      *PandocTool
	ImageMagick *ImageMagickTool
	FFMPEG      *FFMPEGTool
	Tesseract   *TesseractTool
}

// NewToolkit creates a new research toolkit
func NewToolkit() *Toolkit {
	return &Toolkit{
		Pandoc:      NewPandocTool(),
		ImageMagick: NewImageMagickTool(),
		FFMPEG:      NewFFMPEGTool(),
		Tesseract:   NewTesseractTool(),
	}
}

// GetStatus returns availability status of all tools
func (t *Toolkit) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"pandoc":      t.Pandoc.GetStatus(),
		"imagemagick": t.ImageMagick.GetStatus(),
		"ffmpeg":      t.FFMPEG.GetStatus(),
		"tesseract":   t.Tesseract.GetStatus(),
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// PANDOC - Document Conversion
// ═══════════════════════════════════════════════════════════════════════════

// PandocTool handles document format conversion
type PandocTool struct {
	Available bool
	Version   string
}

// NewPandocTool creates and checks pandoc availability
func NewPandocTool() *PandocTool {
	p := &PandocTool{}
	p.checkAvailability()
	return p
}

func (p *PandocTool) checkAvailability() {
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

// Convert converts document from one format to another
func (p *PandocTool) Convert(input, output, fromFmt, toFmt string) error {
	if !p.Available {
		return fmt.Errorf("pandoc not installed")
	}

	args := []string{input, "-f", fromFmt, "-t", toFmt, "-o", output}
	cmd := exec.Command("pandoc", args...)
	return cmd.Run()
}

// ConvertString converts string content between formats
func (p *PandocTool) ConvertString(content, fromFmt, toFmt string) (string, error) {
	if !p.Available {
		return "", fmt.Errorf("pandoc not installed")
	}

	cmd := exec.Command("pandoc", "-f", fromFmt, "-t", toFmt)
	cmd.Stdin = strings.NewReader(content)
	var out bytes.Buffer
	cmd.Stdout = &out
	if err := cmd.Run(); err != nil {
		return "", err
	}
	return out.String(), nil
}

// MarkdownToHTML converts markdown to HTML
func (p *PandocTool) MarkdownToHTML(md string) (string, error) {
	return p.ConvertString(md, "markdown", "html")
}

// MarkdownToDocx converts markdown file to DOCX
func (p *PandocTool) MarkdownToDocx(input, output string) error {
	return p.Convert(input, output, "markdown", "docx")
}

// GetStatus returns pandoc status
func (p *PandocTool) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available": p.Available,
		"version":   p.Version,
		"formats":   []string{"markdown", "html", "docx", "pdf", "latex", "rst", "epub"},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// IMAGEMAGICK - Image Processing
// ═══════════════════════════════════════════════════════════════════════════

// ImageMagickTool handles image processing
type ImageMagickTool struct {
	Available bool
	Version   string
}

// NewImageMagickTool creates and checks imagemagick availability
func NewImageMagickTool() *ImageMagickTool {
	im := &ImageMagickTool{}
	im.checkAvailability()
	return im
}

func (im *ImageMagickTool) checkAvailability() {
	// Try 'magick' first (ImageMagick 7), then 'convert' (ImageMagick 6)
	cmd := exec.Command("magick", "--version")
	output, err := cmd.Output()
	if err != nil {
		cmd = exec.Command("convert", "--version")
		output, err = cmd.Output()
	}
	if err != nil {
		im.Available = false
		return
	}
	im.Available = true
	lines := strings.Split(string(output), "\n")
	if len(lines) > 0 {
		im.Version = strings.TrimSpace(lines[0])
	}
}

// Resize resizes an image
func (im *ImageMagickTool) Resize(input, output string, width, height int) error {
	if !im.Available {
		return fmt.Errorf("imagemagick not installed")
	}

	size := fmt.Sprintf("%dx%d", width, height)
	cmd := exec.Command("magick", input, "-resize", size, output)
	if err := cmd.Run(); err != nil {
		// Try ImageMagick 6 syntax
		cmd = exec.Command("convert", input, "-resize", size, output)
		return cmd.Run()
	}
	return nil
}

// ConvertFormat converts image format
func (im *ImageMagickTool) ConvertFormat(input, output string) error {
	if !im.Available {
		return fmt.Errorf("imagemagick not installed")
	}

	cmd := exec.Command("magick", input, output)
	if err := cmd.Run(); err != nil {
		cmd = exec.Command("convert", input, output)
		return cmd.Run()
	}
	return nil
}

// GetImageInfo returns image dimensions and format
func (im *ImageMagickTool) GetImageInfo(path string) (map[string]interface{}, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	config, format, err := image.DecodeConfig(file)
	if err != nil {
		return nil, err
	}

	return map[string]interface{}{
		"width":  config.Width,
		"height": config.Height,
		"format": format,
	}, nil
}

// CreateThumbnail creates a thumbnail
func (im *ImageMagickTool) CreateThumbnail(input, output string, size int) error {
	return im.Resize(input, output, size, size)
}

// GetStatus returns imagemagick status
func (im *ImageMagickTool) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available":  im.Available,
		"version":    im.Version,
		"operations": []string{"resize", "convert", "thumbnail", "crop", "rotate"},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// FFMPEG - Video/Audio Processing
// ═══════════════════════════════════════════════════════════════════════════

// FFMPEGTool handles video/audio processing
type FFMPEGTool struct {
	Available bool
	Version   string
}

// NewFFMPEGTool creates and checks ffmpeg availability
func NewFFMPEGTool() *FFMPEGTool {
	f := &FFMPEGTool{}
	f.checkAvailability()
	return f
}

func (f *FFMPEGTool) checkAvailability() {
	cmd := exec.Command("ffmpeg", "-version")
	output, err := cmd.Output()
	if err != nil {
		f.Available = false
		return
	}
	f.Available = true
	lines := strings.Split(string(output), "\n")
	if len(lines) > 0 {
		f.Version = strings.TrimSpace(lines[0])
	}
}

// ExtractAudio extracts audio from video
func (f *FFMPEGTool) ExtractAudio(input, output string) error {
	if !f.Available {
		return fmt.Errorf("ffmpeg not installed")
	}

	cmd := exec.Command("ffmpeg", "-i", input, "-vn", "-acodec", "copy", output, "-y")
	return cmd.Run()
}

// ExtractFrames extracts frames from video
func (f *FFMPEGTool) ExtractFrames(input, outputPattern string, fps int) error {
	if !f.Available {
		return fmt.Errorf("ffmpeg not installed")
	}

	fpsArg := fmt.Sprintf("fps=%d", fps)
	cmd := exec.Command("ffmpeg", "-i", input, "-vf", fpsArg, outputPattern, "-y")
	return cmd.Run()
}

// GetMediaInfo returns media file information
func (f *FFMPEGTool) GetMediaInfo(path string) (string, error) {
	if !f.Available {
		return "", fmt.Errorf("ffmpeg not installed")
	}

	cmd := exec.Command("ffprobe", "-v", "quiet", "-print_format", "json", "-show_format", "-show_streams", path)
	output, err := cmd.Output()
	if err != nil {
		return "", err
	}
	return string(output), nil
}

// GetStatus returns ffmpeg status
func (f *FFMPEGTool) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available":  f.Available,
		"version":    f.Version,
		"operations": []string{"extract_audio", "extract_frames", "convert", "compress"},
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// TESSERACT - OCR (Backup to Florence-2)
// ═══════════════════════════════════════════════════════════════════════════

// TesseractTool handles OCR as backup to Florence-2
type TesseractTool struct {
	Available bool
	Version   string
	Languages []string
}

// NewTesseractTool creates and checks tesseract availability
func NewTesseractTool() *TesseractTool {
	t := &TesseractTool{}
	t.checkAvailability()
	return t
}

func (t *TesseractTool) checkAvailability() {
	cmd := exec.Command("tesseract", "--version")
	output, err := cmd.Output()
	if err != nil {
		t.Available = false
		return
	}
	t.Available = true
	lines := strings.Split(string(output), "\n")
	if len(lines) > 0 {
		t.Version = strings.TrimSpace(lines[0])
	}

	// Get available languages
	langCmd := exec.Command("tesseract", "--list-langs")
	langOutput, err := langCmd.Output()
	if err == nil {
		langs := strings.Split(string(langOutput), "\n")
		for _, lang := range langs[1:] { // Skip header
			lang = strings.TrimSpace(lang)
			if lang != "" {
				t.Languages = append(t.Languages, lang)
			}
		}
	}
}

// OCR performs OCR on an image
func (t *TesseractTool) OCR(imagePath string, lang string) (string, error) {
	if !t.Available {
		return "", fmt.Errorf("tesseract not installed")
	}

	if lang == "" {
		lang = "eng"
	}

	cmd := exec.Command("tesseract", imagePath, "stdout", "-l", lang)
	output, err := cmd.Output()
	if err != nil {
		return "", err
	}
	return string(output), nil
}

// OCRToFile performs OCR and saves to file
func (t *TesseractTool) OCRToFile(imagePath, outputBase, lang string) error {
	if !t.Available {
		return fmt.Errorf("tesseract not installed")
	}

	if lang == "" {
		lang = "eng"
	}

	cmd := exec.Command("tesseract", imagePath, outputBase, "-l", lang)
	return cmd.Run()
}

// GetStatus returns tesseract status
func (t *TesseractTool) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available": t.Available,
		"version":   t.Version,
		"languages": t.Languages,
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// FILE UTILITIES
// ═══════════════════════════════════════════════════════════════════════════

// FileInfo represents file metadata
type FileInfo struct {
	Name      string
	Path      string
	Size      int64
	Extension string
	IsDir     bool
	ModTime   string
}

// ListFiles lists files in a directory with optional extension filter
func ListFiles(dir string, extensions []string) ([]FileInfo, error) {
	var files []FileInfo

	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // Skip errors
		}

		ext := strings.ToLower(filepath.Ext(path))

		// Filter by extension if specified
		if len(extensions) > 0 && !info.IsDir() {
			found := false
			for _, e := range extensions {
				if ext == "."+strings.ToLower(e) {
					found = true
					break
				}
			}
			if !found {
				return nil
			}
		}

		files = append(files, FileInfo{
			Name:      info.Name(),
			Path:      path,
			Size:      info.Size(),
			Extension: ext,
			IsDir:     info.IsDir(),
			ModTime:   info.ModTime().Format("2006-01-02 15:04:05"),
		})

		return nil
	})

	return files, err
}

// GetFileType determines file type from extension
func GetFileType(path string) string {
	ext := strings.ToLower(filepath.Ext(path))

	documentExts := map[string]bool{
		".pdf": true, ".doc": true, ".docx": true, ".odt": true,
		".rtf": true, ".txt": true, ".md": true, ".tex": true,
	}
	imageExts := map[string]bool{
		".jpg": true, ".jpeg": true, ".png": true, ".gif": true,
		".bmp": true, ".tiff": true, ".webp": true, ".svg": true,
	}
	dataExts := map[string]bool{
		".csv": true, ".xlsx": true, ".xls": true, ".json": true,
		".xml": true, ".geojson": true, ".shp": true,
	}
	videoExts := map[string]bool{
		".mp4": true, ".avi": true, ".mov": true, ".mkv": true,
		".webm": true, ".flv": true,
	}
	audioExts := map[string]bool{
		".mp3": true, ".wav": true, ".ogg": true, ".flac": true,
		".m4a": true, ".aac": true,
	}

	switch {
	case documentExts[ext]:
		return "document"
	case imageExts[ext]:
		return "image"
	case dataExts[ext]:
		return "data"
	case videoExts[ext]:
		return "video"
	case audioExts[ext]:
		return "audio"
	default:
		return "unknown"
	}
}
