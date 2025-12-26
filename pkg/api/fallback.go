// Package api - Graceful Degradation and Fallback Handling
package api

import (
	"fmt"
)

// FeatureStatus represents the availability of a feature
type FeatureStatus struct {
	Available    bool     `json:"available"`
	Reason       string   `json:"reason,omitempty"`
	Fallback     string   `json:"fallback,omitempty"`
	InstallHelp  string   `json:"install_help,omitempty"`
	Alternatives []string `json:"alternatives,omitempty"`
}

// FeatureRegistry tracks feature availability
type FeatureRegistry struct {
	features map[string]*FeatureStatus
}

// NewFeatureRegistry creates a new feature registry
func NewFeatureRegistry() *FeatureRegistry {
	return &FeatureRegistry{
		features: make(map[string]*FeatureStatus),
	}
}

// Register registers a feature's status
func (r *FeatureRegistry) Register(name string, status *FeatureStatus) {
	r.features[name] = status
}

// Get returns a feature's status
func (r *FeatureRegistry) Get(name string) *FeatureStatus {
	if status, ok := r.features[name]; ok {
		return status
	}
	return &FeatureStatus{
		Available: false,
		Reason:    "Feature not registered",
	}
}

// IsAvailable checks if a feature is available
func (r *FeatureRegistry) IsAvailable(name string) bool {
	if status, ok := r.features[name]; ok {
		return status.Available
	}
	return false
}

// GetAll returns all registered features
func (r *FeatureRegistry) GetAll() map[string]*FeatureStatus {
	return r.features
}

// Common feature definitions with install help

// PandocFeature returns pandoc feature status
func PandocFeature(available bool, version string) *FeatureStatus {
	if available {
		return &FeatureStatus{
			Available: true,
		}
	}
	return &FeatureStatus{
		Available:   false,
		Reason:      "Pandoc is not installed",
		InstallHelp: "Install via: winget install JohnMacFarlane.Pandoc",
		Fallback:    "Document conversion features will be limited",
		Alternatives: []string{
			"Use online converters",
			"Export from source application",
		},
	}
}

// FFmpegFeature returns ffmpeg feature status
func FFmpegFeature(available bool) *FeatureStatus {
	if available {
		return &FeatureStatus{
			Available: true,
		}
	}
	return &FeatureStatus{
		Available:   false,
		Reason:      "FFmpeg is not installed",
		InstallHelp: "Install via: winget install Gyan.FFmpeg",
		Fallback:    "Audio/video processing will be unavailable",
		Alternatives: []string{
			"Use online audio converters",
			"Use VLC for basic conversions",
		},
	}
}

// TesseractFeature returns tesseract feature status
func TesseractFeature(available bool) *FeatureStatus {
	if available {
		return &FeatureStatus{
			Available: true,
		}
	}
	return &FeatureStatus{
		Available:   false,
		Reason:      "Tesseract OCR is not installed",
		InstallHelp: "Install via: winget install UB-Mannheim.TesseractOCR",
		Fallback:    "Local OCR will be unavailable, using cloud OCR instead",
		Alternatives: []string{
			"Cloud OCR via AIMLAPI (Florence-2)",
			"Manual text extraction",
		},
	}
}

// ImageMagickFeature returns imagemagick feature status
func ImageMagickFeature(available bool) *FeatureStatus {
	if available {
		return &FeatureStatus{
			Available: true,
		}
	}
	return &FeatureStatus{
		Available:   false,
		Reason:      "ImageMagick is not installed",
		InstallHelp: "Install via: winget install ImageMagick.ImageMagick",
		Fallback:    "Image processing will be limited",
		Alternatives: []string{
			"Use built-in Go image processing",
			"Use online image tools",
		},
	}
}

// AIMLAPIFeature returns AIMLAPI feature status
func AIMLAPIFeature(configured bool) *FeatureStatus {
	if configured {
		return &FeatureStatus{
			Available: true,
		}
	}
	return &FeatureStatus{
		Available:   false,
		Reason:      "AIMLAPI key not configured",
		InstallHelp: "Set environment variable: AIMLAPI_KEY=your_key",
		Fallback:    "AI-powered features will use mock responses",
		Alternatives: []string{
			"Use local Ollama models",
			"Use rule-based processing",
		},
	}
}

// GracefulError returns an error message with fallback information
func GracefulError(feature string, status *FeatureStatus) string {
	if status.Available {
		return ""
	}

	msg := fmt.Sprintf("%s: %s", feature, status.Reason)
	if status.Fallback != "" {
		msg += fmt.Sprintf("\nFallback: %s", status.Fallback)
	}
	if status.InstallHelp != "" {
		msg += fmt.Sprintf("\nTo enable: %s", status.InstallHelp)
	}

	return msg
}
