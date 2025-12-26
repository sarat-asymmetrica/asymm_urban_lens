// Package media provides unified media processing via ffmpeg
// Supports audio/video conversion, extraction, and transcription preparation
package media

import (
	"bytes"
	"fmt"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

// FFmpegProcessor handles media processing via ffmpeg
type FFmpegProcessor struct {
	Available bool
	Version   string
}

// NewFFmpegProcessor creates a new ffmpeg processor and checks availability
func NewFFmpegProcessor() *FFmpegProcessor {
	fp := &FFmpegProcessor{}
	fp.checkAvailability()
	return fp
}

// checkAvailability checks if ffmpeg is installed
func (f *FFmpegProcessor) checkAvailability() {
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

// MediaInfo contains information about a media file
type MediaInfo struct {
	Duration   time.Duration
	Format     string
	VideoCodec string
	AudioCodec string
	Width      int
	Height     int
	Bitrate    int
	SampleRate int
	Channels   int
	HasVideo   bool
	HasAudio   bool
}

// ConversionRequest represents a media conversion request
type ConversionRequest struct {
	InputPath    string
	OutputPath   string
	OutputFormat string
	Options      ConversionOptions
}

// ConversionOptions holds ffmpeg conversion options
type ConversionOptions struct {
	AudioCodec   string // e.g., "aac", "mp3", "opus"
	VideoCodec   string // e.g., "h264", "h265", "vp9"
	AudioBitrate string // e.g., "128k", "256k"
	VideoBitrate string // e.g., "1M", "2M"
	SampleRate   int    // e.g., 44100, 48000
	Channels     int    // 1 for mono, 2 for stereo
	Resolution   string // e.g., "1920x1080", "1280x720"
	FrameRate    int    // e.g., 24, 30, 60
	StartTime    string // e.g., "00:01:30"
	Duration     string // e.g., "00:05:00"
	NoVideo      bool   // Extract audio only
	NoAudio      bool   // Extract video only
	Overwrite    bool   // Overwrite output file
}

// ConversionResult represents the result of a conversion
type ConversionResult struct {
	Success    bool
	InputPath  string
	OutputPath string
	Duration   time.Duration
	Error      string
}

// Convert converts a media file using ffmpeg
func (f *FFmpegProcessor) Convert(req ConversionRequest) (*ConversionResult, error) {
	if !f.Available {
		return nil, fmt.Errorf("ffmpeg is not installed. Install via: winget install Gyan.FFmpeg")
	}

	start := time.Now()

	// Build ffmpeg command
	args := []string{"-i", req.InputPath}

	// Add options
	if req.Options.Overwrite {
		args = append([]string{"-y"}, args...)
	}
	if req.Options.StartTime != "" {
		args = append(args, "-ss", req.Options.StartTime)
	}
	if req.Options.Duration != "" {
		args = append(args, "-t", req.Options.Duration)
	}
	if req.Options.NoVideo {
		args = append(args, "-vn")
	}
	if req.Options.NoAudio {
		args = append(args, "-an")
	}
	if req.Options.AudioCodec != "" {
		args = append(args, "-acodec", req.Options.AudioCodec)
	}
	if req.Options.VideoCodec != "" {
		args = append(args, "-vcodec", req.Options.VideoCodec)
	}
	if req.Options.AudioBitrate != "" {
		args = append(args, "-b:a", req.Options.AudioBitrate)
	}
	if req.Options.VideoBitrate != "" {
		args = append(args, "-b:v", req.Options.VideoBitrate)
	}
	if req.Options.SampleRate > 0 {
		args = append(args, "-ar", fmt.Sprintf("%d", req.Options.SampleRate))
	}
	if req.Options.Channels > 0 {
		args = append(args, "-ac", fmt.Sprintf("%d", req.Options.Channels))
	}
	if req.Options.Resolution != "" {
		args = append(args, "-s", req.Options.Resolution)
	}
	if req.Options.FrameRate > 0 {
		args = append(args, "-r", fmt.Sprintf("%d", req.Options.FrameRate))
	}

	args = append(args, req.OutputPath)

	// Execute ffmpeg
	cmd := exec.Command("ffmpeg", args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr

	err := cmd.Run()
	duration := time.Since(start)

	if err != nil {
		return &ConversionResult{
			Success:    false,
			InputPath:  req.InputPath,
			OutputPath: req.OutputPath,
			Duration:   duration,
			Error:      stderr.String(),
		}, fmt.Errorf("ffmpeg conversion failed: %s", stderr.String())
	}

	return &ConversionResult{
		Success:    true,
		InputPath:  req.InputPath,
		OutputPath: req.OutputPath,
		Duration:   duration,
	}, nil
}

// ExtractAudio extracts audio from a video file
func (f *FFmpegProcessor) ExtractAudio(inputPath, outputPath string, format string) (*ConversionResult, error) {
	if format == "" {
		format = "mp3"
	}
	if outputPath == "" {
		base := strings.TrimSuffix(inputPath, filepath.Ext(inputPath))
		outputPath = base + "." + format
	}

	return f.Convert(ConversionRequest{
		InputPath:  inputPath,
		OutputPath: outputPath,
		Options: ConversionOptions{
			NoVideo:   true,
			Overwrite: true,
		},
	})
}

// ExtractAudioForTranscription extracts audio optimized for speech-to-text
// 16kHz mono WAV - optimal for Whisper and other ASR models
func (f *FFmpegProcessor) ExtractAudioForTranscription(inputPath, outputPath string) (*ConversionResult, error) {
	if outputPath == "" {
		base := strings.TrimSuffix(inputPath, filepath.Ext(inputPath))
		outputPath = base + "_transcribe.wav"
	}

	return f.Convert(ConversionRequest{
		InputPath:  inputPath,
		OutputPath: outputPath,
		Options: ConversionOptions{
			NoVideo:    true,
			AudioCodec: "pcm_s16le",
			SampleRate: 16000,
			Channels:   1,
			Overwrite:  true,
		},
	})
}

// ConvertToMP3 converts audio to MP3 format
func (f *FFmpegProcessor) ConvertToMP3(inputPath, outputPath string, bitrate string) (*ConversionResult, error) {
	if bitrate == "" {
		bitrate = "192k"
	}
	if outputPath == "" {
		base := strings.TrimSuffix(inputPath, filepath.Ext(inputPath))
		outputPath = base + ".mp3"
	}

	return f.Convert(ConversionRequest{
		InputPath:  inputPath,
		OutputPath: outputPath,
		Options: ConversionOptions{
			AudioCodec:   "libmp3lame",
			AudioBitrate: bitrate,
			Overwrite:    true,
		},
	})
}

// ConvertToOpus converts audio to Opus format (excellent for voice)
func (f *FFmpegProcessor) ConvertToOpus(inputPath, outputPath string, bitrate string) (*ConversionResult, error) {
	if bitrate == "" {
		bitrate = "64k" // Opus is very efficient
	}
	if outputPath == "" {
		base := strings.TrimSuffix(inputPath, filepath.Ext(inputPath))
		outputPath = base + ".opus"
	}

	return f.Convert(ConversionRequest{
		InputPath:  inputPath,
		OutputPath: outputPath,
		Options: ConversionOptions{
			AudioCodec:   "libopus",
			AudioBitrate: bitrate,
			Overwrite:    true,
		},
	})
}

// TrimMedia trims a media file to specified start and duration
func (f *FFmpegProcessor) TrimMedia(inputPath, outputPath, startTime, duration string) (*ConversionResult, error) {
	if outputPath == "" {
		ext := filepath.Ext(inputPath)
		base := strings.TrimSuffix(inputPath, ext)
		outputPath = base + "_trimmed" + ext
	}

	return f.Convert(ConversionRequest{
		InputPath:  inputPath,
		OutputPath: outputPath,
		Options: ConversionOptions{
			StartTime: startTime,
			Duration:  duration,
			Overwrite: true,
		},
	})
}

// GetStatus returns ffmpeg availability status
func (f *FFmpegProcessor) GetStatus() map[string]interface{} {
	return map[string]interface{}{
		"available": f.Available,
		"version":   f.Version,
		"capabilities": []string{
			"audio_extraction",
			"video_conversion",
			"transcription_prep",
			"format_conversion",
			"trimming",
		},
	}
}

// SupportedFormats returns commonly supported formats
func (f *FFmpegProcessor) SupportedFormats() map[string][]string {
	return map[string][]string{
		"audio_input":  {"mp3", "wav", "flac", "aac", "ogg", "opus", "m4a", "wma"},
		"audio_output": {"mp3", "wav", "flac", "aac", "ogg", "opus", "m4a"},
		"video_input":  {"mp4", "mkv", "avi", "mov", "webm", "flv", "wmv"},
		"video_output": {"mp4", "mkv", "webm", "mov"},
	}
}
