package media

import (
	"testing"
)

func TestFFmpegProcessor_Availability(t *testing.T) {
	fp := NewFFmpegProcessor()

	status := fp.GetStatus()
	t.Logf("FFmpeg status: %+v", status)

	if !fp.Available {
		t.Skip("FFmpeg not installed - skipping tests")
	}

	if fp.Version == "" {
		t.Error("Expected version string when available")
	}
}

func TestFFmpegProcessor_SupportedFormats(t *testing.T) {
	fp := NewFFmpegProcessor()

	formats := fp.SupportedFormats()

	if len(formats["audio_input"]) == 0 {
		t.Error("Expected audio input formats")
	}
	if len(formats["video_input"]) == 0 {
		t.Error("Expected video input formats")
	}
}
