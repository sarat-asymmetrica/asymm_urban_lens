package cognition

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	"github.com/google/uuid"
)

// ============================================================================
// THOUGHT RECORDER - Record and replay cognition sessions
// ============================================================================
//
// Records complete cognition sessions for later analysis and replay
// Supports adjustable playback speed
// Stores as quaternion concepts for searchability
//
// ============================================================================

// ThoughtRecorder records and replays cognition sessions
type ThoughtRecorder struct {
	store           *QuaternionStore
	recordingsPath  string
}

// NewThoughtRecorder creates a new recorder
func NewThoughtRecorder(store *QuaternionStore, recordingsPath string) *ThoughtRecorder {
	return &ThoughtRecorder{
		store:          store,
		recordingsPath: recordingsPath,
	}
}

// StartRecording begins capturing events for a session
func (tr *ThoughtRecorder) StartRecording(stream *ThoughtStream) error {
	if stream.Recording {
		return fmt.Errorf("session %s already recording", stream.SessionID)
	}

	stream.Recording = true
	stream.RecordedEvents = make([]*CognitionEvent, 0)

	return nil
}

// StopRecording finalizes a recording
func (tr *ThoughtRecorder) StopRecording(stream *ThoughtStream) (*Recording, error) {
	if !stream.Recording {
		return nil, fmt.Errorf("session %s not recording", stream.SessionID)
	}

	stream.Recording = false

	// Count event types
	conceptsFormed := 0
	connectionsMade := 0
	regimeShifts := 0

	for _, event := range stream.RecordedEvents {
		switch event.EventType {
		case EventConceptFormed:
			conceptsFormed++
		case EventConnectionMade:
			connectionsMade++
		case EventRegimeShift:
			regimeShifts++
		}
	}

	// Build recording
	recording := &Recording{
		ID:              uuid.New(),
		SessionID:       stream.SessionID,
		StartTime:       stream.StartTime,
		EndTime:         time.Now(),
		Events:          stream.RecordedEvents,
		FinalState:      stream.LastState,
		Metadata:        make(map[string]interface{}),
		TotalEvents:     len(stream.RecordedEvents),
		ConceptsFormed:  conceptsFormed,
		ConnectionsMade: connectionsMade,
		RegimeShifts:    regimeShifts,
		Duration:        time.Since(stream.StartTime),
	}

	// Add metadata
	recording.Metadata["session_id"] = stream.SessionID
	recording.Metadata["regime"] = string(stream.CurrentRegime)
	recording.Metadata["event_count"] = stream.EventCount

	return recording, nil
}

// SaveRecording persists a recording to disk
func (tr *ThoughtRecorder) SaveRecording(ctx context.Context, recording *Recording) error {
	// Ensure recordings directory exists
	if err := os.MkdirAll(tr.recordingsPath, 0755); err != nil {
		return fmt.Errorf("failed to create recordings directory: %w", err)
	}

	// Save to JSON file
	filename := fmt.Sprintf("%s_%s.json",
		recording.StartTime.Format("20060102_150405"),
		recording.SessionID)

	filepath := filepath.Join(tr.recordingsPath, filename)

	data, err := json.MarshalIndent(recording, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to serialize recording: %w", err)
	}

	if err := os.WriteFile(filepath, data, 0644); err != nil {
		return fmt.Errorf("failed to write recording file: %w", err)
	}

	// Also store as quaternion concept for searchability
	if err := tr.storeRecordingAsQuaternion(ctx, recording); err != nil {
		// Non-fatal - log but don't fail
		fmt.Printf("⚠️ Failed to store recording as quaternion: %v\n", err)
	}

	return nil
}

// LoadRecording loads a recording from disk
func (tr *ThoughtRecorder) LoadRecording(recordingID uuid.UUID) (*Recording, error) {
	// Find file matching ID
	files, err := os.ReadDir(tr.recordingsPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read recordings directory: %w", err)
	}

	for _, file := range files {
		if file.IsDir() {
			continue
		}

		filepath := filepath.Join(tr.recordingsPath, file.Name())

		// Try to load and check ID
		data, err := os.ReadFile(filepath)
		if err != nil {
			continue
		}

		var recording Recording
		if err := json.Unmarshal(data, &recording); err != nil {
			continue
		}

		if recording.ID == recordingID {
			return &recording, nil
		}
	}

	return nil, fmt.Errorf("recording %s not found", recordingID)
}

// ListRecordings returns all available recordings
func (tr *ThoughtRecorder) ListRecordings() ([]*Recording, error) {
	files, err := os.ReadDir(tr.recordingsPath)
	if err != nil {
		if os.IsNotExist(err) {
			return []*Recording{}, nil
		}
		return nil, fmt.Errorf("failed to read recordings directory: %w", err)
	}

	recordings := make([]*Recording, 0)

	for _, file := range files {
		if file.IsDir() {
			continue
		}

		filepath := filepath.Join(tr.recordingsPath, file.Name())

		data, err := os.ReadFile(filepath)
		if err != nil {
			continue
		}

		var recording Recording
		if err := json.Unmarshal(data, &recording); err != nil {
			continue
		}

		recordings = append(recordings, &recording)
	}

	return recordings, nil
}

// Replay replays a recording at adjustable speed
func (tr *ThoughtRecorder) Replay(ctx context.Context, recordingID uuid.UUID, speed float64) (*ThoughtStream, error) {
	// Load recording
	recording, err := tr.LoadRecording(recordingID)
	if err != nil {
		return nil, err
	}

	if speed <= 0 {
		speed = 1.0 // Default to real-time
	}

	// Create new stream for replay
	stream := &ThoughtStream{
		SessionID:      fmt.Sprintf("replay_%s", recording.ID.String()[:8]),
		StartTime:      time.Now(),
		CurrentRegime:  RegimeExploration,
		EventChannel:   make(chan *CognitionEvent, 256),
		Active:         true,
		LastState:      nil,
		EventCount:     0,
		Recording:      false,
		RecordedEvents: nil,
	}

	// Start replay goroutine
	go func() {
		defer close(stream.EventChannel)

		var lastEventTime time.Time
		for i, event := range recording.Events {
			// Check context cancellation
			select {
			case <-ctx.Done():
				return
			default:
			}

			// Calculate delay based on speed
			if i > 0 {
				originalDelay := event.Timestamp.Sub(lastEventTime)
				adjustedDelay := time.Duration(float64(originalDelay) / speed)

				if adjustedDelay > 0 {
					time.Sleep(adjustedDelay)
				}
			}

			lastEventTime = event.Timestamp

			// Send event (with updated timestamp for "now")
			replayEvent := &CognitionEvent{
				SessionID:    stream.SessionID,
				Timestamp:    time.Now(),
				EventType:    event.EventType,
				Regime:       event.Regime,
				CurrentState: event.CurrentState,
				Delta:        event.Delta,
				Message:      fmt.Sprintf("🔁 [REPLAY %.1fx] %s", speed, event.Message),
				Metadata:     event.Metadata,
			}

			stream.EventChannel <- replayEvent
			stream.EventCount++

			if event.CurrentState != nil {
				stream.LastState = event.CurrentState
			}
			if event.Regime != "" {
				stream.CurrentRegime = event.Regime
			}
		}

		// Mark stream as inactive when replay completes
		stream.Active = false

		// Send completion event
		completionEvent := &CognitionEvent{
			SessionID:    stream.SessionID,
			Timestamp:    time.Now(),
			EventType:    EventStateSnapshot,
			Regime:       stream.CurrentRegime,
			CurrentState: stream.LastState,
			Message:      "✅ Replay complete",
			Metadata: map[string]interface{}{
				"original_duration": recording.Duration.Seconds(),
				"replay_speed":      speed,
				"events_replayed":   stream.EventCount,
			},
		}

		stream.EventChannel <- completionEvent
	}()

	return stream, nil
}

// storeRecordingAsQuaternion stores recording metadata as searchable quaternion
func (tr *ThoughtRecorder) storeRecordingAsQuaternion(ctx context.Context, recording *Recording) error {
	// Create searchable text from recording
	searchText := fmt.Sprintf("Recording %s: %d events, %d concepts formed, %d connections made, %d regime shifts",
		recording.SessionID,
		recording.TotalEvents,
		recording.ConceptsFormed,
		recording.ConnectionsMade,
		recording.RegimeShifts)

	// Encode as quaternion
	q := QuaternionFromText(searchText)

	// Calculate digital root
	dr := CalculateDigitalRoot(recording.ID)

	// Create concept
	concept := &QuaternionConcept{
		ID:              recording.ID,
		Quaternion:      q,
		DigitalRoot:     dr,
		EntityType:      "RECORDING",
		SourceID:        recording.ID,
		SourceType:      "cognition_recording",
		Regime:          RegimeStabilization, // Recordings are stable artifacts
		Confidence:      1.0,
		HarmonicWeight:  1.0,
		Data: map[string]interface{}{
			"session_id":       recording.SessionID,
			"start_time":       recording.StartTime,
			"end_time":         recording.EndTime,
			"duration":         recording.Duration.Seconds(),
			"total_events":     recording.TotalEvents,
			"concepts_formed":  recording.ConceptsFormed,
			"connections_made": recording.ConnectionsMade,
			"regime_shifts":    recording.RegimeShifts,
		},
		HumanAnnotation: fmt.Sprintf("Cognition recording: %s", recording.SessionID),
	}

	return tr.store.Insert(ctx, concept)
}

// DeleteRecording removes a recording
func (tr *ThoughtRecorder) DeleteRecording(ctx context.Context, recordingID uuid.UUID) error {
	// Delete from disk
	files, err := os.ReadDir(tr.recordingsPath)
	if err != nil {
		return fmt.Errorf("failed to read recordings directory: %w", err)
	}

	deleted := false
	for _, file := range files {
		if file.IsDir() {
			continue
		}

		filepath := filepath.Join(tr.recordingsPath, file.Name())

		data, err := os.ReadFile(filepath)
		if err != nil {
			continue
		}

		var recording Recording
		if err := json.Unmarshal(data, &recording); err != nil {
			continue
		}

		if recording.ID == recordingID {
			if err := os.Remove(filepath); err != nil {
				return fmt.Errorf("failed to delete recording file: %w", err)
			}
			deleted = true
			break
		}
	}

	if !deleted {
		return fmt.Errorf("recording %s not found", recordingID)
	}

	// Also delete from quaternion store
	if err := tr.store.SoftDelete(ctx, recordingID); err != nil {
		// Non-fatal
		fmt.Printf("⚠️ Failed to delete recording from quaternion store: %v\n", err)
	}

	return nil
}

// SearchRecordings finds recordings by text query
func (tr *ThoughtRecorder) SearchRecordings(ctx context.Context, query string, limit int) ([]*Recording, error) {
	// Encode query as quaternion
	queryQ := QuaternionFromText(query)
	queryDR := CalculateDigitalRootFromQuaternion(queryQ)

	// Search quaternion store
	concepts, err := tr.store.FindSimilar(ctx, queryQ, queryDR, 0.5, limit)
	if err != nil {
		return nil, fmt.Errorf("quaternion search failed: %w", err)
	}

	// Load full recordings
	recordings := make([]*Recording, 0)
	for _, concept := range concepts {
		if concept.EntityType != "RECORDING" {
			continue
		}

		recording, err := tr.LoadRecording(concept.ID)
		if err != nil {
			continue
		}

		recordings = append(recordings, recording)
	}

	return recordings, nil
}

// GetRecordingStats returns statistics about recordings
func (tr *ThoughtRecorder) GetRecordingStats() (map[string]interface{}, error) {
	recordings, err := tr.ListRecordings()
	if err != nil {
		return nil, err
	}

	totalEvents := 0
	totalConcepts := 0
	totalConnections := 0
	totalRegimeShifts := 0
	var totalDuration time.Duration

	for _, r := range recordings {
		totalEvents += r.TotalEvents
		totalConcepts += r.ConceptsFormed
		totalConnections += r.ConnectionsMade
		totalRegimeShifts += r.RegimeShifts
		totalDuration += r.Duration
	}

	avgEventsPerSession := 0.0
	if len(recordings) > 0 {
		avgEventsPerSession = float64(totalEvents) / float64(len(recordings))
	}

	return map[string]interface{}{
		"total_recordings":     len(recordings),
		"total_events":         totalEvents,
		"total_concepts":       totalConcepts,
		"total_connections":    totalConnections,
		"total_regime_shifts":  totalRegimeShifts,
		"total_duration_hours": totalDuration.Hours(),
		"avg_events_per_session": avgEventsPerSession,
	}, nil
}
