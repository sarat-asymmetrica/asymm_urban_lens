package cognition

import (
	"context"
	"fmt"
	"math"
	"sync"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
	"github.com/google/uuid"
)

// ============================================================================
// COGNITION OBSERVER - Real-time thought process streaming
// ============================================================================
//
// Streams cognitive events at Tesla's 4.909 Hz harmonic (203.9ms intervals)
// Captures complete internal state, regime transitions, concept formation
// Enables real-time visualization and intervention
//
// ============================================================================

// CognitionObserver streams thought processes
type CognitionObserver struct {
	store           *QuaternionStore
	streams         map[string]*ThoughtStream
	streamsMu       sync.RWMutex
	teslaInterval   time.Duration // 203.9ms
	eventHandlers   []EventHandler
}

// EventHandler processes cognitive events
type EventHandler func(*CognitionEvent) error

// NewCognitionObserver creates a new observer
func NewCognitionObserver(store *QuaternionStore) *CognitionObserver {
	return &CognitionObserver{
		store:         store,
		streams:       make(map[string]*ThoughtStream),
		teslaInterval: time.Duration(TeslaHarmonicMs * float64(time.Millisecond)),
	}
}

// RegisterEventHandler adds an event handler
func (co *CognitionObserver) RegisterEventHandler(handler EventHandler) {
	co.eventHandlers = append(co.eventHandlers, handler)
}

// StartObserving creates a new thought stream
func (co *CognitionObserver) StartObserving(ctx context.Context, sessionID string) (*ThoughtStream, error) {
	co.streamsMu.Lock()
	defer co.streamsMu.Unlock()

	// Check if session already exists
	if stream, exists := co.streams[sessionID]; exists {
		if stream.Active {
			return nil, fmt.Errorf("session %s already active", sessionID)
		}
	}

	// Create new stream
	stream := &ThoughtStream{
		SessionID:     sessionID,
		StartTime:     time.Now(),
		CurrentRegime: RegimeExploration, // Always start in EXPLORATION
		EventChannel:  make(chan *CognitionEvent, 256),
		Active:        true,
		LastState:     nil,
		EventCount:    0,
		Recording:     false,
		RecordedEvents: make([]*CognitionEvent, 0),
	}

	co.streams[sessionID] = stream

	// Start streaming goroutine
	go co.streamEvents(ctx, stream)

	// Emit session start event
	startEvent := &CognitionEvent{
		SessionID: sessionID,
		Timestamp: time.Now(),
		EventType: EventStateSnapshot,
		Regime:    RegimeExploration,
		Message:   "🧠 Cognition observation started",
		Metadata: map[string]interface{}{
			"tesla_interval_ms": TeslaHarmonicMs,
			"tesla_frequency_hz": TeslaBaseFrequencyHz,
		},
	}

	stream.EventChannel <- startEvent

	return stream, nil
}

// StopObserving ends observation for a session
func (co *CognitionObserver) StopObserving(sessionID string) error {
	co.streamsMu.Lock()
	defer co.streamsMu.Unlock()

	stream, exists := co.streams[sessionID]
	if !exists {
		return fmt.Errorf("session %s not found", sessionID)
	}

	if !stream.Active {
		return fmt.Errorf("session %s already stopped", sessionID)
	}

	// Mark inactive
	stream.Active = false

	// Emit final event
	finalEvent := &CognitionEvent{
		SessionID:    sessionID,
		Timestamp:    time.Now(),
		EventType:    EventStateSnapshot,
		Regime:       stream.CurrentRegime,
		CurrentState: stream.LastState,
		Message:      "✅ Cognition observation ended",
		Metadata: map[string]interface{}{
			"total_events": stream.EventCount,
			"duration_seconds": time.Since(stream.StartTime).Seconds(),
		},
	}

	stream.EventChannel <- finalEvent

	// Close channel after a short delay (allow final event to be processed)
	go func() {
		time.Sleep(time.Second)
		close(stream.EventChannel)
	}()

	return nil
}

// streamEvents emits events at Tesla harmonic intervals
func (co *CognitionObserver) streamEvents(ctx context.Context, stream *ThoughtStream) {
	ticker := time.NewTicker(co.teslaInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			if !stream.Active {
				return
			}

			// Capture current state
			event := co.captureCurrentState(ctx, stream)
			if event != nil {
				stream.EventChannel <- event
				stream.EventCount++

				// Update last state
				if event.CurrentState != nil {
					stream.LastState = event.CurrentState
				}

				// Record if recording enabled
				if stream.Recording {
					stream.RecordedEvents = append(stream.RecordedEvents, event)
				}

				// Notify handlers
				for _, handler := range co.eventHandlers {
					go handler(event) // Non-blocking
				}
			}

		case <-ctx.Done():
			stream.Active = false
			return
		}
	}
}

// captureCurrentState creates a state snapshot
func (co *CognitionObserver) captureCurrentState(ctx context.Context, stream *ThoughtStream) *CognitionEvent {
	now := time.Now()

	// Query active concepts from store (last 100)
	concepts, err := co.store.FindByRegime(ctx, stream.CurrentRegime, 100)
	if err != nil {
		// Log error but don't stop streaming
		return &CognitionEvent{
			SessionID: stream.SessionID,
			Timestamp: now,
			EventType: EventStateSnapshot,
			Regime:    stream.CurrentRegime,
			Message:   fmt.Sprintf("⚠️ Failed to query concepts: %v", err),
		}
	}

	// Build current state
	state := &CognitiveState{
		ActiveConcepts:      concepts,
		ConnectionGraph:     co.buildConnectionGraph(concepts),
		WorkingMemory:       co.extractQuaternions(concepts),
		Confidence:          co.calculateConfidence(concepts),
		Coherence:           co.calculateCoherence(concepts),
		Entropy:             co.calculateEntropy(concepts),
		CurrentRegime:       stream.CurrentRegime,
		RegimeProgress:      co.calculateRegimeProgress(stream),
		ClusterDistribution: co.buildClusterDistribution(concepts),
		CapturedAt:          now,
	}

	// Calculate delta from last state
	var delta *StateDelta
	if stream.LastState != nil {
		delta = co.calculateDelta(stream.LastState, state)
	}

	// Determine event type based on delta
	eventType := EventStateSnapshot
	message := "📊 State snapshot"

	if delta != nil {
		if len(delta.NewConcepts) > 0 {
			eventType = EventConceptFormed
			message = fmt.Sprintf("💡 Formed %d new concept(s)", len(delta.NewConcepts))
		} else if len(delta.NewConnections) > 0 {
			eventType = EventConnectionMade
			message = fmt.Sprintf("🔗 Made %d new connection(s)", len(delta.NewConnections))
		} else if delta.RegimeChange != nil {
			eventType = EventRegimeShift
			message = fmt.Sprintf("🔄 Regime shift: %s → %s", delta.RegimeChange.From, delta.RegimeChange.To)
		}
	}

	return &CognitionEvent{
		SessionID:    stream.SessionID,
		Timestamp:    now,
		EventType:    eventType,
		Regime:       stream.CurrentRegime,
		CurrentState: state,
		Delta:        delta,
		Message:      message,
	}
}

// buildConnectionGraph creates graph from concepts
func (co *CognitionObserver) buildConnectionGraph(concepts []*QuaternionConcept) *ConnectionGraph {
	graph := &ConnectionGraph{
		Nodes: make(map[uuid.UUID]*ConceptNode),
		Edges: []*Connection{},
	}

	// Create nodes
	for _, concept := range concepts {
		node := &ConceptNode{
			ID:          concept.ID,
			Label:       co.extractLabel(concept),
			Quaternion:  concept.Quaternion,
			DigitalRoot: concept.DigitalRoot,
			Confidence:  concept.Confidence,
			Regime:      concept.Regime,
			Size:        concept.Confidence * 10, // Scale by confidence
			Color:       co.digitalRootColor(concept.DigitalRoot),
		}

		graph.Nodes[concept.ID] = node
	}

	// Create edges (connect similar concepts)
	threshold := 0.7 // Similarity threshold
	for i, c1 := range concepts {
		for j := i + 1; j < len(concepts); j++ {
			c2 := concepts[j]

			// Calculate quaternion similarity (dot product)
			similarity := c1.Quaternion.W*c2.Quaternion.W +
				c1.Quaternion.X*c2.Quaternion.X +
				c1.Quaternion.Y*c2.Quaternion.Y +
				c1.Quaternion.Z*c2.Quaternion.Z

			if similarity > threshold {
				edge := &Connection{
					ID:         fmt.Sprintf("%s-%s", c1.ID.String(), c2.ID.String()),
					Source:     c1.ID,
					Target:     c2.ID,
					Similarity: similarity,
					Strength:   similarity,
					Type:       "semantic",
					CreatedAt:  time.Now(),
				}

				graph.Edges = append(graph.Edges, edge)
			}
		}
	}

	return graph
}

// extractQuaternions extracts quaternion array from concepts
func (co *CognitionObserver) extractQuaternions(concepts []*QuaternionConcept) []vqc.Quaternion {
	quaternions := make([]vqc.Quaternion, len(concepts))
	for i, concept := range concepts {
		quaternions[i] = concept.Quaternion
	}
	return quaternions
}

// calculateConfidence computes overall confidence score
func (co *CognitionObserver) calculateConfidence(concepts []*QuaternionConcept) float64 {
	if len(concepts) == 0 {
		return 0.0
	}

	// Use harmonic mean for rigorous averaging
	values := make([]float64, len(concepts))
	for i, concept := range concepts {
		values[i] = concept.Confidence
	}

	return HarmonicMean(values)
}

// calculateCoherence measures how well concepts relate
func (co *CognitionObserver) calculateCoherence(concepts []*QuaternionConcept) float64 {
	if len(concepts) < 2 {
		return 1.0
	}

	// Average pairwise similarity
	totalSim := 0.0
	count := 0

	for i := 0; i < len(concepts) && i < 20; i++ { // Limit to 20 for performance
		for j := i + 1; j < len(concepts) && j < 20; j++ {
			sim := concepts[i].Quaternion.W*concepts[j].Quaternion.W +
				concepts[i].Quaternion.X*concepts[j].Quaternion.X +
				concepts[i].Quaternion.Y*concepts[j].Quaternion.Y +
				concepts[i].Quaternion.Z*concepts[j].Quaternion.Z
			totalSim += sim
			count++
		}
	}

	if count == 0 {
		return 1.0
	}

	return totalSim / float64(count)
}

// calculateEntropy measures uncertainty
func (co *CognitionObserver) calculateEntropy(concepts []*QuaternionConcept) float64 {
	if len(concepts) == 0 {
		return 0.0
	}

	// Calculate entropy from confidence distribution
	entropy := 0.0
	for _, concept := range concepts {
		p := concept.Confidence
		if p > 0 {
			entropy -= p * math.Log2(p)
		}
	}

	// Normalize by log(n)
	maxEntropy := math.Log2(float64(len(concepts)))
	if maxEntropy > 0 {
		return entropy / maxEntropy
	}

	return 0.0
}

// calculateRegimeProgress estimates progress in current regime
func (co *CognitionObserver) calculateRegimeProgress(stream *ThoughtStream) float64 {
	// Simple time-based progress for now
	// TODO: Make this more sophisticated based on actual reasoning state

	elapsed := time.Since(stream.StartTime).Seconds()

	// Target durations per regime (in seconds)
	var target float64
	switch stream.CurrentRegime {
	case RegimeExploration:
		target = 30.0 // 30% of 100s = 30s
	case RegimeOptimization:
		target = 20.0 // 20% of 100s = 20s
	case RegimeStabilization:
		target = 50.0 // 50% of 100s = 50s
	}

	progress := elapsed / target
	if progress > 1.0 {
		progress = 1.0
	}

	return progress
}

// buildClusterDistribution counts concepts per digital root
func (co *CognitionObserver) buildClusterDistribution(concepts []*QuaternionConcept) map[uint8]int {
	dist := make(map[uint8]int)

	for _, concept := range concepts {
		dist[concept.DigitalRoot]++
	}

	return dist
}

// calculateDelta compares two states
func (co *CognitionObserver) calculateDelta(oldState, newState *CognitiveState) *StateDelta {
	delta := &StateDelta{
		ConfidenceChange: newState.Confidence - oldState.Confidence,
	}

	// Find new concepts
	oldIDs := make(map[uuid.UUID]bool)
	for _, concept := range oldState.ActiveConcepts {
		oldIDs[concept.ID] = true
	}

	for _, concept := range newState.ActiveConcepts {
		if !oldIDs[concept.ID] {
			delta.NewConcepts = append(delta.NewConcepts, concept)
		}
	}

	// Find new connections
	oldEdgeIDs := make(map[string]bool)
	for _, edge := range oldState.ConnectionGraph.Edges {
		oldEdgeIDs[edge.ID] = true
	}

	for _, edge := range newState.ConnectionGraph.Edges {
		if !oldEdgeIDs[edge.ID] {
			delta.NewConnections = append(delta.NewConnections, edge)
		}
	}

	// Check regime change
	if oldState.CurrentRegime != newState.CurrentRegime {
		delta.RegimeChange = &RegimeTransition{
			From:      oldState.CurrentRegime,
			To:        newState.CurrentRegime,
			Reason:    "Progress threshold reached",
			Progress:  newState.RegimeProgress,
			Timestamp: time.Now(),
		}
	}

	return delta
}

// extractLabel gets human-readable label from concept
func (co *CognitionObserver) extractLabel(concept *QuaternionConcept) string {
	if label, ok := concept.Data["label"].(string); ok {
		return label
	}
	if text, ok := concept.Data["text"].(string); ok {
		if len(text) > 30 {
			return text[:30] + "..."
		}
		return text
	}
	return fmt.Sprintf("Concept %s", concept.ID.String()[:8])
}

// digitalRootColor maps digital root to color
func (co *CognitionObserver) digitalRootColor(root uint8) string {
	colors := []string{
		"#FF6B6B", // 0 - Red
		"#4ECDC4", // 1 - Teal
		"#45B7D1", // 2 - Blue
		"#96CEB4", // 3 - Green
		"#FFEAA7", // 4 - Yellow
		"#DFE6E9", // 5 - Gray
		"#A29BFE", // 6 - Purple
		"#FD79A8", // 7 - Pink
		"#FDCB6E", // 8 - Orange
		"#6C5CE7", // 9 - Violet
	}

	if root < uint8(len(colors)) {
		return colors[root]
	}
	return "#000000"
}

// GetStream retrieves an active stream
func (co *CognitionObserver) GetStream(sessionID string) (*ThoughtStream, error) {
	co.streamsMu.RLock()
	defer co.streamsMu.RUnlock()

	stream, exists := co.streams[sessionID]
	if !exists {
		return nil, fmt.Errorf("session %s not found", sessionID)
	}

	return stream, nil
}

// ListActiveSessions returns all active session IDs
func (co *CognitionObserver) ListActiveSessions() []string {
	co.streamsMu.RLock()
	defer co.streamsMu.RUnlock()

	sessions := make([]string, 0, len(co.streams))
	for id, stream := range co.streams {
		if stream.Active {
			sessions = append(sessions, id)
		}
	}

	return sessions
}

// EmitThought manually emits a thought event
func (co *CognitionObserver) EmitThought(sessionID, message, emoji string) error {
	stream, err := co.GetStream(sessionID)
	if err != nil {
		return err
	}

	if !stream.Active {
		return fmt.Errorf("session %s not active", sessionID)
	}

	event := &CognitionEvent{
		SessionID: sessionID,
		Timestamp: time.Now(),
		EventType: EventThought,
		Regime:    stream.CurrentRegime,
		Message:   fmt.Sprintf("%s %s", emoji, message),
	}

	stream.EventChannel <- event
	stream.EventCount++

	return nil
}

// ShiftRegime manually triggers a regime transition
func (co *CognitionObserver) ShiftRegime(sessionID string, newRegime Regime, reason string) error {
	stream, err := co.GetStream(sessionID)
	if err != nil {
		return err
	}

	if !stream.Active {
		return fmt.Errorf("session %s not active", sessionID)
	}

	oldRegime := stream.CurrentRegime
	stream.CurrentRegime = newRegime

	event := &CognitionEvent{
		SessionID: sessionID,
		Timestamp: time.Now(),
		EventType: EventRegimeShift,
		Regime:    newRegime,
		Message:   fmt.Sprintf("🔄 Regime shift: %s → %s", oldRegime, newRegime),
		Delta: &StateDelta{
			RegimeChange: &RegimeTransition{
				From:      oldRegime,
				To:        newRegime,
				Reason:    reason,
				Progress:  0.0,
				Timestamp: time.Now(),
			},
		},
	}

	stream.EventChannel <- event
	stream.EventCount++

	return nil
}
