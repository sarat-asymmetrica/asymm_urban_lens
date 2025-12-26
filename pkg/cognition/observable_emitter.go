package cognition

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"sync"
	"time"
)

// ============================================================================
// OBSERVABLE EVENT EMITTER - Bridge VOID→FLOW→SOLUTION to WebSocket
// ============================================================================
//
// Translates internal reasoning states to clean, professional frontend events
// NO mystical language in user-facing messages
// Internal: VOID/FLOW/SOLUTION → Frontend: Planning/Processing/Complete
//
// ============================================================================

// ObservableEventType defines frontend-facing event types
type ObservableEventType string

const (
	// Phase state events (clean names for frontend)
	ObservableVoidState     ObservableEventType = "void_state"     // Internal: VOID → Frontend: "Planning"
	ObservableFlowState     ObservableEventType = "flow_state"     // Internal: FLOW → Frontend: "Processing"
	ObservableSolutionState ObservableEventType = "solution_state" // Internal: SOLUTION → Frontend: "Complete"

	// Progress and detail events
	ObservableProgress      ObservableEventType = "progress" // Progress updates (0.0-1.0)
	ObservableDetailEvent   ObservableEventType = "event"    // Individual reasoning steps
	ObservableError         ObservableEventType = "error"    // Error occurred
)

// PhaseType defines clean phase names for frontend
type PhaseType string

const (
	PhasePlanning    PhaseType = "planning"    // VOID phase (exploration)
	PhaseProcessing  PhaseType = "processing"  // FLOW phase (optimization)
	PhaseComplete    PhaseType = "complete"    // SOLUTION phase (verification)
)

// ObservableEvent is the frontend-facing event structure
type ObservableEvent struct {
	Type      ObservableEventType    `json:"type"`       // Event type
	Phase     PhaseType              `json:"phase"`      // Current phase
	Progress  float64                `json:"progress"`   // 0.0 to 1.0
	Message   string                 `json:"message"`    // Clean technical description
	Timestamp time.Time              `json:"timestamp"`  // When event occurred
	EventID   string                 `json:"event_id"`   // Unique event identifier
	Metadata  map[string]interface{} `json:"metadata,omitempty"` // Additional data
}

// ObservableEmitter bridges internal reasoning to WebSocket
type ObservableEmitter struct {
	observer     *CognitionObserver
	wsServer     *CognitionWebSocket
	mu           sync.RWMutex
	activeSessions map[string]*emitterSession
	logger       *log.Logger
}

// emitterSession tracks emission state for one session
type emitterSession struct {
	sessionID      string
	currentPhase   PhaseType
	currentProgress float64
	eventCount     int
	startTime      time.Time
}

// NewObservableEmitter creates a new event emitter
func NewObservableEmitter(observer *CognitionObserver, wsServer *CognitionWebSocket) *ObservableEmitter {
	return &ObservableEmitter{
		observer:       observer,
		wsServer:       wsServer,
		activeSessions: make(map[string]*emitterSession),
		logger:         log.New(log.Writer(), "[OBSERVABLE_EMITTER] ", log.LstdFlags),
	}
}

// StartSession begins emitting events for a session
func (oe *ObservableEmitter) StartSession(sessionID string) error {
	oe.mu.Lock()
	defer oe.mu.Unlock()

	if _, exists := oe.activeSessions[sessionID]; exists {
		return fmt.Errorf("session %s already active", sessionID)
	}

	session := &emitterSession{
		sessionID:      sessionID,
		currentPhase:   PhasePlanning,
		currentProgress: 0.0,
		eventCount:     0,
		startTime:      time.Now(),
	}

	oe.activeSessions[sessionID] = session
	oe.logger.Printf("Started emission for session %s", sessionID)

	return nil
}

// StopSession stops emitting events for a session
func (oe *ObservableEmitter) StopSession(sessionID string) {
	oe.mu.Lock()
	defer oe.mu.Unlock()

	delete(oe.activeSessions, sessionID)
	oe.logger.Printf("Stopped emission for session %s", sessionID)
}

// EmitVoidState emits VOID phase start (Planning)
func (oe *ObservableEmitter) EmitVoidState(ctx context.Context, sessionID string, message string) error {
	return oe.emitPhaseTransition(ctx, sessionID, PhasePlanning, ObservableVoidState, 0.0, message)
}

// EmitFlowState emits FLOW phase start (Processing)
func (oe *ObservableEmitter) EmitFlowState(ctx context.Context, sessionID string, message string) error {
	return oe.emitPhaseTransition(ctx, sessionID, PhaseProcessing, ObservableFlowState, 0.3, message)
}

// EmitSolutionState emits SOLUTION phase start (Complete)
func (oe *ObservableEmitter) EmitSolutionState(ctx context.Context, sessionID string, message string) error {
	return oe.emitPhaseTransition(ctx, sessionID, PhaseComplete, ObservableSolutionState, 0.5, message)
}

// EmitProgress emits a progress update
func (oe *ObservableEmitter) EmitProgress(ctx context.Context, sessionID string, progress float64, message string) error {
	oe.mu.RLock()
	session, exists := oe.activeSessions[sessionID]
	oe.mu.RUnlock()

	if !exists {
		return fmt.Errorf("session %s not active", sessionID)
	}

	// Update session progress
	oe.mu.Lock()
	session.currentProgress = progress
	session.eventCount++
	oe.mu.Unlock()

	event := ObservableEvent{
		Type:      ObservableProgress,
		Phase:     session.currentPhase,
		Progress:  progress,
		Message:   message,
		Timestamp: time.Now(),
		EventID:   fmt.Sprintf("%s-%d", sessionID, session.eventCount),
		Metadata:  map[string]interface{}{},
	}

	return oe.broadcastEvent(sessionID, event)
}

// EmitEvent emits a detailed reasoning step
func (oe *ObservableEmitter) EmitEvent(ctx context.Context, sessionID string, message string, metadata map[string]interface{}) error {
	oe.mu.RLock()
	session, exists := oe.activeSessions[sessionID]
	oe.mu.RUnlock()

	if !exists {
		return fmt.Errorf("session %s not active", sessionID)
	}

	oe.mu.Lock()
	session.eventCount++
	eventCount := session.eventCount
	oe.mu.Unlock()

	event := ObservableEvent{
		Type:      ObservableDetailEvent,
		Phase:     session.currentPhase,
		Progress:  session.currentProgress,
		Message:   message,
		Timestamp: time.Now(),
		EventID:   fmt.Sprintf("%s-%d", sessionID, eventCount),
		Metadata:  metadata,
	}

	return oe.broadcastEvent(sessionID, event)
}

// EmitError emits an error event
func (oe *ObservableEmitter) EmitError(ctx context.Context, sessionID string, err error) error {
	oe.mu.RLock()
	session, exists := oe.activeSessions[sessionID]
	oe.mu.RUnlock()

	if !exists {
		return fmt.Errorf("session %s not active", sessionID)
	}

	oe.mu.Lock()
	session.eventCount++
	eventCount := session.eventCount
	oe.mu.Unlock()

	event := ObservableEvent{
		Type:      ObservableError,
		Phase:     session.currentPhase,
		Progress:  session.currentProgress,
		Message:   err.Error(),
		Timestamp: time.Now(),
		EventID:   fmt.Sprintf("%s-%d", sessionID, eventCount),
		Metadata: map[string]interface{}{
			"error": err.Error(),
		},
	}

	return oe.broadcastEvent(sessionID, event)
}

// emitPhaseTransition handles phase state transitions
func (oe *ObservableEmitter) emitPhaseTransition(ctx context.Context, sessionID string, phase PhaseType, eventType ObservableEventType, progress float64, message string) error {
	oe.mu.Lock()
	session, exists := oe.activeSessions[sessionID]
	if !exists {
		oe.mu.Unlock()
		return fmt.Errorf("session %s not active", sessionID)
	}

	session.currentPhase = phase
	session.currentProgress = progress
	session.eventCount++
	eventCount := session.eventCount
	oe.mu.Unlock()

	event := ObservableEvent{
		Type:      eventType,
		Phase:     phase,
		Progress:  progress,
		Message:   message,
		Timestamp: time.Now(),
		EventID:   fmt.Sprintf("%s-%d", sessionID, eventCount),
		Metadata:  map[string]interface{}{},
	}

	// Also emit to cognition observer (for recording)
	if oe.observer != nil {
		cogEvent := oe.toCognitionEvent(sessionID, event)
		stream, err := oe.observer.GetStream(sessionID)
		if err == nil && stream.Active {
			select {
			case stream.EventChannel <- cogEvent:
				// Event sent to observer
			default:
				oe.logger.Printf("Warning: Observer event channel full for session %s", sessionID)
			}
		}
	}

	return oe.broadcastEvent(sessionID, event)
}

// broadcastEvent sends event to WebSocket clients
func (oe *ObservableEmitter) broadcastEvent(sessionID string, event ObservableEvent) error {
	if oe.wsServer == nil {
		oe.logger.Printf("Warning: WebSocket server not configured, event not broadcast")
		return nil
	}

	// Serialize event
	eventData, err := json.Marshal(event)
	if err != nil {
		return fmt.Errorf("failed to serialize event: %w", err)
	}

	// Wrap in WSMessage
	wsMsg := WSMessage{
		Type:      "observable_event",
		SessionID: sessionID,
		Data:      json.RawMessage(eventData),
		Timestamp: time.Now(),
	}

	// Broadcast to session
	oe.wsServer.Broadcast(wsMsg)

	oe.logger.Printf("Broadcasted %s event for session %s: %s", event.Type, sessionID, event.Message)

	return nil
}

// toCognitionEvent converts ObservableEvent to CognitionEvent
func (oe *ObservableEmitter) toCognitionEvent(sessionID string, event ObservableEvent) *CognitionEvent {
	// Map phase to regime
	var regime Regime
	switch event.Phase {
	case PhasePlanning:
		regime = RegimeExploration
	case PhaseProcessing:
		regime = RegimeOptimization
	case PhaseComplete:
		regime = RegimeStabilization
	default:
		regime = RegimeExploration
	}

	// Map observable event type to cognition event type
	var eventType EventType
	switch event.Type {
	case ObservableVoidState, ObservableFlowState, ObservableSolutionState:
		eventType = EventRegimeShift
	case ObservableProgress:
		eventType = EventThought
	case ObservableDetailEvent:
		eventType = EventPatternDetected
	case ObservableError:
		eventType = EventThought
	default:
		eventType = EventThought
	}

	return &CognitionEvent{
		SessionID: sessionID,
		Timestamp: event.Timestamp,
		EventType: eventType,
		Regime:    regime,
		Message:   event.Message,
		Metadata:  event.Metadata,
	}
}

// GetSessionStats returns statistics for a session
func (oe *ObservableEmitter) GetSessionStats(sessionID string) (map[string]interface{}, error) {
	oe.mu.RLock()
	defer oe.mu.RUnlock()

	session, exists := oe.activeSessions[sessionID]
	if !exists {
		return nil, fmt.Errorf("session %s not found", sessionID)
	}

	return map[string]interface{}{
		"session_id":      session.sessionID,
		"current_phase":   session.currentPhase,
		"current_progress": session.currentProgress,
		"event_count":     session.eventCount,
		"elapsed_time":    time.Since(session.startTime).Seconds(),
	}, nil
}

// ============================================================================
// HELPER FUNCTIONS - For integration with VOID→FLOW→SOLUTION engine
// ============================================================================

// EmitFromMathEngine emits events from mathematical reasoning engine
func (oe *ObservableEmitter) EmitFromMathEngine(ctx context.Context, sessionID string, phase string, progress float64, message string, metadata map[string]interface{}) error {
	// Translate internal phase names to frontend names
	switch phase {
	case "VOID_ACCESS":
		if progress == 0.0 {
			return oe.EmitVoidState(ctx, sessionID, message)
		}
		return oe.EmitProgress(ctx, sessionID, progress, message)

	case "FLOW_CONVERGENCE":
		if progress == 0.3 {
			return oe.EmitFlowState(ctx, sessionID, message)
		}
		return oe.EmitProgress(ctx, sessionID, progress, message)

	case "SOLUTION_SUPPORT":
		if progress == 0.5 {
			return oe.EmitSolutionState(ctx, sessionID, message)
		}
		return oe.EmitProgress(ctx, sessionID, progress, message)

	default:
		return oe.EmitEvent(ctx, sessionID, message, metadata)
	}
}

// EmitDigitalRootPattern emits digital root classification event
func (oe *ObservableEmitter) EmitDigitalRootPattern(ctx context.Context, sessionID string, digitalRoot uint8, value float64) error {
	message := fmt.Sprintf("Pattern detected: Digital root %d (value: %.3f)", digitalRoot, value)
	metadata := map[string]interface{}{
		"digital_root": digitalRoot,
		"value":        value,
		"cluster":      digitalRoot,
	}

	return oe.EmitEvent(ctx, sessionID, message, metadata)
}

// EmitHypothesisGenerated emits hypothesis generation event
func (oe *ObservableEmitter) EmitHypothesisGenerated(ctx context.Context, sessionID string, method string, confidence float64) error {
	message := fmt.Sprintf("Generated hypothesis using %s (confidence: %.2f)", method, confidence)
	metadata := map[string]interface{}{
		"method":     method,
		"confidence": confidence,
	}

	return oe.EmitEvent(ctx, sessionID, message, metadata)
}

// EmitConvergence emits convergence event
func (oe *ObservableEmitter) EmitConvergence(ctx context.Context, sessionID string, dimension float64, hypothesesCount int) error {
	message := fmt.Sprintf("Convergence at dimension %.3f with %d hypotheses", dimension, hypothesesCount)
	metadata := map[string]interface{}{
		"dimension":        dimension,
		"hypotheses_count": hypothesesCount,
	}

	return oe.EmitEvent(ctx, sessionID, message, metadata)
}
