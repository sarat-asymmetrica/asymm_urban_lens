package cognition

import (
	"context"
	"fmt"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/resilience"
)

// captureCurrentStateWithTimeout wraps captureCurrentState with 5s timeout
// Use this in streamEvents() instead of calling captureCurrentState directly
func (co *CognitionObserver) captureCurrentStateWithTimeout(ctx context.Context, stream *ThoughtStream) *CognitionEvent {
	// Wrap the entire capture operation in a timeout (5 seconds for cognition snapshots)
	event, err := resilience.WithCognitionTimeoutResult(ctx, func() (*CognitionEvent, error) {
		return co.captureCurrentState(ctx, stream), nil
	})

	if err != nil {
		// Timeout occurred - return error event
		return &CognitionEvent{
			SessionID: stream.SessionID,
			Timestamp: time.Now(),
			EventType: EventStateSnapshot,
			Regime:    stream.CurrentRegime,
			Message:   fmt.Sprintf("⚠️ Snapshot timeout after 5s: %v", err),
		}
	}

	return event
}

// findByRegimeWithTimeout wraps store queries with 5s timeout
func (co *CognitionObserver) findByRegimeWithTimeout(ctx context.Context, regime Regime, limit int) ([]*QuaternionConcept, error) {
	return resilience.WithCognitionTimeoutResult(ctx, func() ([]*QuaternionConcept, error) {
		return co.store.FindByRegime(ctx, regime, limit)
	})
}
