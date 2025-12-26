package cognition_test

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/cognition"
	"github.com/google/uuid"
)

// ExampleBasicObservation demonstrates basic cognition observation
func ExampleBasicObservation() {
	// Create components
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)

	ctx := context.Background()
	sessionID := "example-session"

	// Start observing
	stream, err := observer.StartObserving(ctx, sessionID)
	if err != nil {
		panic(err)
	}

	// Emit some thoughts
	observer.EmitThought(sessionID, "Starting to think about the problem", "💭")
	time.Sleep(100 * time.Millisecond)

	observer.EmitThought(sessionID, "Found an interesting pattern!", "🔍")
	time.Sleep(100 * time.Millisecond)

	// Shift regime
	observer.ShiftRegime(sessionID, cognition.RegimeOptimization, "Pattern found, optimizing")
	time.Sleep(100 * time.Millisecond)

	observer.EmitThought(sessionID, "Solution converging...", "⚡")

	// Stop observing
	observer.StopObserving(sessionID)

	// Print events
	fmt.Println("Cognition stream events:")
	for event := range stream.EventChannel {
		fmt.Printf("[%s] %s: %s\n",
			event.EventType,
			event.Regime,
			event.Message,
		)
	}

	// Output (example):
	// Cognition stream events:
	// [STATE_SNAPSHOT] EXPLORATION: 🧠 Cognition observation started
	// [THOUGHT] EXPLORATION: 💭 Starting to think about the problem
	// [THOUGHT] EXPLORATION: 🔍 Found an interesting pattern!
	// [REGIME_SHIFT] OPTIMIZATION: 🔄 Regime shift: EXPLORATION → OPTIMIZATION
	// [THOUGHT] OPTIMIZATION: ⚡ Solution converging...
	// [STATE_SNAPSHOT] OPTIMIZATION: ✅ Cognition observation ended
}

// ExampleObservableEmitter demonstrates clean frontend events
func ExampleObservableEmitter() {
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)
	wsServer := cognition.NewCognitionWebSocket(observer)
	emitter := cognition.NewObservableEmitter(observer, wsServer)

	ctx := context.Background()
	sessionID := "frontend-session"

	// Start session
	emitter.StartSession(sessionID)
	observer.StartObserving(ctx, sessionID)

	// Emit clean phases for frontend
	emitter.EmitVoidState(ctx, sessionID, "Understanding your question...")
	time.Sleep(100 * time.Millisecond)

	emitter.EmitProgress(ctx, sessionID, 0.15, "Analyzing context...")
	time.Sleep(100 * time.Millisecond)

	emitter.EmitFlowState(ctx, sessionID, "Processing patterns...")
	time.Sleep(100 * time.Millisecond)

	emitter.EmitProgress(ctx, sessionID, 0.6, "Generating response...")
	time.Sleep(100 * time.Millisecond)

	emitter.EmitSolutionState(ctx, sessionID, "Complete!")

	// Stop
	observer.StopObserving(sessionID)
	emitter.StopSession(sessionID)

	fmt.Println("Observable events emitted to frontend!")

	// Output:
	// Observable events emitted to frontend!
}

// ExampleRecording demonstrates session recording and replay
func ExampleRecording() {
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)
	recorder := cognition.NewThoughtRecorder(store, "./test_recordings")

	ctx := context.Background()
	sessionID := "recording-session"

	// Start observing
	stream, _ := observer.StartObserving(ctx, sessionID)

	// Start recording
	recorder.StartRecording(stream)

	// Emit some events
	observer.EmitThought(sessionID, "Recording this thought", "🎬")
	time.Sleep(100 * time.Millisecond)

	observer.EmitThought(sessionID, "And this one too", "📹")

	// Stop and save recording
	recording, _ := recorder.StopRecording(stream)
	recorder.SaveRecording(ctx, recording)

	observer.StopObserving(sessionID)

	fmt.Printf("Recorded %d events\n", recording.TotalEvents)
	fmt.Printf("Recording ID: %s\n", recording.ID.String()[:8])

	// Replay at 2x speed
	replayStream, _ := recorder.Replay(ctx, recording.ID, 2.0)

	fmt.Println("Replaying at 2x speed...")
	for event := range replayStream.EventChannel {
		if event.EventType == cognition.EventThought {
			fmt.Printf("  [REPLAY] %s\n", event.Message)
		}
	}

	// Output (example):
	// Recorded 2 events
	// Recording ID: abc12345
	// Replaying at 2x speed...
	//   [REPLAY] 🔁 [REPLAY 2.0x] 🎬 Recording this thought
	//   [REPLAY] 🔁 [REPLAY 2.0x] 📹 And this one too
}

// ExampleIntervention demonstrates mid-process reasoning steering
func ExampleIntervention() {
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)
	intervention := cognition.NewInterventionEngine(observer, store)

	ctx := context.Background()
	sessionID := "intervention-session"

	// Start observing
	observer.StartObserving(ctx, sessionID)

	// Create a concept
	conceptID := uuid.New()
	concept := &cognition.QuaternionConcept{
		ID:             conceptID,
		Confidence:     0.5,
		HarmonicWeight: 1.0,
		Regime:         cognition.RegimeOptimization,
		Data:           make(map[string]interface{}),
	}
	store.Insert(ctx, concept)

	fmt.Printf("Initial confidence: %.2f\n", concept.Confidence)

	// Amplify the concept
	req := &cognition.InterventionRequest{
		SessionID:     sessionID,
		TargetConcept: conceptID,
		Action:        "amplify",
		Strength:      0.3,
		Reason:        "This is the critical insight!",
	}

	intervention.ApplyIntervention(ctx, req)

	// Check updated confidence
	updatedConcept, _ := store.GetByID(ctx, conceptID)
	fmt.Printf("After amplify: %.2f\n", updatedConcept.Confidence)

	observer.StopObserving(sessionID)

	// Output (example):
	// Initial confidence: 0.50
	// After amplify: 0.65
}

// TestCognitionBasic is a simple test to verify compilation
func TestCognitionBasic(t *testing.T) {
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)

	ctx := context.Background()
	stream, err := observer.StartObserving(ctx, "test-session")
	if err != nil {
		t.Fatal(err)
	}

	// Emit a thought
	observer.EmitThought("test-session", "I'm thinking!", "💭")

	// Receive event
	select {
	case event := <-stream.EventChannel:
		if event.EventType != cognition.EventThought {
			t.Errorf("Expected THOUGHT, got %s", event.EventType)
		}
		if event.Message != "💭 I'm thinking!" {
			t.Errorf("Unexpected message: %s", event.Message)
		}
	case <-time.After(time.Second):
		t.Fatal("Timeout waiting for event")
	}

	observer.StopObserving("test-session")
}

// TestTeslaFrequency verifies 4.909 Hz streaming
func TestTeslaFrequency(t *testing.T) {
	store := cognition.NewQuaternionStore()
	observer := cognition.NewCognitionObserver(store)

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	stream, err := observer.StartObserving(ctx, "frequency-test")
	if err != nil {
		t.Fatal(err)
	}

	// Count events in 1 second
	start := time.Now()
	eventCount := 0

	for {
		select {
		case event := <-stream.EventChannel:
			if time.Since(start) < time.Second {
				if event.EventType == cognition.EventStateSnapshot {
					eventCount++
				}
			}
		case <-time.After(1100 * time.Millisecond):
			goto done
		}
	}

done:
	// Should receive ~4-5 events in 1 second (4.909 Hz)
	if eventCount < 3 || eventCount > 6 {
		t.Errorf("Expected ~4-5 events in 1 second, got %d", eventCount)
	}

	observer.StopObserving("frequency-test")
	t.Logf("Received %d events in 1 second (expected ~4.909 Hz)", eventCount)
}
