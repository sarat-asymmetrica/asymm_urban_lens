package cognition

import (
	"context"
	"fmt"
	"math"

	"github.com/asymmetrica/urbanlens/pkg/vqc"
	"github.com/google/uuid"
)

// ============================================================================
// INTERVENTION SYSTEM - Steer reasoning mid-process
// ============================================================================
//
// Allows external steering of cognitive processes through:
// - Amplify: Increase concept strength
// - Suppress: Decrease concept strength
// - Redirect: Rotate concept in quaternion space
//
// Uses quaternion rotations for smooth, mathematically precise interventions
//
// ============================================================================

// InterventionEngine handles reasoning interventions
type InterventionEngine struct {
	observer *CognitionObserver
	store    *QuaternionStore
}

// NewInterventionEngine creates a new intervention engine
func NewInterventionEngine(observer *CognitionObserver, store *QuaternionStore) *InterventionEngine {
	return &InterventionEngine{
		observer: observer,
		store:    store,
	}
}

// ApplyIntervention processes an intervention request
func (ie *InterventionEngine) ApplyIntervention(ctx context.Context, req *InterventionRequest) error {
	// Validate request
	if err := ie.validateRequest(req); err != nil {
		return fmt.Errorf("invalid intervention: %w", err)
	}

	// Get the concept being affected
	concept, err := ie.store.GetByID(ctx, req.TargetConcept)
	if err != nil {
		return fmt.Errorf("concept not found: %w", err)
	}

	// Apply intervention based on action
	switch req.Action {
	case "amplify":
		return ie.amplify(ctx, concept, req)
	case "suppress":
		return ie.suppress(ctx, concept, req)
	case "redirect":
		return ie.redirect(ctx, concept, req)
	default:
		return fmt.Errorf("unknown action: %s", req.Action)
	}
}

// amplify increases concept strength (confidence and harmonic weight)
func (ie *InterventionEngine) amplify(ctx context.Context, concept *QuaternionConcept, req *InterventionRequest) error {
	// Increase confidence by strength factor (capped at 1.0)
	newConfidence := concept.Confidence * (1.0 + req.Strength)
	if newConfidence > 1.0 {
		newConfidence = 1.0
	}

	// Increase harmonic weight
	newWeight := concept.HarmonicWeight * 1.618 * req.Strength // Golden ratio
	if newWeight > 10.0 {
		newWeight = 10.0 // Cap at 10
	}

	// Update concept
	concept.Confidence = newConfidence
	concept.HarmonicWeight = newWeight
	concept.HumanAnnotation = fmt.Sprintf("Amplified by %.1f×: %s", req.Strength, req.Reason)

	if err := ie.store.Update(ctx, concept); err != nil {
		return fmt.Errorf("failed to update concept: %w", err)
	}

	// Emit event
	return ie.observer.EmitThought(
		req.SessionID,
		fmt.Sprintf("Amplified concept %s by %.1f×", req.TargetConcept.String()[:8], req.Strength),
		"📈",
	)
}

// suppress decreases concept strength
func (ie *InterventionEngine) suppress(ctx context.Context, concept *QuaternionConcept, req *InterventionRequest) error {
	// Decrease confidence by strength factor (floored at 0.0)
	newConfidence := concept.Confidence * (1.0 - req.Strength)
	if newConfidence < 0.0 {
		newConfidence = 0.0
	}

	// Decrease harmonic weight
	newWeight := concept.HarmonicWeight * (1.0 - req.Strength)
	if newWeight < 0.1 {
		newWeight = 0.1 // Minimum weight
	}

	// Update concept
	concept.Confidence = newConfidence
	concept.HarmonicWeight = newWeight
	concept.HumanAnnotation = fmt.Sprintf("Suppressed by %.1f×: %s", req.Strength, req.Reason)

	if err := ie.store.Update(ctx, concept); err != nil {
		return fmt.Errorf("failed to update concept: %w", err)
	}

	// Emit event
	return ie.observer.EmitThought(
		req.SessionID,
		fmt.Sprintf("Suppressed concept %s by %.1f×", req.TargetConcept.String()[:8], req.Strength),
		"📉",
	)
}

// redirect rotates concept in quaternion space
func (ie *InterventionEngine) redirect(ctx context.Context, concept *QuaternionConcept, req *InterventionRequest) error {
	if req.Direction == nil {
		return fmt.Errorf("redirect requires direction quaternion")
	}

	// Normalize direction
	direction := req.Direction.Normalize()

	// Use SLERP to smoothly rotate concept toward direction
	// t = strength (0.0 = no change, 1.0 = full rotation)
	rotated := vqc.SLERP(
		concept.Quaternion,
		direction,
		req.Strength,
	)

	// Update quaternion
	concept.Quaternion = rotated

	// Recalculate digital root (may change cluster!)
	newDR := CalculateDigitalRootFromQuaternion(rotated)
	oldDR := concept.DigitalRoot
	concept.DigitalRoot = newDR

	concept.HumanAnnotation = fmt.Sprintf("Redirected by %.1f%% toward target: %s", req.Strength*100, req.Reason)

	if err := ie.store.Update(ctx, concept); err != nil {
		return fmt.Errorf("failed to update concept: %w", err)
	}

	// Emit event
	return ie.observer.EmitThought(
		req.SessionID,
		fmt.Sprintf("Redirected concept %s (DR: %d → %d)", req.TargetConcept.String()[:8], oldDR, newDR),
		"🧭",
	)
}

// validateRequest checks intervention request validity
func (ie *InterventionEngine) validateRequest(req *InterventionRequest) error {
	if req.SessionID == "" {
		return fmt.Errorf("session_id required")
	}

	if req.TargetConcept == uuid.Nil {
		return fmt.Errorf("target_concept required")
	}

	if req.Action == "" {
		return fmt.Errorf("action required")
	}

	if req.Strength < 0.0 || req.Strength > 1.0 {
		return fmt.Errorf("strength must be in range [0.0, 1.0]")
	}

	if req.Action == "redirect" && req.Direction == nil {
		return fmt.Errorf("redirect action requires direction quaternion")
	}

	return nil
}

// InterventionSuggestion is a recommended intervention
type InterventionSuggestion struct {
	TargetConcept uuid.UUID         `json:"target_concept"`
	Action        string            `json:"action"`
	Strength      float64           `json:"strength"`
	Direction     *vqc.Quaternion   `json:"direction,omitempty"`
	Reason        string            `json:"reason"`
	Priority      float64           `json:"priority"` // Higher = more important
}

// SuggestInterventions analyzes state and suggests interventions
func (ie *InterventionEngine) SuggestInterventions(ctx context.Context, sessionID string) ([]InterventionSuggestion, error) {
	stream, err := ie.observer.GetStream(sessionID)
	if err != nil {
		return nil, err
	}

	if stream.LastState == nil {
		return []InterventionSuggestion{}, nil
	}

	state := stream.LastState
	suggestions := make([]InterventionSuggestion, 0)

	// Suggest amplifying high-confidence concepts in EXPLORATION
	if state.CurrentRegime == RegimeExploration {
		for _, concept := range state.ActiveConcepts {
			if concept.Confidence > 0.8 {
				suggestions = append(suggestions, InterventionSuggestion{
					TargetConcept: concept.ID,
					Action:        "amplify",
					Strength:      0.2,
					Reason:        "High confidence in exploration phase - amplify to accelerate convergence",
					Priority:      concept.Confidence,
				})
			}
		}
	}

	// Suggest suppressing low-confidence outliers in OPTIMIZATION
	if state.CurrentRegime == RegimeOptimization {
		for _, concept := range state.ActiveConcepts {
			if concept.Confidence < 0.3 {
				suggestions = append(suggestions, InterventionSuggestion{
					TargetConcept: concept.ID,
					Action:        "suppress",
					Strength:      0.5,
					Reason:        "Low confidence in optimization phase - suppress noise",
					Priority:      1.0 - concept.Confidence,
				})
			}
		}
	}

	// Suggest redirecting concepts with low coherence
	if state.Coherence < 0.5 {
		// Find highest-confidence concept as target direction
		var highestConcept *QuaternionConcept
		highestConf := 0.0
		for _, concept := range state.ActiveConcepts {
			if concept.Confidence > highestConf {
				highestConf = concept.Confidence
				highestConcept = concept
			}
		}

		if highestConcept != nil {
			for _, concept := range state.ActiveConcepts {
				if concept.ID != highestConcept.ID && concept.Confidence < 0.6 {
					suggestions = append(suggestions, InterventionSuggestion{
						TargetConcept: concept.ID,
						Action:        "redirect",
						Strength:      0.3,
						Direction:     &highestConcept.Quaternion,
						Reason:        "Low coherence - redirect toward high-confidence concept",
						Priority:      highestConf - concept.Confidence,
					})
				}
			}
		}
	}

	// Sort by priority (descending)
	ie.sortSuggestionsByPriority(suggestions)

	// Return top 5
	if len(suggestions) > 5 {
		suggestions = suggestions[:5]
	}

	return suggestions, nil
}

// sortSuggestionsByPriority sorts in descending order
func (ie *InterventionEngine) sortSuggestionsByPriority(suggestions []InterventionSuggestion) {
	// Simple bubble sort (fine for small N)
	n := len(suggestions)
	for i := 0; i < n-1; i++ {
		for j := i + 1; j < n; j++ {
			if suggestions[j].Priority > suggestions[i].Priority {
				suggestions[i], suggestions[j] = suggestions[j], suggestions[i]
			}
		}
	}
}

// CalculateInterventionImpact measures effect of intervention
func (ie *InterventionEngine) CalculateInterventionImpact(beforeState, afterState *CognitiveState) map[string]interface{} {
	if beforeState == nil || afterState == nil {
		return map[string]interface{}{
			"error": "missing state data",
		}
	}

	confidenceDelta := afterState.Confidence - beforeState.Confidence
	coherenceDelta := afterState.Coherence - beforeState.Coherence
	entropyDelta := afterState.Entropy - beforeState.Entropy

	// Calculate magnitude of impact
	magnitude := math.Sqrt(
		confidenceDelta*confidenceDelta +
			coherenceDelta*coherenceDelta +
			entropyDelta*entropyDelta,
	)

	// Determine direction (positive = improving, negative = degrading)
	direction := "neutral"
	if confidenceDelta > 0.05 && coherenceDelta > 0.05 && entropyDelta < -0.05 {
		direction = "positive"
	} else if confidenceDelta < -0.05 || coherenceDelta < -0.05 || entropyDelta > 0.05 {
		direction = "negative"
	}

	return map[string]interface{}{
		"confidence_delta": confidenceDelta,
		"coherence_delta":  coherenceDelta,
		"entropy_delta":    entropyDelta,
		"magnitude":        magnitude,
		"direction":        direction,
		"effective":        magnitude > 0.1,
	}
}
