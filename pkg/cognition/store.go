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
// IN-MEMORY QUATERNION STORE
// ============================================================================
//
// Simplified in-memory store for Urban Lens cognition
// Full QuaternionStore integration can use existing storage layers
//
// ============================================================================

// QuaternionStore manages quaternion concepts in memory
type QuaternionStore struct {
	concepts map[uuid.UUID]*QuaternionConcept
	mu       sync.RWMutex
}

// NewQuaternionStore creates a new in-memory store
func NewQuaternionStore() *QuaternionStore {
	return &QuaternionStore{
		concepts: make(map[uuid.UUID]*QuaternionConcept),
	}
}

// Insert adds a new concept
func (qs *QuaternionStore) Insert(ctx context.Context, concept *QuaternionConcept) error {
	if concept.ID == uuid.Nil {
		concept.ID = uuid.New()
	}

	if concept.CreatedAt.IsZero() {
		concept.CreatedAt = time.Now()
	}

	qs.mu.Lock()
	defer qs.mu.Unlock()

	qs.concepts[concept.ID] = concept
	return nil
}

// Update modifies an existing concept
func (qs *QuaternionStore) Update(ctx context.Context, concept *QuaternionConcept) error {
	qs.mu.Lock()
	defer qs.mu.Unlock()

	if _, exists := qs.concepts[concept.ID]; !exists {
		return fmt.Errorf("concept not found: %s", concept.ID)
	}

	qs.concepts[concept.ID] = concept
	return nil
}

// GetByID retrieves a concept by ID
func (qs *QuaternionStore) GetByID(ctx context.Context, id uuid.UUID) (*QuaternionConcept, error) {
	qs.mu.RLock()
	defer qs.mu.RUnlock()

	concept, exists := qs.concepts[id]
	if !exists {
		return nil, fmt.Errorf("concept not found: %s", id)
	}

	return concept, nil
}

// FindByRegime returns concepts in a specific regime (limited)
func (qs *QuaternionStore) FindByRegime(ctx context.Context, regime Regime, limit int) ([]*QuaternionConcept, error) {
	qs.mu.RLock()
	defer qs.mu.RUnlock()

	results := make([]*QuaternionConcept, 0, limit)

	for _, concept := range qs.concepts {
		if concept.Regime == regime {
			results = append(results, concept)

			if len(results) >= limit {
				break
			}
		}
	}

	return results, nil
}

// FindSimilar finds concepts similar to query quaternion
func (qs *QuaternionStore) FindSimilar(ctx context.Context, query vqc.Quaternion, digitalRoot uint8, threshold float64, limit int) ([]*QuaternionConcept, error) {
	qs.mu.RLock()
	defer qs.mu.RUnlock()

	type scored struct {
		concept *QuaternionConcept
		score   float64
	}

	candidates := make([]scored, 0)

	for _, concept := range qs.concepts {
		// Optional digital root filtering
		if digitalRoot > 0 && concept.DigitalRoot != digitalRoot {
			continue
		}

		// Calculate quaternion similarity (dot product)
		similarity := query.W*concept.Quaternion.W +
			query.X*concept.Quaternion.X +
			query.Y*concept.Quaternion.Y +
			query.Z*concept.Quaternion.Z

		if math.Abs(similarity) >= threshold {
			candidates = append(candidates, scored{
				concept: concept,
				score:   math.Abs(similarity),
			})
		}
	}

	// Sort by score (simple bubble sort for small N)
	for i := 0; i < len(candidates)-1; i++ {
		for j := i + 1; j < len(candidates); j++ {
			if candidates[j].score > candidates[i].score {
				candidates[i], candidates[j] = candidates[j], candidates[i]
			}
		}
	}

	// Extract concepts up to limit
	results := make([]*QuaternionConcept, 0, limit)
	for i := 0; i < len(candidates) && i < limit; i++ {
		results = append(results, candidates[i].concept)
	}

	return results, nil
}

// SoftDelete marks a concept as deleted (in-memory: just delete)
func (qs *QuaternionStore) SoftDelete(ctx context.Context, id uuid.UUID) error {
	qs.mu.Lock()
	defer qs.mu.Unlock()

	delete(qs.concepts, id)
	return nil
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

// QuaternionFromText creates a quaternion from text (simplified encoding)
func QuaternionFromText(text string) vqc.Quaternion {
	if len(text) == 0 {
		return vqc.NewQuaternion(1, 0, 0, 0)
	}

	// Simple hash-based encoding
	var w, x, y, z float64
	for i, ch := range text {
		val := float64(ch)
		switch i % 4 {
		case 0:
			w += val
		case 1:
			x += val
		case 2:
			y += val
		case 3:
			z += val
		}
	}

	q := vqc.NewQuaternion(w, x, y, z)
	return q.Normalize()
}

// CalculateDigitalRoot computes digital root from UUID
func CalculateDigitalRoot(id uuid.UUID) uint8 {
	bytes := id[:]
	sum := uint64(0)
	for _, b := range bytes {
		sum += uint64(b)
	}

	// Reduce to digital root (0-9)
	for sum >= 10 {
		newSum := uint64(0)
		for sum > 0 {
			newSum += sum % 10
			sum /= 10
		}
		sum = newSum
	}

	return uint8(sum)
}

// CalculateDigitalRootFromQuaternion computes digital root from quaternion components
func CalculateDigitalRootFromQuaternion(q vqc.Quaternion) uint8 {
	// Sum the absolute values of components (scaled to integers)
	sum := uint64(math.Abs(q.W)*1000) +
		uint64(math.Abs(q.X)*1000) +
		uint64(math.Abs(q.Y)*1000) +
		uint64(math.Abs(q.Z)*1000)

	// Reduce to digital root
	for sum >= 10 {
		newSum := uint64(0)
		for sum > 0 {
			newSum += sum % 10
			sum /= 10
		}
		sum = newSum
	}

	return uint8(sum)
}

// HarmonicMean computes rigorous harmonic mean
func HarmonicMean(values []float64) float64 {
	if len(values) == 0 {
		return 0.0
	}

	sum := 0.0
	validCount := 0

	for _, v := range values {
		if v > 0 {
			sum += 1.0 / v
			validCount++
		}
	}

	if validCount == 0 {
		return 0.0
	}

	return float64(validCount) / sum
}
