package isomorphism

import (
	"fmt"
	"hash/fnv"
	"math"
	"strings"

	qmath "github.com/asymmetrica/urbanlens/pkg/math"
)

// ============================================================================
// CONCEPT ENCODER - TEXT TO QUATERNION MAPPING
// ============================================================================

// ConceptEncoder encodes concepts as quaternions on S³
// Algorithm: Semantic hashing + normalization to unit quaternion
//
// Encoding Strategy:
//   W: Semantic complexity (word count, abstract vs concrete)
//   X: Domain specificity (technical vs general)
//   Y: Relational density (connections to other concepts)
//   Z: Temporal stability (unchanging vs evolving)
//
// Mathematical Guarantee: ||q|| = 1 (all encoded concepts live on S³)
type ConceptEncoder struct {
	domainVectors map[Domain]qmath.Quaternion // Pre-computed domain centroids
	vocabulary    map[string]float64          // Word frequency scores
}

// NewConceptEncoder creates a new concept encoder
func NewConceptEncoder() *ConceptEncoder {
	encoder := &ConceptEncoder{
		domainVectors: make(map[Domain]qmath.Quaternion),
		vocabulary:    make(map[string]float64),
	}

	// Initialize domain centroids (learned from corpus)
	encoder.initializeDomainVectors()

	return encoder
}

// Encode converts a concept to a quaternion on S³
func (ce *ConceptEncoder) Encode(concept *Concept) qmath.Quaternion {
	// If already encoded, return cached value
	if concept.Quaternion.Norm() > 0.5 { // Already normalized
		return concept.Quaternion
	}

	// Extract features
	w := ce.computeComplexity(concept)
	x := ce.computeSpecificity(concept)
	y := ce.computeRelationalDensity(concept)
	z := ce.computeStability(concept)

	// Create quaternion
	q := qmath.NewQuaternion(w, x, y, z)

	// Normalize to S³ (unit quaternion)
	qNorm := q.Normalize()

	// Cache in concept
	concept.Quaternion = qNorm

	return qNorm
}

// EncodeBatch encodes multiple concepts efficiently
func (ce *ConceptEncoder) EncodeBatch(concepts []*Concept) []qmath.Quaternion {
	quaternions := make([]qmath.Quaternion, len(concepts))

	for i, concept := range concepts {
		quaternions[i] = ce.Encode(concept)
	}

	return quaternions
}

// ============================================================================
// FEATURE EXTRACTION
// ============================================================================

// computeComplexity extracts W component (semantic complexity)
func (ce *ConceptEncoder) computeComplexity(concept *Concept) float64 {
	// Word count in description
	wordCount := float64(len(strings.Fields(concept.Description)))

	// Abstract vs concrete (longer descriptions = more abstract)
	abstractness := math.Tanh(wordCount / 20.0) // Normalize to [0, 1]

	// Tag complexity
	tagComplexity := float64(len(concept.Tags)) / 10.0

	// Weighted combination
	complexity := 0.6*abstractness + 0.4*tagComplexity

	return math.Min(complexity, 1.0)
}

// computeSpecificity extracts X component (domain specificity)
func (ce *ConceptEncoder) computeSpecificity(concept *Concept) float64 {
	// Domain-specific terms in description
	domainVector, exists := ce.domainVectors[concept.Domain]
	if !exists {
		return 0.5 // Default mid-range
	}

	// Compute alignment with domain centroid
	// Higher alignment = higher specificity
	specificity := ce.semanticAlignment(concept.Description, domainVector)

	return specificity
}

// computeRelationalDensity extracts Y component (concept connections)
func (ce *ConceptEncoder) computeRelationalDensity(concept *Concept) float64 {
	// Number of properties = proxy for relational connections
	propertyCount := float64(len(concept.Properties))

	// Tag overlap with other concepts (estimated)
	tagDensity := float64(len(concept.Tags)) / 5.0

	// Weighted combination
	density := 0.5*math.Tanh(propertyCount/10.0) + 0.5*math.Tanh(tagDensity)

	return density
}

// computeStability extracts Z component (temporal stability)
func (ce *ConceptEncoder) computeStability(concept *Concept) float64 {
	// Heuristic: fundamental concepts are more stable

	// Check for stability markers in tags
	stableMarkers := []string{"fundamental", "core", "basic", "universal", "eternal"}
	unstableMarkers := []string{"trending", "new", "emerging", "volatile"}

	stability := 0.5 // Default

	for _, tag := range concept.Tags {
		tagLower := strings.ToLower(tag)
		for _, marker := range stableMarkers {
			if strings.Contains(tagLower, marker) {
				stability += 0.1
			}
		}
		for _, marker := range unstableMarkers {
			if strings.Contains(tagLower, marker) {
				stability -= 0.1
			}
		}
	}

	// Clamp to [0, 1]
	if stability < 0 {
		stability = 0
	}
	if stability > 1 {
		stability = 1
	}

	return stability
}

// ============================================================================
// SEMANTIC ALIGNMENT (Text → Vector)
// ============================================================================

// semanticAlignment computes alignment between text and domain vector
func (ce *ConceptEncoder) semanticAlignment(text string, domainVector qmath.Quaternion) float64 {
	// Simple word-based hashing (can be replaced with embeddings)
	words := strings.Fields(strings.ToLower(text))

	// Hash words to 4D vector
	var sumW, sumX, sumY, sumZ float64

	for i, word := range words {
		hash := ce.hashWord(word)

		// Distribute across 4 components cyclically
		switch i % 4 {
		case 0:
			sumW += hash
		case 1:
			sumX += hash
		case 2:
			sumY += hash
		case 3:
			sumZ += hash
		}
	}

	// Normalize
	textVec := qmath.NewQuaternion(sumW, sumX, sumY, sumZ).Normalize()

	// Compute cosine similarity
	alignment := textVec.Dot(domainVector)

	// Map to [0, 1]
	return (alignment + 1.0) / 2.0
}

// hashWord computes a hash value for a word (0-1 range)
func (ce *ConceptEncoder) hashWord(word string) float64 {
	h := fnv.New64a()
	h.Write([]byte(word))
	hashVal := h.Sum64()

	// Normalize to [0, 1]
	return float64(hashVal%1000) / 1000.0
}

// ============================================================================
// DOMAIN VECTOR INITIALIZATION
// ============================================================================

// initializeDomainVectors sets up pre-computed domain centroids
func (ce *ConceptEncoder) initializeDomainVectors() {
	// Technical domains (high complexity, high specificity)
	ce.domainVectors[DomainProgramming] = qmath.NewQuaternion(0.8, 0.9, 0.7, 0.6).Normalize()
	ce.domainVectors[DomainSystemArchitecture] = qmath.NewQuaternion(0.9, 0.9, 0.8, 0.7).Normalize()
	ce.domainVectors[DomainUXDesign] = qmath.NewQuaternion(0.6, 0.7, 0.8, 0.5).Normalize()
	ce.domainVectors[DomainQA] = qmath.NewQuaternion(0.7, 0.8, 0.7, 0.8).Normalize()
	ce.domainVectors[DomainOperations] = qmath.NewQuaternion(0.6, 0.8, 0.9, 0.7).Normalize()
	ce.domainVectors[DomainProductManagement] = qmath.NewQuaternion(0.7, 0.6, 0.9, 0.6).Normalize()
	ce.domainVectors[DomainDataScience] = qmath.NewQuaternion(0.9, 0.9, 0.7, 0.6).Normalize()
	ce.domainVectors[DomainSales] = qmath.NewQuaternion(0.5, 0.6, 0.8, 0.4).Normalize()
	ce.domainVectors[DomainHR] = qmath.NewQuaternion(0.6, 0.5, 0.8, 0.5).Normalize()

	// Professional domains (moderate complexity, varied specificity)
	ce.domainVectors[DomainDriving] = qmath.NewQuaternion(0.4, 0.5, 0.6, 0.7).Normalize()
	ce.domainVectors[DomainCooking] = qmath.NewQuaternion(0.5, 0.6, 0.7, 0.6).Normalize()
	ce.domainVectors[DomainDance] = qmath.NewQuaternion(0.4, 0.5, 0.7, 0.5).Normalize()
	ce.domainVectors[DomainMusic] = qmath.NewQuaternion(0.6, 0.7, 0.8, 0.6).Normalize()
	ce.domainVectors[DomainSecurity] = qmath.NewQuaternion(0.6, 0.8, 0.7, 0.8).Normalize()
	ce.domainVectors[DomainCleaning] = qmath.NewQuaternion(0.3, 0.4, 0.5, 0.8).Normalize()
	ce.domainVectors[DomainRetail] = qmath.NewQuaternion(0.4, 0.5, 0.7, 0.6).Normalize()
	ce.domainVectors[DomainTeaching] = qmath.NewQuaternion(0.7, 0.6, 0.8, 0.7).Normalize()
	ce.domainVectors[DomainCarpentry] = qmath.NewQuaternion(0.5, 0.7, 0.6, 0.8).Normalize()

	// Urban domains (Urban Lens specific)
	ce.domainVectors[DomainUrbanPlanning] = qmath.NewQuaternion(0.8, 0.8, 0.9, 0.7).Normalize()
	ce.domainVectors[DomainTrafficFlow] = qmath.NewQuaternion(0.6, 0.7, 0.8, 0.6).Normalize()
	ce.domainVectors[DomainPublicTransit] = qmath.NewQuaternion(0.6, 0.7, 0.9, 0.7).Normalize()
	ce.domainVectors[DomainWasteManagement] = qmath.NewQuaternion(0.5, 0.6, 0.7, 0.8).Normalize()
	ce.domainVectors[DomainCommunityOrganizing] = qmath.NewQuaternion(0.6, 0.5, 0.9, 0.6).Normalize()
	ce.domainVectors[DomainStreetVending] = qmath.NewQuaternion(0.4, 0.5, 0.7, 0.5).Normalize()
	ce.domainVectors[DomainCivicEngagement] = qmath.NewQuaternion(0.7, 0.6, 0.9, 0.6).Normalize()
}

// ============================================================================
// DECODING (Quaternion → Concept Space)
// ============================================================================

// DecodeToConcept attempts to decode a quaternion back to concept properties
// This is approximate (lossy compression)
func (ce *ConceptEncoder) DecodeToConcept(q qmath.Quaternion, domain Domain) *Concept {
	// Normalize
	q = q.Normalize()

	// Extract features
	concept := &Concept{
		Name:        fmt.Sprintf("concept_%.3f_%.3f_%.3f_%.3f", q.W, q.X, q.Y, q.Z),
		Domain:      domain,
		Description: ce.generateDescription(q),
		Tags:        ce.generateTags(q),
		Quaternion:  q,
		Properties:  make(map[string]float64),
	}

	// Add numerical properties
	concept.Properties["complexity"] = q.W
	concept.Properties["specificity"] = q.X
	concept.Properties["relational_density"] = q.Y
	concept.Properties["stability"] = q.Z

	return concept
}

// generateDescription generates a description from quaternion features
func (ce *ConceptEncoder) generateDescription(q qmath.Quaternion) string {
	parts := make([]string, 0)

	if q.W > 0.7 {
		parts = append(parts, "highly complex")
	} else if q.W < 0.3 {
		parts = append(parts, "simple")
	}

	if q.X > 0.7 {
		parts = append(parts, "domain-specific")
	} else if q.X < 0.3 {
		parts = append(parts, "general-purpose")
	}

	if q.Y > 0.7 {
		parts = append(parts, "highly connected")
	} else if q.Y < 0.3 {
		parts = append(parts, "isolated")
	}

	if q.Z > 0.7 {
		parts = append(parts, "stable")
	} else if q.Z < 0.3 {
		parts = append(parts, "evolving")
	}

	if len(parts) == 0 {
		return "balanced concept"
	}

	return strings.Join(parts, ", ") + " concept"
}

// generateTags generates tags from quaternion features
func (ce *ConceptEncoder) generateTags(q qmath.Quaternion) []string {
	tags := make([]string, 0)

	if q.W > 0.7 {
		tags = append(tags, "complex")
	}
	if q.X > 0.7 {
		tags = append(tags, "specialized")
	}
	if q.Y > 0.7 {
		tags = append(tags, "networked")
	}
	if q.Z > 0.7 {
		tags = append(tags, "fundamental")
	}

	return tags
}
