package linguistics

import (
	"math"
	"strings"

	"github.com/asymmetrica/urbanlens/pkg/vedic"
)

// EmbeddingBuilder creates quaternion embeddings for words
type EmbeddingBuilder struct {
	thesaurus *ThesaurusGraph
}

// NewEmbeddingBuilder creates a new builder
func NewEmbeddingBuilder(thesaurus *ThesaurusGraph) *EmbeddingBuilder {
	return &EmbeddingBuilder{thesaurus: thesaurus}
}

// BuildEmbedding creates a quaternion embedding for a word
func (eb *EmbeddingBuilder) BuildEmbedding(word string) vedic.Quaternion {
	entry := eb.thesaurus.GetEntry(word)
	if entry == nil {
		// Fallback: hash-based quaternion
		return eb.fallbackEmbedding(word)
	}

	// Build quaternion from semantic features
	w := eb.calculateCore(entry)
	x := eb.calculateTemporal(entry)
	y := eb.calculateValence(entry)
	z := eb.calculateAbstraction(entry)

	// Create and normalize quaternion
	return vedic.NewQuaternion(w, x, y, z)
}

// Calculate w: Core semantic intensity
func (eb *EmbeddingBuilder) calculateCore(entry *ThesaurusEntry) float64 {
	// Based on relationship density
	totalRelations := len(entry.Synonyms) + len(entry.Antonyms) +
		len(entry.Related) + len(entry.Hyponyms) + len(entry.Hypernyms) +
		len(entry.Meronyms) + len(entry.Holonyms)

	// Normalize to 0-1 (max 50 relations = 1.0)
	core := math.Min(float64(totalRelations)/50.0, 1.0)

	// Boost by weight if available
	if entry.Weight > 0 {
		core = (core + entry.Weight) / 2.0
	}

	return core
}

// Calculate x: Temporal dimension (past/present/future)
func (eb *EmbeddingBuilder) calculateTemporal(entry *ThesaurusEntry) float64 {
	word := entry.Word

	// Time-related markers
	pastMarkers := []string{"was", "were", "had", "did", "past", "former", "old", "ancient"}
	futureMarkers := []string{"will", "shall", "future", "next", "coming", "tomorrow"}

	// Check word itself
	for _, marker := range pastMarkers {
		if strings.Contains(word, marker) {
			return -0.5
		}
	}
	for _, marker := range futureMarkers {
		if strings.Contains(word, marker) {
			return 0.5
		}
	}

	// Check verb tenses via endings
	if len(word) > 2 {
		ending := word[len(word)-2:]
		switch ending {
		case "ed": // Past tense
			return -0.5
		case "ng": // Present continuous
			return 0.1
		}

		// Check last 3 characters
		if len(word) > 3 {
			ending3 := word[len(word)-3:]
			if ending3 == "ing" {
				return 0.1 // Progressive
			}
		}
	}

	// Check synonyms for temporal hints
	pastCount := 0
	futureCount := 0

	for _, syn := range entry.Synonyms {
		for _, marker := range pastMarkers {
			if syn == marker {
				pastCount++
			}
		}
		for _, marker := range futureMarkers {
			if syn == marker {
				futureCount++
			}
		}
	}

	if pastCount > futureCount {
		return -0.3
	} else if futureCount > pastCount {
		return 0.3
	}

	return 0.0 // Timeless/present
}

// Calculate y: Emotional valence (positive/negative)
func (eb *EmbeddingBuilder) calculateValence(entry *ThesaurusEntry) float64 {
	// Use antonym analysis - more antonyms = more polarized
	antonymCount := len(entry.Antonyms)

	// Positive emotional markers
	positiveMarkers := []string{
		"good", "great", "happy", "joy", "love", "success", "win",
		"excellent", "wonderful", "beautiful", "pleasant", "delightful",
		"glad", "cheerful", "content", "satisfied", "proud",
	}

	// Negative emotional markers
	negativeMarkers := []string{
		"bad", "sad", "hate", "fail", "pain", "loss", "fear",
		"terrible", "awful", "ugly", "unpleasant", "dreadful",
		"angry", "depressed", "miserable", "ashamed", "guilty",
	}

	// Neutral markers (reduce valence)
	neutralMarkers := []string{
		"neutral", "average", "ordinary", "normal", "typical",
		"standard", "regular", "common", "usual",
	}

	positiveScore := 0
	negativeScore := 0
	neutralScore := 0

	// Check word itself
	for _, marker := range positiveMarkers {
		if entry.Word == marker || strings.Contains(entry.Word, marker) {
			positiveScore += 2
		}
	}
	for _, marker := range negativeMarkers {
		if entry.Word == marker || strings.Contains(entry.Word, marker) {
			negativeScore += 2
		}
	}
	for _, marker := range neutralMarkers {
		if entry.Word == marker {
			neutralScore += 2
		}
	}

	// Check synonyms
	for _, syn := range entry.Synonyms {
		for _, marker := range positiveMarkers {
			if syn == marker {
				positiveScore++
			}
		}
		for _, marker := range negativeMarkers {
			if syn == marker {
				negativeScore++
			}
		}
		for _, marker := range neutralMarkers {
			if syn == marker {
				neutralScore++
			}
		}
	}

	// Check antonyms (opposite valence)
	for _, ant := range entry.Antonyms {
		for _, marker := range positiveMarkers {
			if ant == marker {
				negativeScore++ // Antonym of positive = negative
			}
		}
		for _, marker := range negativeMarkers {
			if ant == marker {
				positiveScore++ // Antonym of negative = positive
			}
		}
	}

	// Calculate valence
	if neutralScore > 2 {
		return 0.0 // Explicitly neutral
	}

	totalScore := positiveScore + negativeScore
	if totalScore == 0 {
		return 0.0 // No emotional content
	}

	// Normalize to [-1, 1]
	valence := float64(positiveScore-negativeScore) / float64(totalScore)

	// Scale by antonym count (more antonyms = more polarized)
	polarization := math.Min(float64(antonymCount)/10.0, 1.0)
	valence *= (0.5 + 0.5*polarization)

	return valence
}

// Calculate z: Abstraction level (concrete vs abstract)
func (eb *EmbeddingBuilder) calculateAbstraction(entry *ThesaurusEntry) float64 {
	// Concrete words: have meronyms (parts) and holonyms (wholes)
	// Abstract words: have many hypernyms (generalizations)

	meronymCount := len(entry.Meronyms)
	holonymCount := len(entry.Holonyms)
	hypernymCount := len(entry.Hypernyms)
	hyponymCount := len(entry.Hyponyms)

	concreteScore := meronymCount + holonymCount
	abstractScore := hypernymCount

	// Abstract concept markers
	abstractMarkers := []string{
		"concept", "idea", "theory", "principle", "notion",
		"thought", "belief", "philosophy", "ism", "ity", "ness",
		"quality", "property", "state", "condition", "situation",
	}

	// Concrete object markers
	concreteMarkers := []string{
		"object", "thing", "item", "tool", "device", "machine",
		"animal", "plant", "person", "place", "building",
	}

	// Check word endings for abstract concepts
	word := entry.Word
	if len(word) > 3 {
		ending := word[len(word)-3:]
		switch ending {
		case "ism", "ity", "ion", "ess": // Abstract suffixes
			abstractScore += 2
		}
	}

	// Check word against markers
	for _, marker := range abstractMarkers {
		if strings.Contains(word, marker) {
			abstractScore += 2
		}
	}
	for _, marker := range concreteMarkers {
		if strings.Contains(word, marker) {
			concreteScore += 2
		}
	}

	// Concrete: has specific instances (hyponyms)
	// Abstract: is a generalization of many things
	if hyponymCount > 5 {
		abstractScore += 2 // Many specific examples = abstract category
	}

	// Calculate abstraction level
	totalScore := concreteScore + abstractScore
	if totalScore == 0 {
		return 0.5 // Neutral
	}

	// Normalize to [0, 1]
	abstraction := float64(abstractScore) / float64(totalScore)

	return abstraction
}

// Fallback: Create embedding from word hash when no thesaurus entry exists
func (eb *EmbeddingBuilder) fallbackEmbedding(word string) vedic.Quaternion {
	// Use existing Vedic encoding (consistent hash-based)
	return vedic.EncodeAsQuaternion(word)
}

// BuildBatch creates embeddings for multiple words efficiently
func (eb *EmbeddingBuilder) BuildBatch(words []string) map[string]vedic.Quaternion {
	embeddings := make(map[string]vedic.Quaternion, len(words))

	for _, word := range words {
		embeddings[word] = eb.BuildEmbedding(word)
	}

	return embeddings
}

// CalculateSemanticDistance computes semantic distance between two words
func (eb *EmbeddingBuilder) CalculateSemanticDistance(word1, word2 string) float64 {
	q1 := eb.BuildEmbedding(word1)
	q2 := eb.BuildEmbedding(word2)

	return vedic.QuaternionDistance(q1, q2)
}

// CalculateSemanticSimilarity computes semantic similarity between two words
func (eb *EmbeddingBuilder) CalculateSemanticSimilarity(word1, word2 string) float64 {
	q1 := eb.BuildEmbedding(word1)
	q2 := eb.BuildEmbedding(word2)

	// Dot product for normalized quaternions gives cosine similarity
	similarity := math.Abs(q1.Dot(q2))

	// Clamp to [0, 1]
	if similarity > 1.0 {
		similarity = 1.0
	}
	if similarity < 0.0 {
		similarity = 0.0
	}

	return similarity
}

// GetSemanticDimensions extracts interpretable dimensions from a word
func (eb *EmbeddingBuilder) GetSemanticDimensions(word string) map[string]float64 {
	q := eb.BuildEmbedding(word)

	return map[string]float64{
		"core":        q.W, // Semantic intensity
		"temporal":    q.X, // Past/present/future
		"valence":     q.Y, // Positive/negative
		"abstraction": q.Z, // Concrete/abstract
	}
}
