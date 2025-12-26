package linguistics

import (
	"hash/fnv"
	"math"
	"sort"

	"github.com/asymmetrica/urbanlens/pkg/vedic"
)

// WordEmbedding represents a word in 4D quaternion space
type WordEmbedding struct {
	Word       string         `json:"word"`
	Quaternion vedic.Quaternion `json:"quaternion"`

	// Semantic dimensions (interpreted from quaternion)
	Core        float64 `json:"core"`        // W: Semantic intensity
	Temporal    float64 `json:"temporal"`    // X: Past/present/future
	Valence     float64 `json:"valence"`     // Y: Emotional charge
	Abstraction float64 `json:"abstraction"` // Z: Concrete/abstract

	DigitalRoot uint8 `json:"digital_root"` // O(1) cluster
	Frequency   int   `json:"frequency"`    // Corpus frequency
}

// EnhancedThesaurusEntry extends existing entry with quaternion
type EnhancedThesaurusEntry struct {
	Word      string       `json:"word"`
	Embedding WordEmbedding `json:"embedding"`

	// Existing relationships
	Synonyms  []string `json:"synonyms"`
	Antonyms  []string `json:"antonyms"`
	Hyponyms  []string `json:"hyponyms"`  // More specific
	Hypernyms []string `json:"hypernyms"` // More general
	Meronyms  []string `json:"meronyms"`  // Part-of
	Holonyms  []string `json:"holonyms"`  // Whole-of
	Related   []string `json:"related"`

	// Enhanced with quaternion neighbors
	SemanticNeighbors []string `json:"semantic_neighbors"` // Close in 4D space
}

// ThesaurusQuaternionIndex provides fast quaternion-based lookup
type ThesaurusQuaternionIndex struct {
	// Cluster by digital root (0-9) for O(1) lookup
	clusters map[uint8][]*WordEmbedding

	// Word to embedding map
	wordMap map[string]*WordEmbedding

	// Total words indexed
	totalWords int
}

// NewThesaurusQuaternionIndex creates a new index
func NewThesaurusQuaternionIndex() *ThesaurusQuaternionIndex {
	return &ThesaurusQuaternionIndex{
		clusters: make(map[uint8][]*WordEmbedding),
		wordMap:  make(map[string]*WordEmbedding),
	}
}

// AddWord adds a word with its quaternion embedding
func (tqi *ThesaurusQuaternionIndex) AddWord(word string, q vedic.Quaternion) {
	// Extract semantic dimensions from quaternion
	embedding := &WordEmbedding{
		Word:        word,
		Quaternion:  q,
		Core:        q.W,
		Temporal:    q.X,
		Valence:     q.Y,
		Abstraction: q.Z,
		DigitalRoot: vedic.DigitalRootString(word),
	}

	// Add to cluster
	tqi.clusters[embedding.DigitalRoot] = append(
		tqi.clusters[embedding.DigitalRoot],
		embedding,
	)

	// Add to word map
	tqi.wordMap[word] = embedding
	tqi.totalWords++
}

// FindNearest finds words nearest to a quaternion (reverse conversion!)
func (tqi *ThesaurusQuaternionIndex) FindNearest(
	q vedic.Quaternion,
	limit int,
) []*WordEmbedding {
	// Calculate digital root for primary cluster lookup
	dr := vedic.DigitalRoot(int64(hashQuaternion(q)))

	// Get candidates from primary cluster and adjacent clusters
	var candidates []*WordEmbedding

	// Add primary cluster
	candidates = append(candidates, tqi.clusters[uint8(dr)]...)

	// Add adjacent clusters (dr-1, dr+1) for better coverage
	drMinus := uint8(dr - 1)
	if dr == 0 {
		drMinus = 9
	}
	drPlus := uint8((dr + 1) % 10)

	candidates = append(candidates, tqi.clusters[drMinus]...)
	candidates = append(candidates, tqi.clusters[drPlus]...)

	// If still empty or very few, search all clusters
	if len(candidates) < limit*2 {
		for _, clusterCandidates := range tqi.clusters {
			candidates = append(candidates, clusterCandidates...)
		}
	}

	// Calculate distances and sort
	type distanceResult struct {
		embedding *WordEmbedding
		distance  float64
	}

	results := make([]distanceResult, 0, len(candidates))
	for _, candidate := range candidates {
		distance := vedic.QuaternionDistance(q, candidate.Quaternion)

		results = append(results, distanceResult{
			embedding: candidate,
			distance:  distance,
		})
	}

	// Sort by distance (ascending)
	sort.Slice(results, func(i, j int) bool {
		return results[i].distance < results[j].distance
	})

	// Return top N
	nearest := make([]*WordEmbedding, 0, limit)
	for i := 0; i < limit && i < len(results); i++ {
		nearest = append(nearest, results[i].embedding)
	}

	return nearest
}

// FindSimilarWords finds words similar to a given word
func (tqi *ThesaurusQuaternionIndex) FindSimilarWords(
	word string,
	limit int,
) []*WordEmbedding {
	embedding, exists := tqi.wordMap[word]
	if !exists {
		return nil
	}

	return tqi.FindNearest(embedding.Quaternion, limit)
}

// GetEmbedding retrieves the embedding for a word
func (tqi *ThesaurusQuaternionIndex) GetEmbedding(word string) (*WordEmbedding, bool) {
	embedding, exists := tqi.wordMap[word]
	return embedding, exists
}

// TotalWords returns the total number of words indexed
func (tqi *ThesaurusQuaternionIndex) TotalWords() int {
	return tqi.totalWords
}

// TotalClusters returns the number of clusters
func (tqi *ThesaurusQuaternionIndex) TotalClusters() int {
	return len(tqi.clusters)
}

// ClusterStats returns statistics about cluster distribution
func (tqi *ThesaurusQuaternionIndex) ClusterStats() map[uint8]int {
	stats := make(map[uint8]int)
	for dr, cluster := range tqi.clusters {
		stats[dr] = len(cluster)
	}
	return stats
}

// Helper: Hash string to uint64 for digital root
func hashString(s string) uint64 {
	h := fnv.New64a()
	h.Write([]byte(s))
	return h.Sum64()
}

// Helper: Hash quaternion to uint64
func hashQuaternion(q vedic.Quaternion) uint64 {
	// Convert float components to fixed-point integers
	w := uint64(math.Abs(q.W) * 10000)
	x := uint64(math.Abs(q.X) * 10000)
	y := uint64(math.Abs(q.Y) * 10000)
	z := uint64(math.Abs(q.Z) * 10000)

	// Combine using prime numbers to reduce collisions
	return w + x*13 + y*17 + z*19
}
