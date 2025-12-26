package linguistics_test

import (
	"fmt"

	"github.com/asymmetrica/urbanlens/pkg/linguistics"
	"github.com/asymmetrica/urbanlens/pkg/vedic"
)

// ExampleEmbeddingBuilder demonstrates quaternion-based semantic encoding
func ExampleEmbeddingBuilder() {
	// Create a simple thesaurus with one word
	thesaurus := &linguistics.ThesaurusGraph{
		Entries: map[string]*linguistics.ThesaurusEntry{
			"happy": {
				Word: "happy",
				Synonyms: []string{"joyful", "glad", "cheerful", "pleased"},
				Antonyms: []string{"sad", "unhappy", "miserable"},
				Weight: 1.0,
			},
		},
		TotalWords: 1,
		TotalRelations: 7,
	}

	// Build embedding
	builder := linguistics.NewEmbeddingBuilder(thesaurus)
	q := builder.BuildEmbedding("happy")

	fmt.Printf("Quaternion encoding of 'happy':\n")
	fmt.Printf("  Core (W): %.3f\n", q.W)
	fmt.Printf("  Temporal (X): %.3f\n", q.X)
	fmt.Printf("  Valence (Y): %.3f (positive!)\n", q.Y)
	fmt.Printf("  Abstraction (Z): %.3f\n", q.Z)

	// Semantic dimensions
	dims := builder.GetSemanticDimensions("happy")
	fmt.Printf("\nSemantic interpretation:\n")
	if dims["valence"] > 0.5 {
		fmt.Printf("  Emotion: Positive\n")
	}
	if dims["abstraction"] < 0.5 {
		fmt.Printf("  Type: Concrete emotion\n")
	}
}

// ExampleThesaurusQuaternionIndex demonstrates digital root clustering
func ExampleThesaurusQuaternionIndex() {
	// Create index
	index := linguistics.NewThesaurusQuaternionIndex()

	// Add words
	words := []string{"happy", "joyful", "sad", "angry"}
	for _, word := range words {
		q := vedic.EncodeAsQuaternion(word)
		index.AddWord(word, q)
	}

	fmt.Printf("Quaternion Index:\n")
	fmt.Printf("  Total words: %d\n", index.TotalWords())
	fmt.Printf("  Total clusters: %d\n", index.TotalClusters())

	// Show cluster distribution
	stats := index.ClusterStats()
	fmt.Printf("\nCluster distribution (digital root):\n")
	for dr := uint8(0); dr <= 9; dr++ {
		if count, exists := stats[dr]; exists && count > 0 {
			fmt.Printf("  Cluster %d: %d words\n", dr, count)
		}
	}

	// Find nearest words to "happiness"
	qHappiness := vedic.EncodeAsQuaternion("happiness")
	nearest := index.FindNearest(qHappiness, 3)

	fmt.Printf("\nWords semantically close to 'happiness':\n")
	for i, emb := range nearest {
		fmt.Printf("  %d. %s (distance: %.3f)\n",
			i+1, emb.Word,
			vedic.QuaternionDistance(qHappiness, emb.Quaternion))
	}
}

// ExampleApplyCompositional demonstrates linguistic transformations
func ExampleApplyCompositional() {
	// Build sample thesaurus
	thesaurus := &linguistics.ThesaurusGraph{
		Entries: map[string]*linguistics.ThesaurusEntry{
			"good": {
				Word: "good",
				Synonyms: []string{"great", "excellent", "fine"},
				Antonyms: []string{"bad", "poor", "terrible"},
			},
			"bad": {
				Word: "bad",
				Synonyms: []string{"poor", "terrible", "awful"},
				Antonyms: []string{"good", "great", "excellent"},
			},
			"hot": {
				Word: "hot",
				Antonyms: []string{"cold"},
			},
			"cold": {
				Word: "cold",
				Antonyms: []string{"hot"},
			},
			"day": {
				Word: "day",
				Antonyms: []string{"night"},
			},
		},
	}

	// Find synonyms
	synonyms := thesaurus.FindSynonyms("good")
	fmt.Printf("Synonyms of 'good': %v\n", synonyms)

	// Apply compositional operator: antonym(good) then synonym
	operators := []linguistics.LanguageOperator{
		linguistics.ANTONYM,
		linguistics.SYNONYM,
	}
	result := linguistics.ApplyCompositional("good", operators, thesaurus)
	fmt.Printf("Synonyms of antonyms of 'good': %v\n", result)

	// Analogy: hot:cold :: day:?
	analogy := linguistics.FindAnalogy("hot", "cold", "day", thesaurus)
	fmt.Printf("Analogy hot:cold :: day:? → %v\n", analogy)
}

// ExampleGetSemanticDistance demonstrates graph-based semantic similarity
func ExampleGetSemanticDistance() {
	// Build connected thesaurus
	thesaurus := &linguistics.ThesaurusGraph{
		Entries: map[string]*linguistics.ThesaurusEntry{
			"happy": {
				Word: "happy",
				Synonyms: []string{"joyful"},
			},
			"joyful": {
				Word: "joyful",
				Synonyms: []string{"happy", "glad"},
			},
			"glad": {
				Word: "glad",
				Synonyms: []string{"joyful", "pleased"},
			},
			"pleased": {
				Word: "pleased",
				Synonyms: []string{"glad"},
			},
		},
	}

	// Measure semantic distance (graph hops)
	distance := linguistics.GetSemanticDistance("happy", "pleased", thesaurus)
	fmt.Printf("Semantic distance from 'happy' to 'pleased': %d hops\n", distance)

	// Direct neighbors
	distance = linguistics.GetSemanticDistance("happy", "joyful", thesaurus)
	fmt.Printf("Semantic distance from 'happy' to 'joyful': %d hop\n", distance)
}
