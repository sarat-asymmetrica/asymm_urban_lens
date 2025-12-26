package linguistics

import (
	"context"
	"fmt"
	"log"
	"time"
)

// InitializeQuaternionThesaurus builds quaternion embeddings for all words
func InitializeQuaternionThesaurus(
	thesaurus *ThesaurusGraph,
) (*ThesaurusQuaternionIndex, error) {
	startTime := time.Now()
	log.Println("🧠 Building quaternion embeddings for thesaurus...")

	index := NewThesaurusQuaternionIndex()
	builder := NewEmbeddingBuilder(thesaurus)

	// Build embedding for each word
	count := 0
	for word := range thesaurus.Entries {
		embedding := builder.BuildEmbedding(word)
		index.AddWord(word, embedding)
		count++

		if count%1000 == 0 {
			log.Printf("  📊 Processed %d words...", count)
		}
	}

	elapsed := time.Since(startTime)

	log.Printf("✅ Quaternion index built: %d words, %d clusters in %v",
		index.totalWords, len(index.clusters), elapsed)

	// Log cluster distribution
	stats := index.ClusterStats()
	log.Println("📈 Cluster distribution:")
	for dr := uint8(0); dr <= 9; dr++ {
		if count, exists := stats[dr]; exists {
			log.Printf("   Digital Root %d: %d words", dr, count)
		}
	}

	return index, nil
}

// Global instances (initialized at startup)
var (
	GlobalThesaurusGraph   *ThesaurusGraph
	GlobalThesaurusIndex   *ThesaurusQuaternionIndex
	GlobalEmbeddingBuilder *EmbeddingBuilder
)

// Initialize initializes the complete linguistic system
// Must be called at server startup
func Initialize(ctx context.Context, oxfordPath, rogetPath string) error {
	startTime := time.Now()
	log.Println("🚀 Initializing Urban Lens linguistic system...")

	// Build thesaurus graph from language packs
	var err error
	GlobalThesaurusGraph, err = BuildThesaurusGraph(oxfordPath, rogetPath)
	if err != nil {
		return fmt.Errorf("failed to build thesaurus graph: %w", err)
	}

	// Build quaternion index
	GlobalThesaurusIndex, err = InitializeQuaternionThesaurus(GlobalThesaurusGraph)
	if err != nil {
		return fmt.Errorf("failed to build quaternion index: %w", err)
	}

	// Create embedding builder
	GlobalEmbeddingBuilder = NewEmbeddingBuilder(GlobalThesaurusGraph)

	elapsed := time.Since(startTime)

	log.Printf("✅ Linguistic system initialized in %v", elapsed)
	log.Printf("   📚 Thesaurus: %d words, %d relationships",
		GlobalThesaurusGraph.TotalWords,
		GlobalThesaurusGraph.TotalRelations)
	log.Printf("   🧮 Quaternion index: %d embeddings, %d clusters",
		GlobalThesaurusIndex.TotalWords(),
		GlobalThesaurusIndex.TotalClusters())

	return nil
}

// InitializeFromCache loads pre-built thesaurus from cache file
func InitializeFromCache(ctx context.Context, cachePath string) error {
	startTime := time.Now()
	log.Printf("📂 Loading thesaurus from cache: %s", cachePath)

	var err error
	GlobalThesaurusGraph, err = LoadThesaurusFromFile(cachePath)
	if err != nil {
		return fmt.Errorf("failed to load thesaurus cache: %w", err)
	}

	// Build quaternion index
	GlobalThesaurusIndex, err = InitializeQuaternionThesaurus(GlobalThesaurusGraph)
	if err != nil {
		return fmt.Errorf("failed to build quaternion index: %w", err)
	}

	// Create embedding builder
	GlobalEmbeddingBuilder = NewEmbeddingBuilder(GlobalThesaurusGraph)

	elapsed := time.Since(startTime)

	log.Printf("✅ Linguistic system initialized from cache in %v", elapsed)
	log.Printf("   📚 Thesaurus: %d words, %d relationships",
		GlobalThesaurusGraph.TotalWords,
		GlobalThesaurusGraph.TotalRelations)
	log.Printf("   🧮 Quaternion index: %d embeddings, %d clusters",
		GlobalThesaurusIndex.TotalWords(),
		GlobalThesaurusIndex.TotalClusters())

	return nil
}

// IsInitialized checks if the linguistic system has been initialized
func IsInitialized() bool {
	return GlobalThesaurusGraph != nil &&
		GlobalThesaurusIndex != nil &&
		GlobalEmbeddingBuilder != nil
}

// GetStats returns statistics about the linguistic system
func GetStats() map[string]interface{} {
	if !IsInitialized() {
		return map[string]interface{}{
			"initialized": false,
		}
	}

	return map[string]interface{}{
		"initialized":      true,
		"total_words":      GlobalThesaurusGraph.TotalWords,
		"total_relations":  GlobalThesaurusGraph.TotalRelations,
		"total_embeddings": GlobalThesaurusIndex.TotalWords(),
		"total_clusters":   GlobalThesaurusIndex.TotalClusters(),
		"cluster_stats":    GlobalThesaurusIndex.ClusterStats(),
	}
}

// Shutdown performs cleanup (if needed)
func Shutdown() {
	log.Println("🔌 Shutting down linguistic system...")
	GlobalThesaurusGraph = nil
	GlobalThesaurusIndex = nil
	GlobalEmbeddingBuilder = nil
}
