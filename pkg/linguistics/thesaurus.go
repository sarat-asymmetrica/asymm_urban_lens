package linguistics

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"regexp"
	"strings"

	"github.com/asymmetrica/urbanlens/pkg/vedic"
)

// ThesaurusEntry represents a word and its semantic relationships
type ThesaurusEntry struct {
	Word      string   `json:"word"`
	Synonyms  []string `json:"synonyms"`
	Antonyms  []string `json:"antonyms"`
	Hyponyms  []string `json:"hyponyms"`  // More specific terms
	Hypernyms []string `json:"hypernyms"` // More general terms
	Meronyms  []string `json:"meronyms"`  // Part-of relationships
	Holonyms  []string `json:"holonyms"`  // Whole-of relationships
	Related   []string `json:"related"`   // Other related concepts
	Weight    float64  `json:"weight"`    // Quaternion-based semantic weight
}

// ThesaurusGraph represents the entire semantic relationship network
type ThesaurusGraph struct {
	Entries        map[string]*ThesaurusEntry `json:"entries"`
	TotalWords     int                        `json:"total_words"`
	TotalRelations int                        `json:"total_relations"`
}

// LanguagePackBook represents the JSON structure of processed books
type LanguagePackBook struct {
	Metadata struct {
		Title                 string  `json:"title"`
		Author                string  `json:"author"`
		Category              string  `json:"category"`
		ProcessedAt           string  `json:"processedAt"`
		ProcessingTimeSeconds float64 `json:"processingTimeSeconds"`
		Format                string  `json:"format"`
	} `json:"metadata"`
	Content struct {
		FullText string `json:"fullText"`
	} `json:"content"`
}

// BuildThesaurusGraph constructs a semantic graph from thesaurus books
func BuildThesaurusGraph(oxfordPath, rogetPath string) (*ThesaurusGraph, error) {
	log.Println("🔨 Building thesaurus graph from language packs...")

	graph := &ThesaurusGraph{
		Entries: make(map[string]*ThesaurusEntry),
	}

	// Parse Oxford Thesaurus
	if oxfordPath != "" {
		log.Println("   📖 Parsing Oxford Thesaurus...")
		if err := parseOxfordThesaurus(oxfordPath, graph); err != nil {
			log.Printf("   ⚠️  Warning: Failed to parse Oxford Thesaurus: %v", err)
		} else {
			log.Printf("   ✅ Oxford Thesaurus parsed: %d entries so far", len(graph.Entries))
		}
	}

	// Parse Roget's Thesaurus (if available)
	if rogetPath != "" {
		log.Println("   📖 Parsing Roget's Thesaurus...")
		if err := parseRogetThesaurus(rogetPath, graph); err != nil {
			log.Printf("   ⚠️  Warning: Failed to parse Roget's: %v", err)
		} else {
			log.Printf("   ✅ Roget's Thesaurus parsed: %d entries total", len(graph.Entries))
		}
	}

	// Calculate quaternion weights for all entries
	log.Println("   🧮 Calculating quaternion semantic weights...")
	graph.calculateQuaternionWeights()

	// Count total relations
	graph.TotalWords = len(graph.Entries)
	graph.TotalRelations = graph.countRelations()

	log.Printf("✅ Thesaurus graph built: %d words, %d relationships", graph.TotalWords, graph.TotalRelations)

	return graph, nil
}

// parseOxfordThesaurus extracts semantic relationships from Oxford Thesaurus
func parseOxfordThesaurus(path string, graph *ThesaurusGraph) error {
	// Read the JSON file
	data, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("failed to read Oxford Thesaurus: %w", err)
	}

	var book LanguagePackBook
	if err := json.Unmarshal(data, &book); err != nil {
		return fmt.Errorf("failed to parse JSON: %w", err)
	}

	text := book.Content.FullText

	// Oxford Thesaurus has entries like:
	// "abandon v. 1 give up or over, yield, surrender, leave, cede, let go,
	//  deliver (up), turn over, relinquish: ..."
	//
	// Strategy: Extract headword and synonyms from each entry

	// Pattern to match headword entries (word followed by part of speech)
	headwordPattern := regexp.MustCompile(`(?m)^([a-z]+)\s+(v\.|n\.|adj\.|adv\.)\s+(.+?)(?:\n[a-z]+\s+(?:v\.|n\.|adj\.|adv\.)|$)`)

	// Find all headword entries
	matches := headwordPattern.FindAllStringSubmatch(text, -1)

	for _, match := range matches {
		if len(match) < 4 {
			continue
		}

		headword := strings.ToLower(strings.TrimSpace(match[1]))
		// pos := match[2] // Part of speech (could use for filtering later)
		entryText := match[3]

		if headword == "" {
			continue
		}

		// Extract synonyms from the entry
		// Oxford format: "1 synonym1, synonym2, synonym3: example sentence. 2 more synonyms..."
		synonyms := extractOxfordSynonyms(entryText)

		// Get or create entry
		entry, exists := graph.Entries[headword]
		if !exists {
			entry = &ThesaurusEntry{
				Word:     headword,
				Synonyms: make([]string, 0),
				Antonyms: make([]string, 0),
				Related:  make([]string, 0),
			}
			graph.Entries[headword] = entry
		}

		// Add synonyms (deduplicate)
		for _, syn := range synonyms {
			if !containsString(entry.Synonyms, syn) && syn != headword {
				entry.Synonyms = append(entry.Synonyms, syn)
			}
		}
	}

	return nil
}

// extractOxfordSynonyms extracts synonym words from Oxford entry text
func extractOxfordSynonyms(entryText string) []string {
	synonyms := make([]string, 0)

	// Split by numbered senses (e.g., "1", "2", "3")
	sensePattern := regexp.MustCompile(`\d+\s+(.+?)(?:\d+\s+|$)`)
	senses := sensePattern.FindAllStringSubmatch(entryText, -1)

	for _, sense := range senses {
		if len(sense) < 2 {
			continue
		}

		senseText := sense[1]

		// Extract everything before the first colon (synonyms are before examples)
		parts := strings.Split(senseText, ":")
		if len(parts) > 0 {
			synonymPart := parts[0]

			// Split by commas and semicolons
			synWords := regexp.MustCompile(`[,;]`).Split(synonymPart, -1)

			for _, syn := range synWords {
				// Clean up: remove labels like "Colloq", "Slang", "US", etc.
				syn = cleanSynonym(syn)
				if syn != "" && len(syn) > 1 {
					synonyms = append(synonyms, syn)
				}
			}
		}
	}

	return synonyms
}

// cleanSynonym removes labels and cleans up a synonym string
func cleanSynonym(s string) string {
	// Remove labels: Colloq, Slang, Brit, US, Literary, Archaic, etc.
	labels := []string{
		"Colloq", "Slang", "Taboo", "Archaic", "Old-fashioned",
		"Technical", "Literary", "Brit", "US", "Australian",
		"Canadian", "New Zealand", "or", "also",
	}

	s = strings.TrimSpace(s)
	lower := strings.ToLower(s)

	// Remove labels
	for _, label := range labels {
		s = strings.ReplaceAll(s, label, "")
		s = strings.ReplaceAll(s, strings.ToLower(label), "")
	}

	// Remove parenthetical notes
	s = regexp.MustCompile(`\([^)]*\)`).ReplaceAllString(s, "")

	// Remove anything after a dash or slash
	s = regexp.MustCompile(`[-/].*`).ReplaceAllString(s, "")

	s = strings.TrimSpace(s)
	lower = strings.ToLower(s)

	// Only keep alphabetic words (no numbers, no punctuation)
	if !regexp.MustCompile(`^[a-z\s-]+$`).MatchString(lower) {
		return ""
	}

	return lower
}

// parseRogetThesaurus extracts relationships from Roget's (if available)
func parseRogetThesaurus(path string, graph *ThesaurusGraph) error {
	// Read the JSON file
	data, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("failed to read Roget's Thesaurus: %w", err)
	}

	var book LanguagePackBook
	if err := json.Unmarshal(data, &book); err != nil {
		return fmt.Errorf("failed to parse JSON: %w", err)
	}

	// Roget's has a different structure (categorical organization)
	// For now, we'll extract word lists from the text
	// TODO: Implement Roget's-specific parsing

	log.Println("   ℹ️  Roget's parsing not yet implemented (structure differs from Oxford)")

	return nil
}

// calculateQuaternionWeights computes semantic weights using Vedic quaternions
func (g *ThesaurusGraph) calculateQuaternionWeights() {
	for word, entry := range g.Entries {
		// Encode word as quaternion
		q := vedic.EncodeAsQuaternion(word)

		// Calculate weight based on:
		// 1. Number of relationships (more relationships = higher weight)
		// 2. Quaternion magnitude
		relationCount := float64(len(entry.Synonyms) + len(entry.Antonyms) + len(entry.Related))
		quaternionMag := q.Magnitude()

		// Combine: harmonic mean of relation count and quaternion magnitude
		if relationCount > 0 && quaternionMag > 0 {
			entry.Weight = vedic.HarmonicMean([]float64{relationCount, quaternionMag})
		} else {
			entry.Weight = 0.0
		}
	}
}

// countRelations counts total relationships in the graph
func (g *ThesaurusGraph) countRelations() int {
	total := 0
	for _, entry := range g.Entries {
		total += len(entry.Synonyms)
		total += len(entry.Antonyms)
		total += len(entry.Hyponyms)
		total += len(entry.Hypernyms)
		total += len(entry.Meronyms)
		total += len(entry.Holonyms)
		total += len(entry.Related)
	}
	return total
}

// FindSynonyms finds synonyms for a word
func (g *ThesaurusGraph) FindSynonyms(word string) []string {
	word = strings.ToLower(strings.TrimSpace(word))
	entry, exists := g.Entries[word]
	if !exists {
		return []string{}
	}
	return entry.Synonyms
}

// FindAntonyms finds antonyms for a word
func (g *ThesaurusGraph) FindAntonyms(word string) []string {
	word = strings.ToLower(strings.TrimSpace(word))
	entry, exists := g.Entries[word]
	if !exists {
		return []string{}
	}
	return entry.Antonyms
}

// FindRelated finds related concepts for a word
func (g *ThesaurusGraph) FindRelated(word string) []string {
	word = strings.ToLower(strings.TrimSpace(word))
	entry, exists := g.Entries[word]
	if !exists {
		return []string{}
	}

	// Combine all relationship types
	related := make([]string, 0)
	related = append(related, entry.Synonyms...)
	related = append(related, entry.Antonyms...)
	related = append(related, entry.Hyponyms...)
	related = append(related, entry.Hypernyms...)
	related = append(related, entry.Related...)

	return related
}

// GetEntry retrieves a thesaurus entry for a word
func (g *ThesaurusGraph) GetEntry(word string) *ThesaurusEntry {
	word = strings.ToLower(strings.TrimSpace(word))
	entry, exists := g.Entries[word]
	if !exists {
		return nil
	}
	return entry
}

// SaveToFile saves the thesaurus graph to a JSON file
func (g *ThesaurusGraph) SaveToFile(path string) error {
	data, err := json.MarshalIndent(g, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal graph: %w", err)
	}

	if err := os.WriteFile(path, data, 0644); err != nil {
		return fmt.Errorf("failed to write file: %w", err)
	}

	log.Printf("💾 Thesaurus graph saved to: %s", path)
	return nil
}

// LoadFromFile loads a thesaurus graph from a JSON file
func LoadThesaurusFromFile(path string) (*ThesaurusGraph, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %w", err)
	}

	var graph ThesaurusGraph
	if err := json.Unmarshal(data, &graph); err != nil {
		return nil, fmt.Errorf("failed to unmarshal graph: %w", err)
	}

	log.Printf("📖 Thesaurus graph loaded: %d words, %d relationships", graph.TotalWords, graph.TotalRelations)
	return &graph, nil
}

// containsString checks if a slice contains a string
func containsString(slice []string, target string) bool {
	for _, item := range slice {
		if strings.EqualFold(item, target) {
			return true
		}
	}
	return false
}
