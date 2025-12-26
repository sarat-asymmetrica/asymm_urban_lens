// Package linguistics provides NLP processing with quaternion-based semantic understanding
// Ported from Ananta to Urban Lens for IIHS ecosystem
package linguistics

import (
	"strings"
)

// LanguageOperator represents transformation operators for semantic manipulation
type LanguageOperator int

const (
	SYNONYM      LanguageOperator = iota // Replace with equivalent meaning
	ANTONYM                              // Negate meaning
	HYPONYM                              // Specialize (vehicle → car)
	HYPERNYM                             // Generalize (car → vehicle)
	MERONYM                              // Part-of (wheel → car)
	HOLONYM                              // Whole-of (car → wheel)
	ANALOGICAL                           // A:B :: C:? pattern
	COMPOSITIONAL                        // Combine multiple operators
)

// String returns the string representation of an operator
func (op LanguageOperator) String() string {
	switch op {
	case SYNONYM:
		return "SYNONYM"
	case ANTONYM:
		return "ANTONYM"
	case HYPONYM:
		return "HYPONYM"
	case HYPERNYM:
		return "HYPERNYM"
	case MERONYM:
		return "MERONYM"
	case HOLONYM:
		return "HOLONYM"
	case ANALOGICAL:
		return "ANALOGICAL"
	case COMPOSITIONAL:
		return "COMPOSITIONAL"
	default:
		return "UNKNOWN"
	}
}

// ApplyOperator applies a semantic transformation to a word using the thesaurus graph
func ApplyOperator(word string, op LanguageOperator, thesaurus *ThesaurusGraph) []string {
	if thesaurus == nil {
		return []string{}
	}

	word = strings.ToLower(strings.TrimSpace(word))
	entry, exists := thesaurus.Entries[word]
	if !exists {
		return []string{}
	}

	switch op {
	case SYNONYM:
		return entry.Synonyms
	case ANTONYM:
		return entry.Antonyms
	case HYPONYM:
		return entry.Hyponyms
	case HYPERNYM:
		return entry.Hypernyms
	case MERONYM:
		return entry.Meronyms
	case HOLONYM:
		return entry.Holonyms
	case ANALOGICAL:
		return entry.Related
	default:
		return []string{}
	}
}

// ApplyCompositional applies multiple operators in sequence
// Example: Find synonyms of antonyms of "good" → synonyms("bad") = ["evil", "wicked", ...]
func ApplyCompositional(word string, operators []LanguageOperator, thesaurus *ThesaurusGraph) []string {
	if len(operators) == 0 {
		return []string{word}
	}

	results := []string{word}

	for _, op := range operators {
		nextResults := make([]string, 0)
		seen := make(map[string]bool)

		for _, currentWord := range results {
			transformed := ApplyOperator(currentWord, op, thesaurus)
			for _, t := range transformed {
				if !seen[t] {
					seen[t] = true
					nextResults = append(nextResults, t)
				}
			}
		}

		results = nextResults
		if len(results) == 0 {
			break // No more transformations possible
		}
	}

	return results
}

// FindAnalogy finds analogical completions: A:B :: C:?
// Example: "hot":"cold" :: "day":? → ["night"]
func FindAnalogy(a, b, c string, thesaurus *ThesaurusGraph) []string {
	// Strategy: Find the relationship between A and B,
	// then apply the same relationship to C

	a = strings.ToLower(strings.TrimSpace(a))
	b = strings.ToLower(strings.TrimSpace(b))
	c = strings.ToLower(strings.TrimSpace(c))

	// Check if B is in A's related words (and what type of relation)
	entryA, existsA := thesaurus.Entries[a]
	if !existsA {
		return []string{}
	}

	// Determine the operator that transforms A → B
	var operator LanguageOperator
	found := false

	if contains(entryA.Synonyms, b) {
		operator = SYNONYM
		found = true
	} else if contains(entryA.Antonyms, b) {
		operator = ANTONYM
		found = true
	} else if contains(entryA.Hyponyms, b) {
		operator = HYPONYM
		found = true
	} else if contains(entryA.Hypernyms, b) {
		operator = HYPERNYM
		found = true
	}

	if !found {
		return []string{}
	}

	// Apply the same operator to C
	return ApplyOperator(c, operator, thesaurus)
}

// contains checks if a slice contains a string
func contains(slice []string, target string) bool {
	for _, item := range slice {
		if strings.EqualFold(item, target) {
			return true
		}
	}
	return false
}

// GetSemanticDistance computes the semantic distance between two words
// Distance is measured by the number of hops needed in the thesaurus graph
func GetSemanticDistance(word1, word2 string, thesaurus *ThesaurusGraph) int {
	if thesaurus == nil {
		return -1
	}

	word1 = strings.ToLower(strings.TrimSpace(word1))
	word2 = strings.ToLower(strings.TrimSpace(word2))

	if word1 == word2 {
		return 0
	}

	// BFS to find shortest path
	visited := make(map[string]bool)
	queue := []struct {
		word  string
		depth int
	}{{word1, 0}}

	maxDepth := 5 // Limit search depth

	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		if current.depth > maxDepth {
			break
		}

		if visited[current.word] {
			continue
		}
		visited[current.word] = true

		if current.word == word2 {
			return current.depth
		}

		entry, exists := thesaurus.Entries[current.word]
		if !exists {
			continue
		}

		// Add all related words to queue
		neighbors := make([]string, 0)
		neighbors = append(neighbors, entry.Synonyms...)
		neighbors = append(neighbors, entry.Antonyms...)
		neighbors = append(neighbors, entry.Hyponyms...)
		neighbors = append(neighbors, entry.Hypernyms...)

		for _, neighbor := range neighbors {
			if !visited[neighbor] {
				queue = append(queue, struct {
					word  string
					depth int
				}{neighbor, current.depth + 1})
			}
		}
	}

	return -1 // Not found within maxDepth
}
