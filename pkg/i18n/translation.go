package i18n

import (
	"context"
	"encoding/json"
	"fmt"
	"strings"
)

// ═══════════════════════════════════════════════════════════════════════════
// TRANSLATION WITH CONTEXT PRESERVATION
// ═══════════════════════════════════════════════════════════════════════════

// AIClient interface for translation (compatible with AIMLAPI)
type AIClient interface {
	ChatCompletion(ctx context.Context, request ChatRequest) (ChatResponse, error)
}

// ChatRequest for AI translation
type ChatRequest struct {
	Model       string    `json:"model"`
	Messages    []Message `json:"messages"`
	Temperature float64   `json:"temperature,omitempty"`
	MaxTokens   int       `json:"max_tokens,omitempty"`
}

// ChatResponse from AI
type ChatResponse struct {
	Choices []Choice `json:"choices"`
}

// Choice in response
type Choice struct {
	Message Message `json:"message"`
}

// Message in chat
type Message struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

// TranslationOptions configures translation behavior
type TranslationOptions struct {
	PreserveTechnicalTerms bool     // Don't translate technical terms
	TechnicalTerms         []string // Specific terms to preserve
	PreserveFormatting     bool     // Keep markdown/formatting
	CulturalAdaptation     bool     // Adapt idioms culturally
	Tone                   string   // "formal", "casual", "academic"
}

// DefaultTranslationOptions returns sensible defaults
func DefaultTranslationOptions() *TranslationOptions {
	return &TranslationOptions{
		PreserveTechnicalTerms: true,
		TechnicalTerms:         PreserveTechnicalTerms,
		PreserveFormatting:     true,
		CulturalAdaptation:     true,
		Tone:                   "casual",
	}
}

// PreserveTechnicalTerms are common terms that should NOT be translated
var PreserveTechnicalTerms = []string{
	// Mathematics
	"theorem", "proof", "lemma", "corollary", "axiom", "proposition",
	"quaternion", "SLERP", "manifold", "topology", "algebra",

	// Computer Science
	"algorithm", "function", "variable", "API", "GPU", "CPU",
	"runtime", "compile", "debug", "deploy", "repository",

	// Lean/Formal Verification
	"Lean", "tactic", "simp", "rw", "intro", "apply", "exact",
	"have", "show", "by", "sorry",

	// Programming Languages
	"Go", "Rust", "Python", "JavaScript", "TypeScript", "Svelte",

	// Asymmetrica-specific
	"VQC", "Phi-Organism", "SAT-Origami", "Williams Optimizer",
	"Three-Regime", "R1", "R2", "R3",

	// Mathematical symbols (keep as-is)
	"∀", "∃", "∈", "∉", "⊂", "⊃", "∪", "∩", "→", "←", "↔", "≤", "≥", "≠", "≈",
	"∞", "∑", "∏", "∫", "∂", "∇", "⊗", "⊕", "⊙",
}

// ═══════════════════════════════════════════════════════════════════════════
// TRANSLATION FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

// TranslateWithContext translates text while preserving technical terms and context
func TranslateWithContext(
	ctx context.Context,
	text string,
	fromLang string,
	toLang string,
	aiClient AIClient,
	options *TranslationOptions,
) (string, error) {
	// If languages are the same, no translation needed
	if fromLang == toLang {
		return text, nil
	}

	// Use default options if not provided
	if options == nil {
		options = DefaultTranslationOptions()
	}

	// Build the translation prompt
	prompt := buildTranslationPrompt(text, fromLang, toLang, options)

	// Call AI for translation
	request := ChatRequest{
		Model: "gpt-4o-mini", // Fast, cheap, good for translation
		Messages: []Message{
			{
				Role:    "system",
				Content: "You are a professional translator specializing in technical and educational content. Preserve technical terms, maintain tone, and ensure cultural appropriateness.",
			},
			{
				Role:    "user",
				Content: prompt,
			},
		},
		Temperature: 0.3, // Low temperature for consistent translation
		MaxTokens:   2000,
	}

	response, err := aiClient.ChatCompletion(ctx, request)
	if err != nil {
		return "", fmt.Errorf("translation failed: %w", err)
	}

	if len(response.Choices) == 0 {
		return "", fmt.Errorf("no translation returned")
	}

	translation := response.Choices[0].Message.Content
	return strings.TrimSpace(translation), nil
}

// buildTranslationPrompt constructs the prompt for AI translation
func buildTranslationPrompt(text string, fromLang string, toLang string, options *TranslationOptions) string {
	var prompt strings.Builder

	// Get language names
	fromLangName := getLanguageName(fromLang)
	toLangName := getLanguageName(toLang)

	prompt.WriteString(fmt.Sprintf("Translate the following text from %s to %s.\n\n", fromLangName, toLangName))

	// Add constraints
	if options.PreserveTechnicalTerms {
		prompt.WriteString("IMPORTANT: Do NOT translate these technical terms:\n")
		for _, term := range options.TechnicalTerms {
			prompt.WriteString(fmt.Sprintf("- %s\n", term))
		}
		prompt.WriteString("\n")
	}

	if options.PreserveFormatting {
		prompt.WriteString("Preserve all formatting (markdown, line breaks, etc.).\n")
	}

	if options.CulturalAdaptation {
		prompt.WriteString("Adapt idioms and expressions to be culturally appropriate for the target language.\n")
	}

	// Tone guidance
	switch options.Tone {
	case "formal":
		prompt.WriteString("Use formal, professional language.\n")
	case "academic":
		prompt.WriteString("Use academic, scholarly language.\n")
	case "casual":
		prompt.WriteString("Use casual, conversational language.\n")
	}

	prompt.WriteString("\nText to translate:\n")
	prompt.WriteString("```\n")
	prompt.WriteString(text)
	prompt.WriteString("\n```\n")
	prompt.WriteString("\nProvide ONLY the translation, no explanations.")

	return prompt.String()
}

// getLanguageName returns the full language name for a code
func getLanguageName(langCode string) string {
	lang, exists := SupportedLanguages[langCode]
	if !exists {
		return langCode
	}
	return lang.Name
}

// ═══════════════════════════════════════════════════════════════════════════
// BATCH TRANSLATION (For Multiple Strings)
// ═══════════════════════════════════════════════════════════════════════════

// TranslateBatch translates multiple strings efficiently
func TranslateBatch(
	ctx context.Context,
	texts []string,
	fromLang string,
	toLang string,
	aiClient AIClient,
	options *TranslationOptions,
) ([]string, error) {
	if fromLang == toLang {
		return texts, nil
	}

	if options == nil {
		options = DefaultTranslationOptions()
	}

	// Build batch prompt
	var prompt strings.Builder
	fromLangName := getLanguageName(fromLang)
	toLangName := getLanguageName(toLang)

	prompt.WriteString(fmt.Sprintf("Translate the following %d texts from %s to %s.\n\n", len(texts), fromLangName, toLangName))

	if options.PreserveTechnicalTerms {
		prompt.WriteString("Do NOT translate: ")
		prompt.WriteString(strings.Join(options.TechnicalTerms[:min(10, len(options.TechnicalTerms))], ", "))
		prompt.WriteString("\n\n")
	}

	prompt.WriteString("Return translations as JSON array in the EXACT same order.\n\n")
	prompt.WriteString("Texts:\n")
	for i, text := range texts {
		prompt.WriteString(fmt.Sprintf("%d. %s\n", i+1, text))
	}
	prompt.WriteString("\nReturn format: [\"translation1\", \"translation2\", ...]")

	request := ChatRequest{
		Model: "gpt-4o-mini",
		Messages: []Message{
			{
				Role:    "system",
				Content: "You are a professional translator. Return translations as JSON array.",
			},
			{
				Role:    "user",
				Content: prompt.String(),
			},
		},
		Temperature: 0.3,
		MaxTokens:   4000,
	}

	response, err := aiClient.ChatCompletion(ctx, request)
	if err != nil {
		return nil, fmt.Errorf("batch translation failed: %w", err)
	}

	if len(response.Choices) == 0 {
		return nil, fmt.Errorf("no translations returned")
	}

	content := response.Choices[0].Message.Content

	// Parse JSON array
	var translations []string
	if err := json.Unmarshal([]byte(content), &translations); err != nil {
		// If JSON parsing fails, fall back to line-by-line
		return fallbackBatchTranslation(ctx, texts, fromLang, toLang, aiClient, options)
	}

	if len(translations) != len(texts) {
		return nil, fmt.Errorf("translation count mismatch: expected %d, got %d", len(texts), len(translations))
	}

	return translations, nil
}

// fallbackBatchTranslation translates one-by-one if batch fails
func fallbackBatchTranslation(
	ctx context.Context,
	texts []string,
	fromLang string,
	toLang string,
	aiClient AIClient,
	options *TranslationOptions,
) ([]string, error) {
	translations := make([]string, len(texts))
	for i, text := range texts {
		translation, err := TranslateWithContext(ctx, text, fromLang, toLang, aiClient, options)
		if err != nil {
			return nil, fmt.Errorf("failed to translate text %d: %w", i, err)
		}
		translations[i] = translation
	}
	return translations, nil
}

// min returns the minimum of two integers
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// ═══════════════════════════════════════════════════════════════════════════
// SMART TRANSLATION (Detect Language First)
// ═══════════════════════════════════════════════════════════════════════════

// SmartTranslate detects source language and translates
func SmartTranslate(
	ctx context.Context,
	text string,
	toLang string,
	aiClient AIClient,
	options *TranslationOptions,
) (string, error) {
	// Detect source language
	detectedLang, confidence := DetectLanguage(text)

	// If confidence is too low, assume English
	if confidence < 0.3 {
		detectedLang = SupportedLanguages["en"]
	}

	// Translate
	return TranslateWithContext(ctx, text, detectedLang.Code, toLang, aiClient, options)
}

// ═══════════════════════════════════════════════════════════════════════════
// TERM PRESERVATION HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// AddTechnicalTerms adds custom technical terms to preserve
func (opts *TranslationOptions) AddTechnicalTerms(terms ...string) {
	if opts.TechnicalTerms == nil {
		opts.TechnicalTerms = PreserveTechnicalTerms
	}
	opts.TechnicalTerms = append(opts.TechnicalTerms, terms...)
}

// ExtractTechnicalTerms identifies potential technical terms in text
func ExtractTechnicalTerms(text string) []string {
	var terms []string

	// Look for words in PreserveTechnicalTerms
	for _, term := range PreserveTechnicalTerms {
		if strings.Contains(text, term) {
			terms = append(terms, term)
		}
	}

	// Look for CamelCase words (likely technical)
	words := strings.Fields(text)
	for _, word := range words {
		if isCamelCase(word) {
			terms = append(terms, word)
		}
	}

	// Look for SCREAMING_SNAKE_CASE (constants)
	for _, word := range words {
		if isScreamingSnakeCase(word) {
			terms = append(terms, word)
		}
	}

	return terms
}

// isCamelCase checks if a word is in CamelCase
func isCamelCase(word string) bool {
	if len(word) < 2 {
		return false
	}
	hasUpper := false
	hasLower := false
	for _, r := range word {
		if r >= 'A' && r <= 'Z' {
			hasUpper = true
		}
		if r >= 'a' && r <= 'z' {
			hasLower = true
		}
	}
	return hasUpper && hasLower
}

// isScreamingSnakeCase checks if a word is in SCREAMING_SNAKE_CASE
func isScreamingSnakeCase(word string) bool {
	if len(word) < 2 {
		return false
	}
	for _, r := range word {
		if !((r >= 'A' && r <= 'Z') || r == '_' || (r >= '0' && r <= '9')) {
			return false
		}
	}
	return strings.Contains(word, "_")
}
