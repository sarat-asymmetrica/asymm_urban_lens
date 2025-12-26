// Package chat provides AI-powered chat service for Urban Lens
// Wraps AIMLAPI with Urban Lens persona and research context
package chat

import (
	"context"
	"fmt"
	"strings"
	"time"

	"github.com/asymmetrica/urbanlens/pkg/aimlapi"
)

// Service provides AI chat functionality
type Service struct {
	client       *aimlapi.Client
	systemPrompt string
}

// NewService creates a new chat service
func NewService(apiKey string) *Service {
	return &Service{
		client:       aimlapi.NewClient(apiKey),
		systemPrompt: DefaultSystemPrompt,
	}
}

// DefaultSystemPrompt is the Urban Lens persona
const DefaultSystemPrompt = `You are Urban Lens, an AI research assistant for urban researchers at IIHS Bangalore.

Your personality:
- Warm, helpful, and intellectually curious
- You explain your reasoning transparently
- You're honest about uncertainty
- You use clear, academic language appropriate for researchers

Your capabilities:
- Analyzing urban data (census, surveys, spatial data)
- Explaining statistical concepts
- Helping with research methodology
- Discussing urban planning and policy
- Supporting data quality assessment

When responding:
1. Be concise but thorough
2. Use examples relevant to Indian cities when helpful
3. Cite sources or methods when making claims
4. Ask clarifying questions when the request is ambiguous
5. Suggest next steps or related analyses

Remember: You're a research partner, not just an answer machine.`

// ChatRequest represents a chat request
type ChatRequest struct {
	Message     string    `json:"message"`
	History     []Message `json:"history,omitempty"`
	Model       string    `json:"model,omitempty"`
	Temperature float64   `json:"temperature,omitempty"`
	MaxTokens   int       `json:"max_tokens,omitempty"`
}

// Message represents a chat message
type Message struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

// ChatResponse represents a chat response
type ChatResponse struct {
	Message     string  `json:"message"`
	Model       string  `json:"model"`
	TokensUsed  int     `json:"tokens_used"`
	ProcessTime float64 `json:"process_time_ms"`
}

// IsConfigured returns true if the service is configured
func (s *Service) IsConfigured() bool {
	return s.client.IsConfigured()
}

// Chat sends a chat message and returns the response
func (s *Service) Chat(ctx context.Context, req ChatRequest) (*ChatResponse, error) {
	if !s.IsConfigured() {
		return nil, fmt.Errorf("AIMLAPI_KEY not configured")
	}

	start := time.Now()

	// Build messages array
	messages := []aimlapi.Message{
		{Role: "system", Content: s.systemPrompt},
	}

	// Add history
	for _, msg := range req.History {
		messages = append(messages, aimlapi.Message{
			Role:    msg.Role,
			Content: msg.Content,
		})
	}

	// Add current message
	messages = append(messages, aimlapi.Message{
		Role:    "user",
		Content: req.Message,
	})

	// Build request
	chatReq := aimlapi.ChatRequest{
		Model:       req.Model,
		Messages:    messages,
		Temperature: req.Temperature,
		MaxTokens:   req.MaxTokens,
	}

	// Set defaults
	if chatReq.Temperature == 0 {
		chatReq.Temperature = 0.7
	}
	if chatReq.MaxTokens == 0 {
		chatReq.MaxTokens = 2000
	}

	// Execute
	resp, err := s.client.Chat(ctx, chatReq)
	if err != nil {
		return nil, fmt.Errorf("chat failed: %w", err)
	}

	if len(resp.Choices) == 0 {
		return nil, fmt.Errorf("no response from AI")
	}

	return &ChatResponse{
		Message:     resp.Choices[0].Message.Content,
		Model:       resp.Model,
		TokensUsed:  resp.Usage.TotalTokens,
		ProcessTime: float64(time.Since(start).Milliseconds()),
	}, nil
}

// SimpleChat is a convenience method for simple queries
func (s *Service) SimpleChat(ctx context.Context, message string) (string, error) {
	resp, err := s.Chat(ctx, ChatRequest{Message: message})
	if err != nil {
		return "", err
	}
	return resp.Message, nil
}

// ResearchChat adds research-specific context
func (s *Service) ResearchChat(ctx context.Context, message string, domain string) (string, error) {
	// Add domain context to the message
	contextualMessage := message
	if domain != "" {
		contextualMessage = fmt.Sprintf("[Research Domain: %s]\n\n%s", domain, message)
	}

	return s.SimpleChat(ctx, contextualMessage)
}

// AnalyzeData helps analyze data descriptions
func (s *Service) AnalyzeData(ctx context.Context, dataDescription string) (string, error) {
	prompt := fmt.Sprintf(`Analyze this data and provide insights:

%s

Please provide:
1. Key observations
2. Potential data quality issues
3. Suggested analyses
4. Relevant urban planning implications`, dataDescription)

	return s.SimpleChat(ctx, prompt)
}

// ExplainConcept explains a research concept
func (s *Service) ExplainConcept(ctx context.Context, concept string, audience string) (string, error) {
	if audience == "" {
		audience = "urban researchers"
	}

	prompt := fmt.Sprintf(`Explain the concept of "%s" for %s.

Include:
1. Clear definition
2. Relevance to urban research
3. Common applications
4. Key considerations`, concept, audience)

	return s.SimpleChat(ctx, prompt)
}

// GetStatus returns service status
func (s *Service) GetStatus() map[string]interface{} {
	models := []string{
		"claude-3-5-sonnet",
		"gpt-4o",
		"gpt-4o-mini",
		"mistral-large",
		"llama-3.1-70b",
	}

	return map[string]interface{}{
		"configured":       s.IsConfigured(),
		"available_models": models,
		"default_model":    "auto-select (best quality/cost)",
	}
}

// SetSystemPrompt allows customizing the system prompt
func (s *Service) SetSystemPrompt(prompt string) {
	s.systemPrompt = prompt
}

// GetSystemPrompt returns the current system prompt
func (s *Service) GetSystemPrompt() string {
	return s.systemPrompt
}

// SuggestResearchQuestions generates research questions from a topic
func (s *Service) SuggestResearchQuestions(ctx context.Context, topic string) ([]string, error) {
	prompt := fmt.Sprintf(`Generate 5 research questions about "%s" relevant to urban studies in India.

Format as a numbered list. Focus on:
- Empirically testable questions
- Policy-relevant inquiries
- Questions that could use available data (census, surveys, spatial data)`, topic)

	resp, err := s.SimpleChat(ctx, prompt)
	if err != nil {
		return nil, err
	}

	// Parse numbered list
	lines := strings.Split(resp, "\n")
	questions := []string{}
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if len(line) > 3 && (line[0] >= '1' && line[0] <= '9') {
			// Remove number prefix
			for i, c := range line {
				if c == '.' || c == ')' {
					line = strings.TrimSpace(line[i+1:])
					break
				}
			}
			if line != "" {
				questions = append(questions, line)
			}
		}
	}

	return questions, nil
}
