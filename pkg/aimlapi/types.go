// Package aimlapi - Core types and structures
package aimlapi

// ═══════════════════════════════════════════════════════════════════════════
// REQUEST TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Message represents a chat message
type Message struct {
	Role    string `json:"role"`    // "system", "user", "assistant"
	Content string `json:"content"` // Text content or image URL
	Name    string `json:"name,omitempty"` // Optional name for user
}

// ChatRequest represents a chat completion request
type ChatRequest struct {
	Model            string    `json:"model"`                       // Model ID
	Messages         []Message `json:"messages"`                    // Conversation messages
	Temperature      float64   `json:"temperature,omitempty"`       // 0.0-2.0 (default: 0.7)
	TopP             float64   `json:"top_p,omitempty"`             // Nucleus sampling (default: 1.0)
	N                int       `json:"n,omitempty"`                 // Number of completions (default: 1)
	Stream           bool      `json:"stream,omitempty"`            // Enable streaming
	Stop             []string  `json:"stop,omitempty"`              // Stop sequences
	MaxTokens        int       `json:"max_tokens,omitempty"`        // Max tokens to generate
	PresencePenalty  float64   `json:"presence_penalty,omitempty"`  // -2.0 to 2.0
	FrequencyPenalty float64   `json:"frequency_penalty,omitempty"` // -2.0 to 2.0
	LogitBias        map[string]int `json:"logit_bias,omitempty"`   // Token bias
	User             string    `json:"user,omitempty"`              // User identifier
}

// ChatResponse represents a chat completion response
type ChatResponse struct {
	ID      string   `json:"id"`
	Object  string   `json:"object"`
	Created int64    `json:"created"`
	Model   string   `json:"model"`
	Choices []Choice `json:"choices"`
	Usage   Usage    `json:"usage"`
}

// Choice represents a completion choice
type Choice struct {
	Index        int     `json:"index"`
	Message      Message `json:"message"`
	FinishReason string  `json:"finish_reason"` // "stop", "length", "content_filter"
}

// Usage represents token usage statistics
type Usage struct {
	PromptTokens     int `json:"prompt_tokens"`
	CompletionTokens int `json:"completion_tokens"`
	TotalTokens      int `json:"total_tokens"`
}

// ═══════════════════════════════════════════════════════════════════════════
// ERROR TYPES
// ═══════════════════════════════════════════════════════════════════════════

// APIError represents an API error response
type APIError struct {
	StatusCode int    `json:"status_code"`
	Message    string `json:"message"`
	Type       string `json:"type"`
	Param      string `json:"param,omitempty"`
	Code       string `json:"code,omitempty"`
}

func (e *APIError) Error() string {
	return e.Message
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVENIENCE BUILDERS
// ═══════════════════════════════════════════════════════════════════════════

// NewChatRequest creates a basic chat request
func NewChatRequest(model string, messages ...Message) ChatRequest {
	return ChatRequest{
		Model:       model,
		Messages:    messages,
		Temperature: 0.7,
		MaxTokens:   4000,
	}
}

// NewUserMessage creates a user message
func NewUserMessage(content string) Message {
	return Message{
		Role:    "user",
		Content: content,
	}
}

// NewSystemMessage creates a system message
func NewSystemMessage(content string) Message {
	return Message{
		Role:    "system",
		Content: content,
	}
}

// NewAssistantMessage creates an assistant message
func NewAssistantMessage(content string) Message {
	return Message{
		Role:    "assistant",
		Content: content,
	}
}

// ═══════════════════════════════════════════════════════════════════════════
// CONVERSATION HELPERS
// ═══════════════════════════════════════════════════════════════════════════

// Conversation represents a multi-turn conversation
type Conversation struct {
	Messages []Message
}

// NewConversation creates a new conversation
func NewConversation() *Conversation {
	return &Conversation{
		Messages: []Message{},
	}
}

// AddSystem adds a system message
func (c *Conversation) AddSystem(content string) *Conversation {
	c.Messages = append(c.Messages, NewSystemMessage(content))
	return c
}

// AddUser adds a user message
func (c *Conversation) AddUser(content string) *Conversation {
	c.Messages = append(c.Messages, NewUserMessage(content))
	return c
}

// AddAssistant adds an assistant message
func (c *Conversation) AddAssistant(content string) *Conversation {
	c.Messages = append(c.Messages, NewAssistantMessage(content))
	return c
}

// ToChatRequest converts conversation to chat request
func (c *Conversation) ToChatRequest(model string) ChatRequest {
	return NewChatRequest(model, c.Messages...)
}

// Reset clears all messages
func (c *Conversation) Reset() {
	c.Messages = []Message{}
}

// GetLastMessage returns the last message
func (c *Conversation) GetLastMessage() *Message {
	if len(c.Messages) == 0 {
		return nil
	}
	return &c.Messages[len(c.Messages)-1]
}

// GetMessageCount returns number of messages
func (c *Conversation) GetMessageCount() int {
	return len(c.Messages)
}
