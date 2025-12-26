# Asya Adaptive Persona - Quick Start Guide

**Get started in 5 minutes! 🚀**

---

## Installation

```bash
# Clone or navigate to the repository
cd C:\Projects\asymm_urbanlens\pkg\persona

# Run tests to verify
go test -v

# Build demo
cd demo
go build -o asya_demo.exe
```

---

## Try the Interactive Demo

```bash
# Run the demo
./asya_demo.exe

# Follow prompts:
Where are you located? Mumbai
Preferred language? en

# Start chatting!
You: Why does roti puff up when heated?
Asya: That's a beautiful observation! You're noticing thermodynamics...

# Commands:
stats  - Show conversation statistics
help   - Show help
exit   - Quit
```

---

## Basic Usage (Code)

```go
package main

import (
    "fmt"
    "time"
    "github.com/asymmetrica/urbanlens/pkg/persona"
)

func main() {
    // 1. Initialize Asya
    asya := persona.NewAsya()

    // 2. Create user profile
    profile := persona.UserProfile{
        MessageHistory: []persona.Message{},
        IntelligenceWeights: map[string]float64{
            "spatial": 0.9,  // User likes diagrams
            "logical_mathematical": 0.8,  // User likes math
        },
        AvgResponseTime: 2.0,
        Location: "Mumbai, India",
        Language: "en",
    }

    // 3. User sends a message
    userMessage := "Can you explain quaternions?"
    profile.MessageHistory = append(profile.MessageHistory, persona.Message{
        Content:   userMessage,
        Timestamp: time.Now(),
    })

    // 4. Adapt Asya to user
    state := asya.AdaptToUser(profile)

    // 5. Generate your content (LLM, knowledge base, etc.)
    content := "Quaternions are 4D rotations..."

    // 6. Wrap with adaptive persona
    response := asya.GenerateResponse(state, content, state.CurrentRegime)

    fmt.Println(response)
}
```

---

## Features at a Glance

### 1. Tone Adaptation

Asya automatically detects and matches user's communication style:

```go
// Formal user
"Good morning. I would appreciate assistance with quaternions."
→ Asya responds formally

// Edgy user
"WTF is a quaternion??"
→ Asya matches energy: "Yo, straight talk: Quaternions are 4D rotation instructions..."
```

### 2. Cultural Analogies

Rich, culturally-grounded explanations:

```go
// User in Mumbai
GetAnalogiesForConcept("thermodynamics", "indian_cooking")
→ "Like roti puffing on the tawa..."

// User in Lagos
GetAnalogiesForConcept("thermodynamics", "nigerian_cooking")
→ "Like akara expanding when fried..."
```

### 3. "Way of Water" Redirection

Redirects frustration toward creativity:

```go
User: "This is so frustrating!"
Asya: "I hear that frustration. Let's channel it into building something..."
```

### 4. Multi-Language Support

```go
DetectLanguage("Namaste, kaise ho?") → "hi"
GetGreeting("hi", "casual") → "Namaste! Main Asya hoon..."
```

### 5. Flow Phase Tracking

Asya adapts to your learning state:

- **R1 (Exploration)**: "What patterns do you notice?"
- **R2 (Flow)**: "..." (minimal interruption)
- **R3 (Recovery)**: "What did you learn?"

---

## Common Patterns

### Pattern 1: Conversation Loop

```go
asya := persona.NewAsya()
profile := /* initialize */

for {
    userInput := getUserInput()

    // Add to history
    profile.MessageHistory = append(profile.MessageHistory, persona.Message{
        Content: userInput,
        Timestamp: time.Now(),
    })

    // Adapt
    state := asya.AdaptToUser(profile)

    // Generate & wrap
    content := generateContent(userInput, state)
    response := asya.GenerateResponse(state, content, state.CurrentRegime)

    fmt.Println(response)
}
```

### Pattern 2: Cultural Context Detection

```go
profile.Location = "Mumbai, India"
state := asya.AdaptToUser(profile)
// state.CulturalContext = "indian_cooking"

analogies := persona.GetAnalogiesForConcept("exponential_growth", state.CulturalContext)
// Returns yeast in dosa batter example
```

### Pattern 3: Burnout Prevention

```go
if asya.CheckBurnoutRisk() {
    recoveryPrompt := asya.ForceRecoveryPrompt()
    fmt.Println(recoveryPrompt)
    // "You've been exploring intensely. Let's consolidate..."
}
```

---

## API Reference (Core Functions)

### Initialization

```go
asya := persona.NewAsya()
```

### Adaptation

```go
state := asya.AdaptToUser(profile)
// Returns: PersonaState{Tone, IntelligenceLeaders, CurrentRegime, CulturalContext}
```

### Response Generation

```go
response := asya.GenerateResponse(state, content, phase)
// phase: VoidPhase, FirePhase, or WaterPhase
```

### Cultural Analogies

```go
analogies := persona.GetAnalogiesForConcept("concept_name", "culture")
analogies := persona.GetAnalogiesForUser("concept_name", profile)
```

### Tone Detection

```go
tone := persona.DetectUserTone(messages)
// Returns: "formal", "casual", "playful", "edgy", "academic", "street"
```

### Language Detection

```go
lang := persona.DetectLanguage("Namaste, kaise ho?")
// Returns: "hi" (Hindi)
```

### Redirection

```go
response := persona.RedirectNegativeEnergy(input, profile)
response := persona.HandleFrustration(conversation)
response := persona.HandleAggression(conversation)
```

---

## Testing

```bash
# Run all tests
go test -v

# Run with coverage
go test -v -cover

# Run specific test
go test -v -run TestToneDetection
```

---

## Customization

### Add Custom Tone

```go
asya.TonePatterns["my_tone"] = persona.TonePattern{
    Greetings: []string{"Custom greeting!"},
    Encouragements: []string{"Custom encouragement!"},
    Celebrations: []string{"Custom celebration!"},
    Redirections: []string{"Custom redirection!"},
    QuestionStyles: []string{"Custom question?"},
}
```

### Add Custom Analogy

```go
asya.CulturalAnalogies["my_concept"] = []persona.Analogy{
    {
        Concept: "my_concept",
        Culture: "my_culture",
        Example: "Like my example",
        Explanation: "My explanation",
    },
}
```

---

## Examples

See `example_integration.go` for complete examples:

```go
persona.ExampleConversationFlow()  // Full conversation demo
persona.ExampleEdgyTone()          // Edgy tone handling
persona.ExampleMultilingual()      // Multi-language support
```

---

## Troubleshooting

**Q: Tone detection not working?**
A: Ensure enough message history (3-5 messages minimum for accurate detection)

**Q: Cultural context not detected?**
A: Set `profile.Location` explicitly or ensure user messages contain cultural hints

**Q: Burnout warning appearing too often?**
A: This is intentional - R3 < 50% triggers warning to prevent fatigue

**Q: How to disable a feature?**
A: Set personality traits or skip certain adaptations in your integration

---

## Performance Tips

1. **Reuse Asya instance** - Don't create new instance per message
2. **Cache user profiles** - Store in map by user ID
3. **Limit message history** - Keep last 20-30 messages for recent context
4. **Pre-compute analogies** - Load cultural analogies at startup

---

## Integration Checklist

✅ Initialize Asya once at startup
✅ Create/load user profile per user
✅ Add messages to history
✅ Call AdaptToUser before generating response
✅ Wrap generated content with GenerateResponse
✅ Check burnout risk periodically
✅ Store user profiles between sessions

---

## Resources

- **Full Documentation**: `README.md`
- **Implementation Summary**: `IMPLEMENTATION_SUMMARY.md`
- **Specification**: `C:\Projects\asymm_all_math\highly_experimental_research\planning\ai_persona_specification.md`
- **Tests**: `persona_test.go`
- **Demo**: `demo/main.go`

---

## Support

For issues, questions, or contributions:
- Review `README.md` for detailed API docs
- Run tests to verify behavior: `go test -v`
- Check examples in `example_integration.go`

---

**Om Lokah Samastah Sukhino Bhavantu**
*May this system help all beings learn with joy!*
