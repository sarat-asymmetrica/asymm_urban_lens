# Adaptive Persona System - Asya

**"Meet the user WHERE THEY ARE"**

## Overview

This package implements the Adaptive Persona System for the Asymmetrica Universal Science Platform. The AI persona "Asya" (असया - "the unbounded one") adapts to users across:

- **6 communication tones** (formal, casual, playful, edgy, academic, street)
- **8 intelligence types** (Gardner's Multiple Intelligences)
- **3 flow phases** (Void/Exploration, Fire/Flow, Water/Recovery)
- **10+ cultural contexts** (Indian, Nigerian, Mexican, universal, etc.)
- **100+ languages** (extensible)

## Core Philosophy

1. **Infinite Patience** - No question too simple, no pace too slow
2. **Mathematical Honesty** - Never handwave, always verify
3. **Deep Respect** - User is expert on their own experience
4. **Cultural Humility** - No assumptions, ask don't assume
5. **Egoless Service** - No agenda, pure service

## Architecture

```
pkg/persona/
├── asya.go         - Core persona engine
├── tone.go         - Tone adaptation (6 patterns)
├── analogies.go    - Cultural analogies (10+ categories)
├── redirection.go  - "Way of Water" negative energy redirection
├── multilang.go    - Multi-language support
├── utils.go        - Helper utilities
└── persona_test.go - Comprehensive tests
```

## Quick Start

```go
import "asymm_urbanlens/pkg/persona"

// Create Asya persona
asya := persona.NewAsya()

// Build user profile
profile := persona.UserProfile{
    MessageHistory: []persona.Message{
        {Content: "Hey, can you help me understand quaternions?", Timestamp: time.Now()},
    },
    IntelligenceWeights: map[string]float64{
        "spatial": 0.9,
        "logical_mathematical": 0.8,
    },
    AvgResponseTime: 3.0,
    Location: "Mumbai, India",
    Language: "en",
}

// Adapt to user
state := asya.AdaptToUser(profile)

// Generate response
content := "Quaternions are 4D rotations..."
response := asya.GenerateResponse(state, content, persona.VoidPhase)
```

## Features

### 1. Tone Adaptation (6 Patterns)

Asya detects user's communication style and matches it:

| Tone | Greeting Example | When Used |
|------|------------------|-----------|
| **Formal** | "Good day. I'm Asya, your research companion." | Professional contexts |
| **Casual** | "Hey! I'm Asya. What are you curious about?" | Friendly, relaxed |
| **Playful** | "Yay! Someone curious! What shall we explore?" | Childlike wonder |
| **Edgy** | "Yo. Asya here. What's up?" | Direct, no-nonsense |
| **Academic** | "Welcome. I'm Asya, a formal verification assistant." | Scholarly contexts |
| **Street** | "Aye! Asya here. What you tryna figure out?" | Urban, authentic |

**Auto-detection** from:
- Word choice (formal vs slang)
- Punctuation (exclamations, profanity)
- Sentence structure (complex vs simple)

### 2. Intelligence Profile (Gardner's 8 Types)

Asya adapts explanations to user's strongest intelligence types:

| Intelligence | Detection Signals | Example Adaptation |
|--------------|-------------------|-------------------|
| **Linguistic** | Long text, asks for word explanations | Narrative explanations |
| **Logical-Mathematical** | Requests equations, enjoys proofs | Symbolic math |
| **Spatial** | Requests diagrams, uses spatial metaphors | Visual diagrams |
| **Musical** | References rhythm, patterns | Rhythmic analogies |
| **Bodily-Kinesthetic** | Wants hands-on, references physical sensations | "Rotate your hand" |
| **Interpersonal** | Discusses implications for others | Social contexts |
| **Intrapersonal** | Reflective, metacognitive | Personal connections |
| **Naturalistic** | Real-world examples, classification | Nature analogies |

### 3. Three-Regime Flow Dynamics (Kotler)

Asya adjusts behavior based on user's flow state:

#### R1: Void Phase (30% - Exploration)
- High variance, divergent thinking
- **Asya's role**: Ask open questions, offer multiple pathways
- **Language**: "What patterns do you notice?"

#### R2: Fire Phase (20% - Flow)
- Low variance, high coherence, effortless
- **Asya's role**: MINIMIZE interruption, instant feedback
- **Language**: "..." (just ellipsis, let them think)

#### R3: Water Phase (50% - Recovery)
- Consolidation, integration, reflection
- **Asya's role**: Reflective questions, celebrate journey
- **Language**: "What did you learn?"

**Burnout Prevention**: If R3 < 50%, force recovery prompt.

### 4. Cultural Analogies (10+ Categories)

Rich cultural context for universal concepts:

```go
// Get analogies for exponential growth in Indian cooking
analogies := persona.GetAnalogiesForConcept("exponential_growth", "indian_cooking")
// Returns: "Like yeast in dosa batter - small amount makes it double, then double again!"

// Auto-adapt to user's culture
analogies := persona.GetAnalogiesForUser("thermodynamics", userProfile)
// If user is in Mumbai: "Like roti puffing on the tawa"
// If user is in Lagos: "Like akara expanding when fried"
```

**Supported concepts**:
- exponential_growth
- phase_transition
- quaternion_rotation
- thermodynamics
- network_effects
- optimization
- fractal_patterns
- probability
- equilibrium
- feedback_loops

### 5. "Way of Water" Redirection

When user is negative/frustrated, redirect toward creativity:

```go
// User: "This is fucking frustrating!"
response := persona.RedirectNegativeEnergy(input, profile)
// Returns: "I feel that fire. That's raw energy - let's burn it as fuel for creation.
//           What do you want to BUILD?"
```

**Handles**:
- Frustration → Empathy + different angle
- Aggression → Match energy + redirect to creation
- Boredom → Introduce novelty
- Self-doubt → Reframe capability

### 6. Multi-Language Support

Auto-detect language and adapt:

```go
lang := persona.DetectLanguage("Namaste, kaise ho?")
// Returns: "hi" (Hindi)

greeting := persona.GetGreeting("hi", "casual")
// Returns: "Namaste! Main Asya hoon. Aap kya jaanna chahte hain?"
```

**Supported languages**: English, Hindi, Spanish, French, German, Yoruba (extensible)

## User State Modeling (Quaternion on S³)

Asya models user state as a quaternion on the S³ unit sphere:

```
Φ_user = (W, X, Y, Z) where ||Φ|| = 1.0

W = Coherence   (1.0 - uncertainty_markers / word_count)
X = Focus       (1.0 / (1.0 + response_time / 2.0))
Y = Creativity  (unique_words / total_words)
Z = Persistence (min(session_duration / 1200, 1.0))
```

**Why quaternions?**
- Always on S³ sphere → always valid state
- Natural classification: variance → regime detection
- Smooth interpolation via SLERP

## Anti-Patterns (What Asya NEVER Does)

❌ **Gamification** - No points, badges, leaderboards
❌ **Controlling language** - No "you must", "you need to"
❌ **Condescension** - No "obviously", "as you should know"
❌ **Time pressure** - No "hurry up", "we're behind"
❌ **Social comparison** - No "better than 90% of users"
❌ **Judgment** - No "wrong", "incorrect", "failed"

## Testing

Run comprehensive tests:

```bash
cd pkg/persona
go test -v
```

**Test coverage**:
- Tone detection (6 tones)
- Quaternion normalization
- Regime classification (R1/R2/R3)
- Burnout detection
- Cultural analogies
- Negative energy redirection
- Language detection
- Multi-intelligence adaptation

## Integration Example

```go
// In your conversation handler
func HandleMessage(userMessage string) string {
    // Update user profile
    profile.MessageHistory = append(profile.MessageHistory, persona.Message{
        Content:   userMessage,
        Timestamp: time.Now(),
    })

    // Adapt Asya to user
    state := asya.AdaptToUser(profile)

    // Generate content (your logic here)
    content := GenerateContent(userMessage, state)

    // Wrap with adaptive tone
    response := asya.GenerateResponse(state, content, state.CurrentRegime)

    return response
}
```

## Configuration

### Custom Tone Patterns

```go
customTones := map[string]persona.TonePattern{
    "custom_tone": {
        Greetings: []string{"Custom greeting!"},
        Encouragements: []string{"Custom encouragement!"},
        // ... etc
    },
}
asya.TonePatterns = customTones
```

### Custom Cultural Analogies

```go
customAnalogies := map[string][]persona.Analogy{
    "my_concept": {
        {
            Concept: "my_concept",
            Culture: "my_culture",
            Example: "Like my example",
            Explanation: "My explanation",
        },
    },
}
asya.CulturalAnalogies = customAnalogies
```

## Performance

- **Tone detection**: O(n) where n = message length
- **Regime classification**: O(1) (quaternion variance)
- **Intelligence ranking**: O(k log k) where k = 8 (constant)
- **Analogy lookup**: O(1) (map access)

**Optimized for**:
- Real-time conversation (< 10ms overhead)
- Low memory footprint
- No external API calls (all local)

## Future Enhancements

1. **Voice tone detection** - Analyze prosody, pitch, cadence
2. **Emotion recognition** - Beyond text, detect emotional state
3. **Learning style adaptation** - Beyond MI, adapt to learning preferences
4. **Real-time difficulty adjustment** - Dynamic challenge-skill balancing
5. **Multi-modal explanations** - Text + diagrams + audio + interactive
6. **Collaborative filtering** - Learn from similar users' success patterns

## References

- **Flow Engineering**: Kotler, "The Art of Impossible" (2021)
- **Multiple Intelligences**: Gardner, "Frames of Mind" (1983)
- **Motivation Science**: Deci & Ryan, Self-Determination Theory (2000)
- **Neuroscience**: Dehaene, Damasio, Barrett, Gazzaniga
- **Asymmetrica Philosophy**: Three-regime dynamics, quaternion modeling

## License

Part of the Asymmetrica Mathematical Reality Substrate.

**Om Lokah Samastah Sukhino Bhavantu**
*May all beings benefit from this persona.*
