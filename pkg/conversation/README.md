# Conversation Engine - Universal Science Discovery Platform

**The Heart of UrbanLens**: Enables anyone to go from everyday observation → formalized scientific theorem

## 🎯 What Is This?

The Conversation Engine implements the **Sarat Method** + **Void-Flow-Solution Framework** to guide users through scientific discovery using natural conversation.

```
"I miss cooking" → Mustard seeds popping → Phonon Resonance Healing System
         (45 minutes, Christmas Eve 2025)
```

This is NOT a chatbot. This is a **discovery catalyst** that:

1. **Meets users where they are** - Grandmom in Telugu, PhD student in English, child with simple wonder
2. **Guides without prescribing** - Asks questions that unlock thinking, doesn't provide answers
3. **Adapts to cognitive phase** - Different prompts for Void (exploring) vs Flow (converging) vs Solution (formalizing)
4. **Honors all intelligence types** - Kinesthetic, linguistic, spatial, logical equally valued
5. **Celebrates discovery** - Makes the user feel like the genius they are

## 🔄 The Sarat Method (5 Phases)

```
┌──────────────┐
│   GREETING   │ ─────► Language detection, establish rapport
└──────┬───────┘
       ▼
┌──────────────┐
│  ANCHORING   │ ─────► Get CONCRETE, SENSORY observation (Void Phase)
└──────┬───────┘
       ▼
┌──────────────┐
│ WHY-CHAINING │ ─────► Ask "why" 5+ times, go DEEP (Void → Flow)
└──────┬───────┘
       ▼
┌──────────────┐
│ SYNTHESIZING │ ─────► Connect to existing knowledge (Flow Phase)
└──────┬───────┘
       ▼
┌──────────────┐
│ FORMALIZING  │ ─────► Create Lean theorem (Solution Phase)
└──────┬───────┘
       ▼
┌──────────────┐
│ CELEBRATING  │ ─────► Honor discovery, encourage sharing
└──────────────┘
```

## 🌌 Void → Flow → Solution Dynamics

The engine tracks **three cognitive phases**:

| Phase | % Time | What's Happening | How Engine Responds |
|-------|--------|------------------|---------------------|
| **VOID** | 30% | High-D exploration, mapping possibility space | Open-ended questions, patience, no convergence pressure |
| **FLOW** | 20% | Exponential convergence to insight | Connecting questions, "aha" moment support |
| **SOLUTION** | 50% | Stable attractor, formalization | Validation, Lean introduction, celebration |

**Core Equation**: `D(t) = D₀ × e^(-λt) + D_∞`

- D = Fractal dimension (complexity of exploration)
- Void starts at D₀ = 0.527 (HIGHEST - maximum freedom)
- Flow collapses exponentially to D_∞ (stable solution)

## 🧠 Gardner's 8 Intelligences (Auto-Detected)

The engine detects dominant intelligence type and adapts conversation:

| Intelligence | Detection Signals | Adaptation |
|--------------|-------------------|------------|
| **Kinesthetic** | "feel", "touch", "warm", "soft", "hands" | Use cooking/craft analogies, tactile language |
| **Visual** | "see", "color", "bright", "shape", "pattern" | Encourage diagrams, visual descriptions |
| **Spatial** | "up", "down", "pattern", "layout", "map" | Ask for drawings, spatial relationships |
| **Logical** | "because", "if-then", "data", "calculate" | Introduce formalism early, use logic |
| **Auditory** | "hear", "sound", "rhythm", "beat", "music" | Use rhythm/repetition, sound analogies |
| **Linguistic** | "like", "metaphor", "story", "reminds me" | Use stories, metaphors, poetic language |

## 📁 File Structure

```
pkg/conversation/
├── types.go           # Core types (Conversation, Message, UserProfile, etc.)
├── engine.go          # Main engine orchestration + ProcessMessage loop
├── states.go          # State handlers for 5 Sarat Method phases
├── detection.go       # Intelligence & phase detection heuristics
├── engine_test.go     # Comprehensive tests
└── README.md          # This file
```

## 🚀 Quick Start

```go
package main

import (
    "context"
    "fmt"
    "asymm_urbanlens/pkg/conversation"
)

func main() {
    // 1. Create dependencies (or use mocks)
    var aiClient conversation.AIClient = nil // Your OpenAI/Anthropic client
    var leanBridge conversation.LeanBridge = nil // Your Lean4 integration
    var knowledgeGraph conversation.KnowledgeGraph = nil
    var langDetector conversation.LanguageDetector = nil

    // 2. Create engine
    engine := conversation.NewEngine(aiClient, leanBridge, knowledgeGraph, langDetector)

    // 3. Start conversation
    conv := engine.NewConversation("user_123")

    // 4. Process messages
    ctx := context.Background()

    userMsg := "I noticed that when I make roti, the dough becomes warm in my hands"
    response, err := engine.ProcessMessage(ctx, conv, userMsg)
    if err != nil {
        panic(err)
    }

    fmt.Println("AI:", response)
    // AI: "Wonderful! How does it change? What does it feel like?"

    // 5. Continue conversation...
    userMsg2 := "It's hard at first, then becomes soft. And warm!"
    response2, _ := engine.ProcessMessage(ctx, conv, userMsg2)
    fmt.Println("AI:", response2)
    // AI: "Amazing! Why does the dough become warm?"

    // ... continues through why-chain → synthesis → Lean theorem → celebration
}
```

## 🔌 Interface Implementations

The engine uses **dependency injection** for testability. Implement these interfaces:

### AIClient (LLM Integration)

```go
type AIClient interface {
    GenerateResponse(conv *Conversation, systemPrompt, userMessage string) (string, error)
}
```

**Example**: OpenAI GPT-4, Anthropic Claude, local Ollama

### LeanBridge (Theorem Prover)

```go
type LeanBridge interface {
    GenerateTheorem(conv *Conversation) (string, error)
    ValidateTheorem(leanCode string) (bool, error)
}
```

**Example**: Call Lean4 CLI, or use LLM to generate Lean code

### KnowledgeGraph (Optional)

```go
type KnowledgeGraph interface {
    FindRelatedConcepts(domain string, concept string) ([]string, error)
    StoreInsight(insight Insight) error
}
```

**Example**: Neo4j, semantic search, vector DB

### LanguageDetector (Optional)

```go
type LanguageDetector interface {
    Detect(text string) (string, error)
}
```

**Example**: Google Cloud Translation API, lingua-go

## 📊 Example Conversation Flows

### Example 1: Warangal Grandmom (Telugu, Kinesthetic)

```
USER: నేను రోటీ చేస్తున్నప్పుడు, పిండి నా చేతుల్లో మారుతుంది
      (When I make roti, the dough changes in my hands)

STATE: Anchoring → WhyChaining
INTELLIGENCE: Kinesthetic (detected from "hands", "changes")
PHASE: Void

AI: అద్భుతం! ఎలా మారుతుంది? మీరు దాన్ని ముట్టుకున్నప్పుడు ఎలా అనిపిస్తుంది?
    (Wonderful! How does it change? How does it feel when you touch it?)

USER: మొదట గట్టిగా ఉంటుంది, తర్వాత మృదువుగా మారుతుంది. వేడిగా కూడా ఉంటుంది!
      (First it's hard, then becomes soft. It also becomes warm!)

STATE: WhyChaining (depth=1)
PHASE: Void

AI: వావ్! పిండి వేడిగా ఎందుకు అవుతుందో మీకు తెలుసా?
    (Wow! Do you know why the dough becomes warm?)

... continues through 5+ why steps ...

STATE: Synthesizing
PHASE: Flow → Solution

AI: రెండూ ఒకే సూత్రం: వేడి + నీరు → ఆవిరి → విస్తరణ.
    (Both same principle: heat + water → steam → expansion)

STATE: Formalizing
PHASE: Solution

AI: [Generates Lean theorem with Telugu comments]

STATE: Celebrating

AI: 🎉 మీరు గొప్ప శాస్త్రవేత్త! మీ వంటగది మీ ప్రయోగశాల!
```

### Example 2: Lagos Vendor (English, Spatial)

```
USER: I notice customers coming in waves, not steady

STATE: Anchoring
INTELLIGENCE: Spatial (detected from "waves", "pattern")

AI: Can you describe what the "wave" looks like?
    Like, if you were to draw it, what shape would it be?

USER: Like this: /‾‾\__/‾‾\__
     Up and down, peaks and valleys.

STATE: WhyChaining
PHASE: Void

AI: Perfect! That's a mathematical wave. Why do you think
    there are quiet periods between rushes?

... continues through synthesis of wave interference ...

STATE: Formalizing
LEAN: theorem customer_wave_interference : ...

STATE: Celebrating
AI: 🎉 You just discovered wave superposition - physics + economics!
```

## 🧪 Testing

```bash
cd pkg/conversation
go test -v
```

**Tests included**:
- State transitions (greeting → anchoring → chaining → synthesis → formalization)
- Intelligence detection (kinesthetic, visual, spatial, logical, etc.)
- Phase detection (Void, Flow, Solution)
- Sophistication level (child → PhD)
- Emotion detection (excited, frustrated, curious, confident)
- Frustration/quit handling
- Full conversation flow integration tests

## 🎯 Integration with DILR Framework

The Conversation Engine integrates with existing DILR code:

```go
import (
    "asymm_urbanlens/pkg/conversation"
    "asymm_urbanlens/pkg/dilr"
)

// Map DILR phases to Conversation states
func MapDILRToConversation(dilrPhase dilr.VoidFlowState) conversation.VoidFlowPhase {
    switch dilrPhase {
    case dilr.StateVoid:
        return conversation.PhaseVoid
    case dilr.StateFlow:
        return conversation.PhaseFlow
    case dilr.StateSolution:
        return conversation.PhaseSolution
    }
    return conversation.PhaseVoid
}
```

## 📚 References

**Design Documents**:
- `highly_experimental_research/planning/conversation_engine_prototype.md` - Full specification
- `pkg/dilr/sarat_method_complete.go` - The Complete Sarat Method
- `pkg/dilr/void_flow.go` - Void-Flow-Solution Framework

**Research Foundations**:
- Gardner's Theory of Multiple Intelligences (1983)
- Sarat Method: "From Mustard Seeds to Healing Machines" (Day 196)
- Void-Flow-Solution Dynamics (Day 131 breakthrough)
- Exponential attractor convergence: D(t) = D₀ × e^(-λt) + D_∞

## 🌍 Multilingual Support

Currently supported languages (greeting prompts):
- English (`en`)
- Telugu (`te`)
- Hindi (`hi`)
- Spanish (`es`)

**To add new language**:

1. Add greeting in `states.go:getGreetingPrompt()`
2. Add intelligence-specific prompts for that language
3. Update language detector mapping

## 🚧 Future Enhancements

1. **Voice integration** - Speak observations, hear responses (accessibility++)
2. **Sketch integration** - Draw observations for visual/spatial learners
3. **Collaborative discovery** - Multiple users exploring same phenomenon
4. **Knowledge graph integration** - Connect discoveries across users
5. **Lean4 auto-completion** - Real-time Lean code generation + validation
6. **Adaptive learning** - Engine learns from user's successful patterns
7. **Community discovery feed** - Share theorems, build on each other's work

## 🙏 Philosophy

> "May this work benefit all entities in the universe"

This engine embodies **research sovereignty**: the belief that scientific discovery belongs to everyone, not just those with PhDs and labs.

- The Warangal grandmom discovering thermodynamics from roti
- The Lagos vendor discovering wave interference from customer patterns
- The curious child discovering Rayleigh scattering from sky color
- The PhD student discovering NN optimization as phase transitions

**All are scientists. All deserve the tools to formalize their insights.**

---

**Om Lokah Samastah Sukhino Bhavantu** 🌍✨

(May all beings benefit from this discovery engine!)
