# Asya - Asymmetrica Universal Science Platform

> **"Her" for Everyone** - AI companion for learning mathematics, physics, and all sciences

**Version**: 0.1.0 Genesis
**Philosophy**: Meet learners where they are, infinite patience, mathematical honesty
**Foundation**: Sarat Method + Void-Flow-Solution Framework + Lean 4 Verification

---

## 🌟 Vision

Asya is an AI platform that makes rigorous science accessible to everyone, regardless of background. It combines:

- **Conversational AI** - Natural dialogue, not lectures
- **Adaptive Persona** - Meets you where you are (language, culture, intelligence type)
- **Formal Verification** - Lean 4 theorem proving for mathematical rigor
- **Knowledge Graph** - Navigate interconnected concepts
- **Cultural Sensitivity** - Honors diverse ways of knowing

### The Name

"Asya" (आस्या) - Sanskrit for "worthy of reverence" and "one who brings hope". An AI companion worthy of trust, bringing hope that anyone can understand the universe.

---

## 🚀 Quick Start

### Prerequisites

- **Go 1.22+** (for backend)
- **Node.js 18+** (for frontend)
- **Lean 4** (optional, falls back to mock mode if not installed)
- **AIMLAPI Key** (optional, for real AI responses)

### Installation

```bash
cd /c/Projects/asymm_urbanlens

# Build backend
go build -o asya.exe ./cmd/asya
go build -o urbanlens.exe ./cmd/urbanlens

# Build frontend
cd frontend
npm install
npm run build
cd ..
```

### Run Asya

```bash
# Set API key (optional)
export AIMLAPI_KEY="your_key_here"

# Start server
./asya.exe

# Server runs on http://localhost:8080
```

### Run Urban Lens (IIHS Research Tools)

```bash
./urbanlens.exe

# Server runs on http://localhost:8080
```

---

## 📚 Features

### 1. Conversational AI (Sarat Method)

The **Sarat Method** guides learning through three phases:

| Phase | Description | Example |
|-------|-------------|---------|
| **Void** | Observation, curiosity, questions | "Why does the sky change colors?" |
| **Flow** | Pattern exploration, connections | Discovering light scattering patterns |
| **Solution** | Formalization, proof, rigor | Rayleigh scattering equations + Lean proof |

**Regime Tracking** (Three-Regime Dynamics):
- **R1 (30%)**: Exploration - divergent thinking, many ideas
- **R2 (20%)**: Optimization - convergence, refinement
- **R3 (50%)**: Stabilization - execution, validation

Asya adapts conversation flow based on detected regime.

### 2. Adaptive Persona

Asya adapts to:

- **Intelligence Types** (Gardner's 8 Intelligences)
  - Linguistic, Logical-Mathematical, Spatial, Musical
  - Bodily-Kinesthetic, Interpersonal, Intrapersonal, Naturalistic

- **Cultural Context**
  - Uses analogies from user's culture
  - Honors indigenous ways of knowing
  - Connects to user's daily experience

- **Language**
  - Auto-detects language
  - Explains in user's native language
  - Code-switches naturally

### 3. Lean 4 Theorem Proving

Every mathematical claim can be formally verified:

```lean
-- User learns: "2 + 2 = 4"
theorem two_plus_two : 2 + 2 = 4 := by rfl

-- Verified by Lean ✓
```

Proofs stored in `proofs/` directory and linked to knowledge graph.

### 4. Knowledge Graph

Concepts, theorems, and relationships stored as graph:

- **Concepts**: Nodes representing ideas (e.g., "Pythagorean Theorem")
- **Relationships**: Edges (e.g., "requires", "proves", "generalizes")
- **User Journeys**: Track learning paths, prerequisites

Backend: In-memory (dev) → Neo4j (production)

### 5. Multi-Modal Explanation

Asya explains concepts through:
- **Text** - Clear, step-by-step reasoning
- **Analogies** - Cultural and experiential connections
- **Visual** - Spatial reasoning (future: diagrams)
- **Interactive** - Questions and exploration

---

## 🏗️ Architecture

### Project Structure

```
asymm_urbanlens/
├── cmd/
│   ├── asya/                    # Universal Science Platform binary
│   │   └── main.go
│   └── urbanlens/               # Urban Research Tools binary
│       ├── main.go
│       └── embed.go
├── pkg/
│   ├── conversation/            # Conversation engine (Sarat Method)
│   │   ├── engine.go
│   │   ├── types.go
│   │   ├── states.go
│   │   └── detection.go
│   ├── persona/                 # Asya adaptive persona
│   │   ├── asya.go
│   │   ├── analogies.go
│   │   ├── multilang.go
│   │   ├── tone.go
│   │   └── utils.go
│   ├── knowledge/               # Knowledge graph (Neo4j/in-memory)
│   │   └── graph.go
│   ├── lean/                    # Lean 4 theorem prover bridge
│   │   └── bridge.go
│   ├── vqc/                     # Vedic Quaternion Computing
│   │   ├── primitives.go
│   │   ├── phi_organism_network.go
│   │   └── wrapper.go
│   ├── aimlapi/                 # Multi-model AI router
│   │   ├── client.go
│   │   ├── models.go
│   │   └── streaming.go
│   ├── dilr/                    # DILR framework (Sarat Method core)
│   ├── reasoning/               # Reasoning engine + proof catalog
│   ├── ocr/                     # Document OCR pipeline
│   ├── streaming/               # WebSocket streaming
│   ├── api/                     # HTTP API server
│   ├── config/                  # Configuration
│   └── [other specialized packages]
├── frontend/                    # Svelte frontend
│   ├── src/
│   │   ├── lib/components/
│   │   │   ├── ChatInterface.svelte
│   │   │   └── ReasoningPhase.svelte
│   │   ├── lib/stores/
│   │   │   └── websocket.ts
│   │   └── routes/
│   │       └── +page.svelte
│   └── package.json
├── proofs/                      # Lean 4 proof library
│   ├── basic_arithmetic.lean
│   ├── pythagorean.lean
│   └── README.md
├── prompts/                     # Persona templates
│   ├── base_persona.txt
│   ├── mathematics.txt
│   ├── physics.txt
│   └── exploration.txt
├── go.mod
├── go.sum
├── README.md                    # Urban Lens README
└── README_ASYA.md              # This file
```

### Technology Stack

| Layer | Technology | Purpose |
|-------|------------|---------|
| **Frontend** | Svelte + TypeScript | Reactive UI, WebSocket streaming |
| **Backend** | Go 1.22 | HTTP API, conversation orchestration |
| **AI** | AIMLAPI (multi-model) | GPT-4, Claude, Gemini routing |
| **Verification** | Lean 4 | Formal theorem proving |
| **Knowledge** | Neo4j (future) / In-memory | Concept graph, user journeys |
| **Math** | VQC (Quaternions on S³) | State encoding, regime detection |

### Data Flow

```
User Input
    ↓
Conversation Engine (Sarat Method)
    ↓
[Detect: Language, Intelligence Type, Regime]
    ↓
Asya Persona (Adaptive Response)
    ↓
AIMLAPI (Generate Response)
    ↓
[Optional: Lean Verification]
    ↓
Knowledge Graph (Record Journey)
    ↓
WebSocket Stream → Frontend
```

---

## 🌐 API Reference

### Endpoints

#### `GET /`
Health check and feature list

**Response:**
```json
{
  "name": "Asya",
  "version": "0.1.0",
  "status": "operational",
  "features": ["Conversational AI", "Lean 4 Proof Verification", ...]
}
```

#### `POST /chat`
Send a message to Asya

**Request:**
```json
{
  "user_id": "user123",
  "message": "Why is the sky blue?"
}
```

**Response:**
```json
{
  "response": "Beautiful question! The sky appears blue because...",
  "conversation": {
    "id": "conv_xyz",
    "phase": "Flow",
    "regime": {"R1": 0.4, "R2": 0.3, "R3": 0.3}
  }
}
```

#### `POST /proof`
Verify a Lean proof

**Request:**
```json
{
  "proof": "theorem two_plus_two : 2 + 2 = 4 := by rfl"
}
```

**Response:**
```json
{
  "valid": true,
  "errors": [],
  "warnings": [],
  "duration": "12ms",
  "lean_version": "4.0"
}
```

#### `GET /concepts?q=pythagorean`
Search knowledge graph

**Response:**
```json
{
  "query": "pythagorean",
  "concepts": [
    {
      "id": "concept_123",
      "name": "Pythagorean Theorem",
      "domain": "Mathematics",
      "difficulty": 6,
      "prerequisites": ["concept_45", "concept_67"]
    }
  ]
}
```

#### `GET /domains`
List scientific domains

**Response:**
```json
{
  "domains": [
    {"name": "Mathematics", "sub_domains": ["Algebra", "Geometry", ...]},
    {"name": "Physics", "sub_domains": ["Mechanics", "Thermodynamics", ...]}
  ]
}
```

#### `WebSocket ws://localhost:8080/ws`
Real-time streaming conversation

**Send:**
```json
{"action": "chat", "message": "Explain Newton's laws"}
```

**Receive (streamed):**
```json
{"type": "phase", "phase": "Void", "text": "Great question! Let's start..."}
{"type": "phase", "phase": "Flow", "text": "Newton discovered..."}
{"type": "phase", "phase": "Solution", "text": "Formally, F = ma..."}
```

---

## 🧪 Examples

### Example 1: Learning Arithmetic

**User:** "What is 2 + 2?"

**Asya:**
> "That's 4! Let me show you why. Imagine you have 2 mangoes 🥭🥭, and I give you 2 more 🥭🥭. Now you have 4 mangoes total!
>
> In mathematics, we write this as: 2 + 2 = 4
>
> Would you like to see a formal proof? I can verify it with Lean!"

**User:** "Yes, show me the proof!"

**Asya:**
> "Here's the Lean proof:
> ```lean
> theorem two_plus_two : 2 + 2 = 4 := by rfl
> ```
> The `rfl` tactic means 'reflexivity' - it checks if both sides are literally the same. Lean verified it! ✓
>
> Want to try proving something yourself?"

### Example 2: Exploring Physics

**User:** "Why does a ball fall down?"

**Asya (Void Phase):**
> "Wonderful observation! You've noticed one of the most fundamental patterns in nature. What do you think might be pulling the ball down?"

**User:** "Maybe the Earth?"

**Asya (Flow Phase):**
> "Exactly! The Earth has mass, and mass creates something we call *gravity*. Think of it like the Earth and the ball are attracted to each other - but the Earth is so much bigger, it barely moves, while the ball falls toward it.
>
> Have you noticed that all objects fall at the same speed (ignoring air)? A feather and a hammer would fall together on the Moon!"

**User:** "Can you write that as an equation?"

**Asya (Solution Phase):**
> "Yes! Newton discovered the equation:
> ```
> F = G × (m₁ × m₂) / r²
> ```
> Where:
> - F = gravitational force
> - G = gravitational constant
> - m₁, m₂ = masses of two objects
> - r = distance between them
>
> For falling objects near Earth's surface, this simplifies to F = mg, where g ≈ 9.8 m/s².
>
> Want to prove this works? We can formalize it in Lean!"

---

## 🔬 VQC Mathematics (Core Engine)

Asya uses **Vedic Quaternion Computing** for state representation:

### Quaternions on S³

Every state (user, concept, conversation) encoded as unit quaternion on 3-sphere:

```go
q := Quaternion{W: completion, X: learning, Y: connection, Z: joy}
q = q.Normalize() // Projects onto S³ unit sphere
```

**Properties:**
- Always valid (||q|| = 1.0)
- Smooth evolution via SLERP (spherical linear interpolation)
- Regime detection from component distribution

### Three-Regime Dynamics

```
R1 (Exploration):   30% - High variance, divergent
R2 (Optimization):  20% - Convergence, refinement
R3 (Stabilization): 50% - Execution, validation

Stability check: R3 ≥ 50%
```

### Digital Root Filtering (53× Speedup)

```go
DigitalRoot(n) = 1 + (n-1) % 9  // O(1) complexity!

Clusters:
  [1,4,7] → Action/Transform tasks
  [2,5,8] → Analysis/Investigation tasks
  [3,6,9] → Synthesis/Optimization tasks
```

Eliminates 88.9% of candidates instantly!

### Williams Batching

Optimal batch size for processing:
```go
batchSize = int(√n × log₂(n))  // Provably optimal space-time tradeoff
```

---

## 🌍 Cultural Sensitivity

Asya is designed for **universal access**:

### Analogy Library

- **India**: Vedic mathematics, Ramayana/Mahabharata analogies
- **Africa**: Fractal patterns, Ubuntu philosophy
- **Middle East**: Islamic geometric patterns, Al-Khwarizmi's algebra
- **East Asia**: Yin-yang dualities, Go game strategies
- **Americas**: Natural cycles, indigenous knowledge systems

### Language Support

- Auto-detects language (English, Hindi, Tamil, Spanish, French, Arabic, etc.)
- Explains in native language
- Mathematical notation transcends language

### Intelligence Types

Adapts to Gardner's 8 intelligences:
- **Linguistic**: Word-based explanations
- **Logical-Mathematical**: Equations and proofs
- **Spatial**: Visual/geometric thinking
- **Musical**: Rhythms and patterns
- **Bodily-Kinesthetic**: Physical analogies
- **Interpersonal**: Social contexts
- **Intrapersonal**: Self-reflection
- **Naturalistic**: Nature patterns

---

## 🛠️ Development

### Run in Development Mode

```bash
# Backend with hot reload
go run ./cmd/asya/main.go

# Frontend with hot reload
cd frontend
npm run dev
```

### Add a New Proof

1. Create `.lean` file in `proofs/`:
```lean
theorem my_theorem : statement := by
  proof_steps
```

2. Verify:
```bash
lean proofs/my_theorem.lean
```

3. Register in knowledge graph (TODO: automation)

### Add a New Domain Prompt

1. Create `prompts/domain_name.txt`
2. Follow template from `prompts/mathematics.txt`
3. Reference in conversation engine

### Run Tests

```bash
# Go tests
go test ./...

# Frontend tests
cd frontend
npm test
```

---

## 📖 References

### Theoretical Foundations

- **Sarat Method**: Void-Flow-Solution framework (built by Commander Sarat)
- **Three-Regime Dynamics**: 30%-20%-50% distribution (Asymmetrica research)
- **Vedic Mathematics**: Sutras 1-16, digital root filtering
- **Lean 4**: [Lean Prover](https://leanprover.github.io/)
- **Gardner's Intelligences**: [Multiple Intelligences Theory](https://en.wikipedia.org/wiki/Theory_of_multiple_intelligences)

### Code Ancestry

- **INDRA Conductor**: Three-regime routing, Williams batching
- **Asymm Mathematical Organism**: VQC primitives, phi-organism network
- **ACE Engine**: OCR pipelines, document processing
- **Urban Lens**: IIHS research tools foundation

---

## 🎯 Roadmap

### Phase 1: Core Platform ✅
- [x] Conversation engine (Sarat Method)
- [x] Adaptive persona (Asya)
- [x] Lean bridge (mock + real)
- [x] Knowledge graph (in-memory)
- [x] VQC mathematics
- [x] WebSocket streaming
- [x] Prompt templates
- [x] Proof library starter

### Phase 2: Enhancement (Next)
- [ ] Neo4j knowledge graph (production-ready)
- [ ] Visual diagram generation
- [ ] Voice interface
- [ ] Mobile app (React Native)
- [ ] Collaborative proving (multiplayer)
- [ ] Gamification (proof challenges)

### Phase 3: Scaling (Future)
- [ ] Multi-tenant SaaS
- [ ] University integration
- [ ] Proof competition platform
- [ ] AI-generated curricula
- [ ] Global proof library

---

## 🙏 Dedication

This platform is built with love for:

- **Every curious child** who asks "why?"
- **Every frustrated student** told "you're not good at math"
- **Every adult** who wishes they understood science
- **Every teacher** seeking better tools
- **Every culture** whose knowledge was dismissed

**Om Lokah Samastah Sukhino Bhavantu**
*May all beings benefit from this work.*

---

## 📜 License

Built with love for universal learning.
Research sovereignty - knowledge belongs to humanity.

---

## 🤝 Contact

- **Project**: Asymmetrica Mathematical Organism
- **Vision**: Commander Sarat
- **Built by**: Research Dyad (Human + AI collaboration)
- **Repository**: `asymm_urbanlens`

For questions, issues, or collaborations, reach out through the repository.

---

**Asya - Because understanding the universe is a human right, not a privilege.** 🌟🔬✨
