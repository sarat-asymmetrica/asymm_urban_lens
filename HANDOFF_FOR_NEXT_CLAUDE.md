# HANDOFF FOR NEXT CLAUDE SESSION

**Date**: December 23, 2025
**Project**: Urban Lens - "Her" for Urban Research
**Status**: Backend Complete, Frontend Pending
**For**: IIHS Urban Informatics Lab (Commander's gift to Aromar Revi)

---

## QUICK CONTEXT

Commander is building a **gift for IIHS Bangalore** (Indian Institute for Human Settlements) where he worked 2013-2015. Aromar Revi (founder, UN SDSN Co-Chair, IPCC author) mentored him. This is a "love letter to researchers."

**Key Requirements**:
1. **Neutral academic language** (no spiritual/Vedic terminology in code)
2. **"Her"-style conversational AI** with transparent reasoning
3. **All the tech** from ACE_Engine and asymm_all_math repos
4. **Immediate practical value** for urban researchers

---

## WHAT'S DONE ✅

### Go Backend (1,730 LOC) - BUILDS AND RUNS

```
C:\Projects\asymm_urbanlens\
├── cmd/urbanlens/main.go           # HTTP server, WebSocket, routes
├── pkg/
│   ├── math/quaternion.go          # Quaternion, SLERP, Pattern Clustering, Balanced Score
│   ├── reasoning/engine.go         # 4-phase reasoning (Intake→Analysis→Synthesis→Insight)
│   ├── orchestrator/conductor.go   # Three-regime routing, Williams batching, caching
│   ├── streaming/websocket.go      # Real-time WebSocket for "Her" experience
│   └── urban/tools.go              # IIHS tools (Census, Survey, Spatial, Document, Flood)
├── go.mod
├── go.sum
├── urbanlens.exe                   # BUILT AND READY
└── README.md
```

**To verify**:
```bash
cd C:\Projects\asymm_urbanlens
.\urbanlens.exe
# Server starts on http://localhost:8080
```

### Language Sanitization Applied

| Original (Spiritual) | Urban Lens (Neutral) |
|---------------------|---------------------|
| Jagrat | Intake |
| Svapna | Analysis |
| Sushupti | Synthesis |
| Turiya | Insight |
| Digital Root (Vedic) | Pattern Clustering |
| Harmonic Mean | Balanced Score |
| VOID→FLOW→SOLUTION | Explore→Evaluate→Recommend |

---

## WHAT'S PENDING ⏳

### 1. Port OCR Engine with Florence-2

**Source**: `C:\Projects\ACE_Engine\pkg\ocr\`
- 28,638 LOC of production OCR code
- Florence-2 integration (40x faster, 60x cheaper)
- Trinity consensus validation
- GPU preprocessing (9M ops/sec)

**Target**: `C:\Projects\asymm_urbanlens\pkg\ocr\`

**Key files to port**:
```
C:\Projects\ACE_Engine\pkg\ocr\
├── engine.go              # Main ACE OCR engine
├── florence2_client.go    # Florence-2 Modal endpoint
├── trinity_optimizer.go   # Consensus validation
├── gpu_levelzero.go       # GPU preprocessing
├── babel_mapper.go        # Language detection
└── orchestrator\          # OCR orchestration
```

**Integration point in Urban Lens**:
- Add to `pkg/urban/tools.go` DocumentProcessor
- Wire to `handleDocumentProcess()` in main.go

### 2. Port Unified Interface (Svelte)

**Source**: `C:\Projects\asymm_all_math\asymm_mathematical_organism\design_system\showcase\asymmetrica_unified_interface.html`
- 1,185 LOC HTML with embedded CSS/JS
- φ breathing (8s cycle)
- Fibonacci spacing (8, 13, 21, 34, 55, 89, 144px)
- 87.532% content width
- Paper texture + wax seal aesthetic
- Three modes (Enterprise, Personal, Government) → Add "Research" mode for IIHS

**Target**: `C:\Projects\asymm_urbanlens\frontend\`

**Suggested structure**:
```
C:\Projects\asymm_urbanlens\frontend\
├── src/
│   ├── App.svelte
│   ├── lib/
│   │   ├── components/
│   │   │   ├── ChatInterface.svelte
│   │   │   ├── ThinkingPhases.svelte      # Shows Intake→Analysis→Synthesis→Insight
│   │   │   ├── ToolSelector.svelte
│   │   │   └── ResultDisplay.svelte
│   │   └── stores/
│   │       └── websocket.ts               # WebSocket connection to backend
│   └── styles/
│       └── phi-breathing.css              # φ animations
├── package.json
└── vite.config.js
```

**Key CSS from source** (already in the HTML file):
```css
:root {
    --phi: 1.618033988749;
    --fib-1: 8px; --fib-2: 13px; --fib-3: 21px; --fib-4: 34px;
    --breath-cycle: 8s;
    --breath-inhale: 2.472s;  /* 8s × 0.309 (φ⁻²) */
    --content-width: 87.532%;
}
```

### 3. Wire Florence-2 to Document Tool

After porting OCR, update `pkg/urban/tools.go`:

```go
// In DocumentProcessor.Process()
// Replace stub with real Florence-2 call
func (d *DocumentProcessor) Process(filename string, content []byte) (*DocumentResult, error) {
    // Call Florence-2 endpoint
    result, err := d.florence2Client.Extract(content)
    // ... process result
}
```

---

## SOURCE REPOS TO REFERENCE

### ACE_Engine (`C:\Projects\ACE_Engine\`)

**Most mature for Urban Lens**:
- `pkg/ocr/` - Florence-2, Trinity, GPU preprocessing
- `indra/pkg/core/conductor.go` - Already ported (orchestrator)
- `indra/pkg/asymmetrica/unified_router.go` - Task routing patterns

### asymm_all_math (`C:\Projects\asymm_all_math\`)

**Most mature for Urban Lens**:
- `asymm_mathematical_organism/design_system/showcase/` - Unified interface
- `asymm_mathematical_organism/00_NUCLEUS/primitives.go` - Quaternion ops (ported)
- `asymm_mathematical_organism/03_ENGINES/vqc/` - VQC indexer (optional)

### asymm_ananta (`C:\Projects\asymm_ananta\`)

**Already ported from here**:
- `backend/internal/reasoning/classifier.go` → `pkg/reasoning/engine.go`
- `backend/internal/vedic/digital_root.go` → `pkg/math/quaternion.go` (as PatternCluster)

---

## IIHS URBAN INFORMATICS LAB CONTEXT

**What they work on** (from research):
- Economic Census data enhancement
- Bangalore Enterprise Mapping
- High-Resolution Population estimation
- Remote sensing ML
- India Flood Monitoring (Microsoft Planetary Computer)
- Survey data analysis

**Tools they use**: Excel, Stata, R, Tableau, QGIS

**What Urban Lens provides**:
- Census enhancement with validation
- Survey validation against codebook rules
- Spatial clustering analysis
- Document OCR (especially for Indian languages)
- Flood monitoring alerts

---

## ARCHITECTURE DIAGRAM

```
┌─────────────────────────────────────────────────────────────────────┐
│                         URBAN LENS                                   │
│                   "Her" for Urban Research                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                       │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │              FRONTEND (Svelte) [PENDING]                     │    │
│  │  • Chat interface with streaming                             │    │
│  │  • Thinking phases visualization                             │    │
│  │  • φ breathing, Fibonacci spacing                            │    │
│  │  • "Research" mode for IIHS                                  │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                              │ WebSocket                             │
│                              ▼                                       │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │              BACKEND (Go) [DONE ✅]                          │    │
│  │                                                               │    │
│  │  ┌──────────────┐ ┌──────────────┐ ┌──────────────────────┐ │    │
│  │  │  Reasoning   │ │ Orchestrator │ │     Streaming        │ │    │
│  │  │   Engine     │ │  (Conductor) │ │    (WebSocket)       │ │    │
│  │  │              │ │              │ │                      │ │    │
│  │  │ Intake       │ │ R1 Explore   │ │ Phase updates        │ │    │
│  │  │ Analysis     │ │ R2 Optimize  │ │ Progress stream      │ │    │
│  │  │ Synthesis    │ │ R3 Stabilize │ │ Result delivery      │ │    │
│  │  │ Insight      │ │ Williams     │ │                      │ │    │
│  │  └──────────────┘ └──────────────┘ └──────────────────────┘ │    │
│  │                                                               │    │
│  │  ┌──────────────────────────────────────────────────────────┐│    │
│  │  │              URBAN TOOLS [DONE ✅]                        ││    │
│  │  │  Census │ Survey │ Spatial │ Document │ Flood            ││    │
│  │  └──────────────────────────────────────────────────────────┘│    │
│  │                                                               │    │
│  │  ┌──────────────────────────────────────────────────────────┐│    │
│  │  │              OCR ENGINE [PENDING]                         ││    │
│  │  │  Florence-2 │ Trinity │ GPU Preprocessing                ││    │
│  │  └──────────────────────────────────────────────────────────┘│    │
│  │                                                               │    │
│  │  ┌──────────────────────────────────────────────────────────┐│    │
│  │  │              MATH PRIMITIVES [DONE ✅]                    ││    │
│  │  │  Quaternion │ SLERP │ Pattern Clustering │ Balanced Score││    │
│  │  └──────────────────────────────────────────────────────────┘│    │
│  └─────────────────────────────────────────────────────────────┘    │
│                                                                       │
└─────────────────────────────────────────────────────────────────────┘
```

---

## SUGGESTED NEXT STEPS

### Option A: Frontend First (Visual Impact)
1. Create `frontend/` with Svelte + Vite
2. Port the unified interface HTML → Svelte components
3. Add "Research" mode (blue/academic theme)
4. Wire WebSocket to backend

### Option B: OCR First (Functionality)
1. Port Florence-2 client from ACE_Engine
2. Add to DocumentProcessor in urban/tools.go
3. Test with sample Indian documents
4. Wire to main.go routes

### Option C: Full Integration
1. Do both in parallel with subagents
2. One agent on frontend
3. One agent on OCR

---

## CRITICAL FILES TO READ

Before starting, read these for context:

1. **Vision**: `C:\Projects\asymm_urbanlens\docs\Asymm_Urbanlens_Vision.md`
2. **Main entry**: `C:\Projects\asymm_urbanlens\cmd\urbanlens\main.go`
3. **Reasoning engine**: `C:\Projects\asymm_urbanlens\pkg\reasoning\engine.go`
4. **Urban tools**: `C:\Projects\asymm_urbanlens\pkg\urban\tools.go`
5. **Source UI**: `C:\Projects\asymm_all_math\asymm_mathematical_organism\design_system\showcase\asymmetrica_unified_interface.html`
6. **Source OCR**: `C:\Projects\ACE_Engine\pkg\ocr\engine.go`

---

## CLAUDE.md REMINDERS

From `C:\Projects\ACE_Engine\CLAUDE.md`:
- NO TIME ESTIMATES (say "Let's build it" and execute)
- NEVER present incomplete as finished
- Use emojis freely (Commander's request)
- "Have fun broseph!" is the vibe

---

## TEST THE CURRENT BUILD

```bash
# Terminal 1: Start server
cd C:\Projects\asymm_urbanlens
.\urbanlens.exe

# Terminal 2: Test endpoints
curl http://localhost:8080/
curl http://localhost:8080/health
curl http://localhost:8080/tools
curl -X POST http://localhost:8080/analyze -H "Content-Type: application/json" -d "{\"input\":\"analyze census data for Bangalore\"}"
```

---

**Good luck, next Claude! Build something beautiful for IIHS! 🚀**

*Om Lokah Samastah Sukhino Bhavantu*
*May all beings benefit from this work.*
