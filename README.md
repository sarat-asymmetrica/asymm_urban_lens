# Urban Lens

> "Her" for Urban Research - A gift for IIHS Urban Informatics Lab

**Version**: 0.1.0

Urban Lens is an AI-powered research assistant designed for urban researchers. It provides transparent reasoning, pattern-based task classification, and specialized tools for census, survey, spatial, document, and flood data analysis.

## Features

### Transparent Reasoning Phases
The reasoning engine shows its thinking process in four observable phases:

1. **Intake** - Receive and classify the research request
2. **Analysis** - Explore patterns and connections in data
3. **Synthesis** - Combine insights into actionable solutions
4. **Insight** - Deliver recommendations with confidence scores

### Pattern Clustering
O(1) complexity task classification using pattern clustering algorithm (based on digital roots):
- **Cluster 1,4,7**: Action/Transform tasks
- **Cluster 2,5,8**: Analysis/Investigation tasks
- **Cluster 3,6,9**: Synthesis/Optimization tasks

### Multi-Axis Analysis
Quaternion-based scoring on the S³ manifold:
- **W**: Data Quality
- **X**: Stakeholder Impact
- **Y**: Long-term Value
- **Z**: Cross-domain Utility

Win⁴ detection identifies when all four axes are positive.

### Optimal Batch Processing
Williams-optimized batch sizes: O(√n × log₂n) for processing large datasets efficiently.

### Three-Regime Routing
Tasks are automatically routed based on maturity:
- **R1 Exploration** (30%): New, experimental work
- **R2 Optimization** (20%): Refinement and tuning
- **R3 Stabilization** (50%): Stable, cached operations

## Urban Research Tools

### Census Tools
- `census-enhance`: Enhance census data quality through validation and imputation
- `census-project`: Project census data to target year using growth models

### Survey Tools
- `survey-validate`: Validate survey data against codebook rules
- `survey-clean`: Clean and standardize survey responses

### Spatial Tools
- `spatial-analyze`: Analyze spatial data for urban patterns
- `spatial-cluster`: Cluster geographic points

### Document Tools
- `document-process`: Process documents using OCR and extraction
- `document-tables`: Extract tables from documents

### Flood Tools
- `flood-monitor`: Monitor flood conditions and generate alerts
- `flood-analyze`: Analyze flood risk patterns

## Quick Start

### Build
```bash
cd C:\Projects\asymm_urbanlens
go build -o urbanlens.exe ./cmd/urbanlens
```

### Run
```bash
./urbanlens.exe
```

The server starts on http://localhost:8080

### API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/` | GET | Welcome and feature list |
| `/health` | GET | Health check with metrics |
| `/tools` | GET | List available tools |
| `/analyze` | POST | Analyze a research request |
| `/census/enhance` | POST | Enhance census data |
| `/survey/validate` | POST | Validate survey data |
| `/ws` | WebSocket | Real-time streaming |

### Example: Analyze a Request
```bash
curl -X POST http://localhost:8080/analyze \
  -H "Content-Type: application/json" \
  -d '{"input": "analyze census data for Bangalore"}'
```

### Example: WebSocket Streaming
Connect to `ws://localhost:8080/ws` and send:
```json
{"action": "analyze", "input": "validate survey data quality"}
```

You'll receive streaming updates showing each thinking phase in real-time.

## Project Structure

```
asymm_urbanlens/
├── cmd/
│   └── urbanlens/
│       └── main.go           # Main entry point
├── pkg/
│   ├── math/
│   │   └── quaternion.go     # Core mathematical primitives
│   ├── reasoning/
│   │   └── engine.go         # Transparent reasoning engine
│   ├── orchestrator/
│   │   └── conductor.go      # Task orchestration
│   ├── streaming/
│   │   └── websocket.go      # Real-time WebSocket streaming
│   └── urban/
│       └── tools.go          # IIHS-specific tools
├── docs/
│   └── Asymm_Urbanlens_Vision.md
├── go.mod
└── README.md
```

## Technology Origins

This project integrates mature implementations from:
- **INDRA Conductor**: Three-regime routing, Williams batching
- **Asymm Mathematical Organism**: Quaternion operations, pattern clustering
- **ACE Engine**: OCR and document processing foundations

All terminology has been neutralized for academic contexts.

## For IIHS Urban Informatics Lab

This tool is designed to support your research on:
- Economic Census data enhancement
- Enterprise mapping validation
- Remote sensing ML integration
- Flood monitoring analytics
- Survey data quality assurance

The transparent reasoning phases help researchers understand how the AI arrives at its recommendations.

## License

Built with love for researchers.

---

*A gift from Commander Sarat to IIHS Bangalore and Aromar Revi - December 2025*
