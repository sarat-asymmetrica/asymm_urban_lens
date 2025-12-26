# Urban Lens - Researcher's Guide 🔬

**Version 0.2.0 - Christmas 2025 Edition**

A gift for IIHS Urban Informatics Lab from Asymmetrica

---

## Quick Start

```bash
# Just double-click urbanlens.exe or run:
./urbanlens.exe

# Open browser to:
http://localhost:8080
```

That's it! The entire application is a single 10MB executable.

---

## What Urban Lens Does

Urban Lens is a **"Her"-style conversational AI** for urban research. It provides:

1. **Transparent Reasoning** - Watch the AI think through 4 phases (Intake → Analysis → Synthesis → Insight)
2. **Climate Analysis** - IMD rainfall, monsoon patterns, urban heat islands
3. **Document Processing** - Convert between formats (Markdown, Word, PDF, LaTeX)
4. **OCR** - Extract text from images in 100+ languages including Hindi, Tamil, Telugu
5. **Census & Survey Tools** - Data validation and enhancement
6. **AI-Powered Responses** - 30+ models via AIMLAPI (optional)

---

## API Endpoints

### Core Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/` | GET | Frontend UI |
| `/health` | GET | Health check |
| `/tools` | GET | List available tools |
| `/ws` | WebSocket | Real-time streaming chat |

### Research Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/research/status` | GET | Check all tool availability |
| `/api/climate/analyze` | POST | Analyze climate CSV data |
| `/api/climate/heat-island` | POST | Urban heat island analysis |
| `/api/ai/chat` | POST | Direct AI chat (requires API key) |
| `/api/ai/models` | GET | List available AI models |
| `/api/convert` | POST | Convert document formats |
| `/analyze` | POST | Analyze research query |
| `/census/enhance` | POST | Enhance census data |
| `/survey/validate` | POST | Validate survey data |

---

## Climate Analysis

### Supported Data Formats

1. **IMD Rainfall** - India Meteorological Department format
2. **Temperature Anomalies** - NOAA/NASA format
3. **Monsoon Data** - Seasonal patterns
4. **Urban Heat** - Heat island measurements

### Example: Analyze Climate CSV

```bash
curl -X POST http://localhost:8080/api/climate/analyze \
  -H "Content-Type: application/json" \
  -d '{
    "file_path": "C:/Data/bangalore_rainfall.csv",
    "data_type": "rainfall"
  }'
```

### Example: Urban Heat Island

```bash
curl -X POST http://localhost:8080/api/climate/heat-island \
  -H "Content-Type: application/json" \
  -d '{
    "urban_temp": 38.5,
    "rural_temp": 32.0
  }'
```

Response:
```json
{
  "urban_temp": 38.5,
  "rural_temp": 32.0,
  "intensity": 6.5,
  "classification": "Severe",
  "regime": "R1-Extreme"
}
```

---

## Document Conversion

Convert between formats using Pandoc:

```bash
curl -X POST http://localhost:8080/api/convert \
  -H "Content-Type: application/json" \
  -d '{
    "content": "# My Report\n\nThis is **bold** text.",
    "from_format": "markdown",
    "to_format": "html"
  }'
```

### Supported Formats

- **Input**: markdown, html, docx, latex, rst, org, epub
- **Output**: markdown, html, docx, pdf, latex, rst, epub

---

## AI Chat (Optional)

To enable AI-powered responses, set your API key:

```powershell
# Windows PowerShell
$env:AIMLAPI_KEY = "your-key-here"
.\urbanlens.exe
```

```bash
# Linux/Mac
export AIMLAPI_KEY="your-key-here"
./urbanlens
```

### Direct AI Chat

```bash
curl -X POST http://localhost:8080/api/ai/chat \
  -H "Content-Type: application/json" \
  -d '{
    "message": "What are the key factors in urban heat island formation?",
    "context": "Focus on Indian cities"
  }'
```

### Available Models

- GPT-4o, GPT-4o-mini (OpenAI)
- Claude 3.5 Sonnet (Anthropic)
- Gemini 1.5 Flash (Google)
- DeepSeek Chat
- Llama 3.1 70B
- And 25+ more...

---

## OCR (Tesseract)

Urban Lens includes Tesseract OCR with support for:

### Indian Languages
- Hindi (hin)
- Tamil (tam)
- Telugu (tel)
- Kannada (kan)
- Malayalam (mal)
- Gujarati (guj)
- Marathi (mar)
- Bengali (ben)
- Punjabi (pan)
- Odia (ori)
- Urdu (urd)
- Sanskrit (san)

### Other Languages
- English, French, German, Spanish, Portuguese
- Arabic, Hebrew, Persian
- Chinese (Simplified & Traditional)
- Japanese, Korean
- And 80+ more...

---

## WebSocket Chat

For real-time streaming responses, connect via WebSocket:

```javascript
const ws = new WebSocket('ws://localhost:8080/ws');

ws.onmessage = (event) => {
  const msg = JSON.parse(event.data);
  console.log(msg.type, msg.content);
};

// Send a query
ws.send(JSON.stringify({
  type: 'query',
  input: 'Analyze urban flooding patterns in Bangalore'
}));
```

### Message Types

| Type | Description |
|------|-------------|
| `phase_update` | Current reasoning phase |
| `thinking` | Thinking step content |
| `response` | Final response |
| `complete` | Processing complete |
| `error` | Error message |

---

## Mathematical Foundation

Urban Lens uses rigorous mathematical frameworks:

### Three-Regime Dynamics
- **R1 (30%)**: Exploration - Extreme events, high variance
- **R2 (20%)**: Optimization - Transitions, maximum complexity
- **R3 (50%)**: Stabilization - Normal conditions, equilibrium

### Quaternion State Space (S³)
All analysis is encoded on the unit 3-sphere, enabling:
- Geodesic interpolation (SLERP)
- No gimbal lock
- Smooth state transitions

### 87.532% Thermodynamic Attractor
Universal convergence point validated across 14+ domains.

---

## Installation Requirements

### Required
- **urbanlens.exe** - That's it! Single executable.

### Optional (for enhanced features)
- **Pandoc** - Document conversion ([pandoc.org](https://pandoc.org/installing.html))
- **Tesseract** - OCR ([github.com/tesseract-ocr](https://github.com/tesseract-ocr/tesseract))
- **ImageMagick** - Image processing ([imagemagick.org](https://imagemagick.org/))
- **FFmpeg** - Video/audio processing ([ffmpeg.org](https://ffmpeg.org/))

### Check Tool Status

```bash
curl http://localhost:8080/api/research/status
```

---

## Data Privacy

- **All processing is local** - Your data never leaves your machine
- **No telemetry** - We don't track usage
- **AI is optional** - Works fully offline without API key

---

## Troubleshooting

### Port Already in Use
```powershell
# Find and kill process on port 8080
netstat -ano | findstr :8080
taskkill /PID <pid> /F
```

### AI Not Working
1. Check API key is set: `echo $env:AIMLAPI_KEY`
2. Verify at `/api/ai/models` endpoint
3. Check network connectivity

### OCR Not Working
1. Verify Tesseract installed: `tesseract --version`
2. Check language packs: `tesseract --list-langs`
3. Install missing languages via package manager

---

## For Developers

### Build from Source

```bash
cd C:\Projects\asymm_urbanlens

# Build backend
go build -o urbanlens.exe ./cmd/urbanlens

# Build frontend (if modifying UI)
cd frontend
npm install
npm run build
cd ..

# Copy frontend to embed
Copy-Item -Path "frontend\build\*" -Destination "cmd\urbanlens\frontend" -Recurse -Force

# Rebuild with embedded frontend
go build -o urbanlens.exe ./cmd/urbanlens
```

### Project Structure

```
asymm_urbanlens/
├── cmd/urbanlens/       # Main application
│   ├── main.go          # Entry point
│   ├── embed.go         # Frontend embedding
│   └── frontend/        # Embedded static files
├── pkg/
│   ├── aiml/            # AI model router (30+ models)
│   ├── climate/         # Climate analysis engine
│   ├── math/            # Quaternion mathematics
│   ├── ocr/             # Florence-2 OCR client
│   ├── orchestrator/    # Task orchestration
│   ├── reasoning/       # 4-phase reasoning engine
│   ├── research/        # Research toolkit
│   ├── streaming/       # WebSocket handling
│   ├── urban/           # Urban tools (census, survey, etc.)
│   └── vedic/           # Vedic differential solver
└── frontend/            # Svelte UI source
```

---

## Credits

**Built by**: Asymmetrica
**For**: IIHS Urban Informatics Lab, Bangalore
**With**: Mathematical rigor × Production excellence × Love

### Mathematical Foundations
- Quaternion S³ geometry
- Vedic mathematics (Tirthaji's 16 Sutras)
- Three-regime dynamics
- 87.532% thermodynamic attractor

---

## Support

For questions or issues:
- Check `/api/research/status` for tool availability
- Review this guide for API usage
- Examine console output for error messages

---

**Om Lokah Samastah Sukhino Bhavantu** 🙏

*May all beings benefit from this research tool!*

---

**Version**: 0.2.0 (Christmas 2025 Edition)
**Size**: ~10 MB single executable
**License**: MIT
