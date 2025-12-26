# Urban Lens - Deployment Guide

## Quick Start

### Prerequisites

**Required:**
- Go 1.22+
- Git

**Recommended (for full functionality):**
```powershell
# Install via winget (Windows)
winget install JohnMacFarlane.Pandoc    # Document conversion
winget install Gyan.FFmpeg               # Audio/video processing
winget install UB-Mannheim.TesseractOCR  # Local OCR
winget install ImageMagick.ImageMagick   # Image processing
```

### Build & Run

```powershell
# Clone
git clone https://github.com/sarat-asymmetrica/asymm_urban_lens.git
cd asymm_urban_lens

# Build
go build -o urbanlens.exe ./cmd/urbanlens

# Run
./urbanlens.exe
```

Server starts at `http://localhost:8080`

---

## Configuration

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `AIMLAPI_KEY` | AIMLAPI key for AI features | (none - mock mode) |
| `PORT` | Server port | 8080 |

### Setting AIMLAPI Key

```powershell
# Windows (permanent)
[System.Environment]::SetEnvironmentVariable("AIMLAPI_KEY", "your-key", "User")

# Or per-session
$env:AIMLAPI_KEY = "your-key"
./urbanlens.exe
```

---

## API Endpoints

### Core
| Endpoint | Method | Description |
|----------|--------|-------------|
| `/health` | GET | System health (add `?quick=true` for minimal) |
| `/tools` | GET | List available tools |
| `/analyze` | POST | Analyze a research request |
| `/ws` | WS | WebSocket for streaming |

### Document Pipeline
| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/pipeline/status` | GET | Check Pandoc/FFmpeg availability |
| `/api/pipeline/process` | POST | Process documents/media |

### Climate
| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/climate/analyze` | POST | Analyze climate data |
| `/api/climate/heat-island` | POST | Urban heat island analysis |

### DILR (Problem Solving)
| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/dilr/analyze` | POST | Analyze DILR problem |
| `/api/dilr/sarat-method` | GET | Get Sarat Method guide |
| `/api/dilr/void-flow` | GET | Void-Flow-Solution framework |

### Cultural Mathematics
| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/cultural/katapayadi` | POST | Number ↔ Sanskrit encoding |
| `/api/cultural/digital-root` | POST | Vedic digital root |
| `/api/cultural/mandala` | POST | Generate mandala |

---

## Docker Deployment (Future)

```dockerfile
FROM golang:1.22-alpine AS builder
WORKDIR /app
COPY . .
RUN go build -o urbanlens ./cmd/urbanlens

FROM alpine:latest
RUN apk add --no-cache pandoc ffmpeg tesseract-ocr
COPY --from=builder /app/urbanlens /usr/local/bin/
EXPOSE 8080
CMD ["urbanlens"]
```

---

## Health Check

```bash
# Quick check (for load balancers)
curl http://localhost:8080/health?quick=true

# Full status with component health
curl http://localhost:8080/health
```

Response includes:
- System status (healthy/degraded)
- Component availability (pandoc, ffmpeg, tesseract)
- Go runtime metrics
- Uptime

---

## Troubleshooting

### "Tool not available" errors

Install missing tools:
```powershell
winget install JohnMacFarlane.Pandoc
winget install Gyan.FFmpeg
```

Restart your terminal to refresh PATH.

### AI features returning mock responses

Set your AIMLAPI key:
```powershell
$env:AIMLAPI_KEY = "your-key"
```

### Port already in use

```powershell
# Find process using port 8080
netstat -ano | findstr :8080

# Kill it
taskkill /PID <pid> /F
```

---

## Production Checklist

- [ ] Set `AIMLAPI_KEY` environment variable
- [ ] Install Pandoc, FFmpeg, Tesseract
- [ ] Configure reverse proxy (nginx/caddy)
- [ ] Set up SSL/TLS
- [ ] Configure logging
- [ ] Set up monitoring (health endpoint)
- [ ] Configure backup for any persistent data

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Urban Lens Server                     │
├─────────────────────────────────────────────────────────┤
│  HTTP API (REST + WebSocket)                            │
├─────────────────────────────────────────────────────────┤
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐       │
│  │Reasoning│ │ Climate │ │  DILR   │ │Cultural │       │
│  │ Engine  │ │Analyzer │ │Framework│ │  Math   │       │
│  └─────────┘ └─────────┘ └─────────┘ └─────────┘       │
├─────────────────────────────────────────────────────────┤
│  ┌─────────────────────────────────────────────────┐   │
│  │           Document Pipeline                      │   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐         │   │
│  │  │ Pandoc  │  │ FFmpeg  │  │Tesseract│         │   │
│  │  └─────────┘  └─────────┘  └─────────┘         │   │
│  └─────────────────────────────────────────────────┘   │
├─────────────────────────────────────────────────────────┤
│  ┌─────────────────────────────────────────────────┐   │
│  │              AI Router (AIMLAPI)                 │   │
│  │  Claude │ GPT-4 │ Mistral │ Llama │ Gemini     │   │
│  └─────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
```

---

*Built with love for IIHS Urban Informatics Lab* 🏙️
