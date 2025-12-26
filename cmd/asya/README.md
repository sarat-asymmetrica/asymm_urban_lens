# ASYA - The Conversation Engine Server

**आस्या** - "Her" for Universal Science Discovery

## Overview

ASYA implements the **Sarat Method + Void-Flow-Solution Framework** to guide anyone from observation → formalized theorem. Built on the conversation engine architecture with WebSocket streaming for real-time interaction.

## Features

- ✨ **Multi-language support** - Auto-detects user language
- 🧠 **Intelligence adaptation** - Adapts to Gardner's 8 intelligence types
- 🌊 **Void-Flow-Solution phases** - Three-regime dynamics (30%, 20%, 50%)
- 🔄 **Real-time WebSocket streaming** - Token-by-token responses
- 🤖 **AIMLAPI integration** - 30+ AI models available
- 📐 **Lean theorem generation** - Formalizes discoveries into proofs
- 🎯 **State-aware conversation** - Greeting → Anchoring → Why-chaining → Synthesizing → Formalizing → Celebrating

## Quick Start

### 1. Configuration

Copy `.env.example` to `.env`:

```bash
cp .env.example .env
```

Edit `.env` and set your AIMLAPI key:

```
AIMLAPI_KEY=your_key_here
```

### 2. Build

```bash
go build
```

### 3. Run

```bash
./asya
```

Server starts on `http://localhost:8080`

## API Endpoints

### REST API

| Method | Endpoint | Description |
|--------|----------|-------------|
| GET | `/` | API info |
| GET | `/health` | Health check |
| POST | `/api/sessions` | Create new conversation |
| POST | `/api/sessions/:id/messages` | Send message |
| GET | `/api/sessions/:id` | Get conversation state |
| POST | `/api/visualize` | Request visualization |

### WebSocket

Connect to `/ws` for streaming:

```javascript
const ws = new WebSocket('ws://localhost:8080/ws');

// Create session
ws.send(JSON.stringify({
  action: 'create_session',
  user_id: 'optional'
}));

// Send message
ws.send(JSON.stringify({
  action: 'send_message',
  session_id: 'session-uuid',
  message: 'I noticed water boils faster at high altitudes...'
}));

// Request hint
ws.send(JSON.stringify({
  action: 'request_hint',
  session_id: 'session-uuid'
}));
```

### WebSocket Events

| Type | Description |
|------|-------------|
| `welcome` | Connection established |
| `token` | Streaming response token |
| `phase_change` | Void-Flow-Solution phase changed |
| `state_change` | Conversation state changed |
| `entity` | Entity detected in conversation |
| `insight` | Insight discovered |
| `discovery` | Major discovery made |
| `complete` | Response complete |
| `error` | Error occurred |

## Conversation States

1. **GREETING** - Initial contact, language detection
2. **ANCHORING** - Get concrete, sensory observation
3. **WHY_CHAINING** - Ask "why" 5+ times, go deep
4. **SYNTHESIZING** - Connect to existing knowledge
5. **FORMALIZING** - Introduce Lean, create theorem
6. **CELEBRATING** - Honor the discovery

## Void-Flow-Solution Phases

- **VOID (30%)** - High-D exploration, divergent thinking
- **FLOW (20%)** - Exponential convergence, "aha" moments
- **SOLUTION (50%)** - Stable attractor, confident understanding

## Intelligence Types (Gardner's 8)

The system adapts conversation style based on detected intelligence:

- KINESTHETIC - Body, touch, movement
- VISUAL - Sight, color, spatial
- AUDITORY - Sound, rhythm, music
- SPATIAL - Patterns, maps, shapes
- LOGICAL - Numbers, systems, logic
- LINGUISTIC - Words, stories, metaphor
- SOCIAL - People, empathy, group dynamics
- NATURALIST - Nature, patterns, classification

## Architecture

```
cmd/asya/
  main.go                 # Entry point, HTTP server

pkg/api/
  server.go               # Server struct, session management
  websocket.go            # WebSocket streaming
  middleware.go           # CORS, logging, recovery, rate limiting

pkg/config/
  config.go               # Environment configuration

pkg/conversation/
  engine.go               # Main conversation orchestrator
  types.go                # Core types and interfaces
  states.go               # State handlers (greeting, anchoring, etc.)
```

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `PORT` | 8080 | Server port |
| `AIMLAPI_KEY` | - | AIMLAPI key for AI responses |
| `ALLOWED_ORIGINS` | localhost:5173,3000 | CORS allowed origins |
| `DEBUG` | false | Enable debug logging |
| `MAX_SESSIONS` | 1000 | Maximum concurrent sessions |
| `SESSION_TIMEOUT` | 60 | Session timeout (minutes) |
| `RATE_LIMIT_ENABLED` | true | Enable rate limiting |
| `RATE_LIMIT_REQUESTS` | 100 | Max requests per window |
| `RATE_LIMIT_WINDOW` | 1 | Rate limit window (minutes) |

## Development

### Run in debug mode

```bash
DEBUG=true ./asya
```

### Test API

```bash
# Health check
curl http://localhost:8080/health

# Create session
curl -X POST http://localhost:8080/api/sessions

# Send message
curl -X POST http://localhost:8080/api/sessions/YOUR_SESSION_ID/messages \
  -H "Content-Type: application/json" \
  -d '{"message": "Why does ice float on water?"}'
```

## Production Deployment

### With systemd

Create `/etc/systemd/system/asya.service`:

```ini
[Unit]
Description=ASYA Conversation Engine
After=network.target

[Service]
Type=simple
User=asya
WorkingDirectory=/opt/asya
ExecStart=/opt/asya/asya
Restart=always
Environment="PORT=8080"
Environment="AIMLAPI_KEY=your_key"

[Install]
WantedBy=multi-user.target
```

Enable and start:

```bash
sudo systemctl enable asya
sudo systemctl start asya
```

### With Docker

```dockerfile
FROM golang:1.22-alpine AS builder
WORKDIR /app
COPY . .
RUN go build -o asya ./cmd/asya

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/
COPY --from=builder /app/asya .
EXPOSE 8080
CMD ["./asya"]
```

Build and run:

```bash
docker build -t asya .
docker run -p 8080:8080 -e AIMLAPI_KEY=your_key asya
```

## Philosophy

**From Observation → Formalized Theorem**

ASYA embodies the principle that science belongs to everyone. Every curious observation - from a child noticing bubbles to a street vendor understanding fermentation - can lead to formalized scientific understanding.

The Sarat Method + Void-Flow-Solution framework provides the scaffolding for this journey, adapting to each person's unique way of thinking and learning.

## Credits

Built with love for curious minds everywhere.

**Om Lokah Samastah Sukhino Bhavantu**
*May all beings benefit from these discoveries!*

---

**Version:** 0.1.0 (Genesis Edition)
**License:** MIT
**Contact:** [Add your contact info]
