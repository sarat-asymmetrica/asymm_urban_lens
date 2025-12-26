# Urban Lens Frontend

**"Her"-style conversational AI interface for urban research**

## 🎯 Overview

This is the Svelte frontend for Urban Lens - a gift for IIHS Urban Informatics Lab. It provides an elegant, research-appropriate interface with:

- **Streaming conversation** with "Her"-style responsiveness
- **Transparent reasoning** - shows 4-phase thinking process (Intake → Analysis → Synthesis → Insight)
- **Wabi-Sabi aesthetic** - paper texture, Fibonacci spacing, φ breathing
- **Real-time WebSocket** connection to Go backend

## 🏗️ Structure

```
frontend/
├── src/
│   ├── app.css                         # Global styles (Wabi-Sabi design)
│   ├── lib/
│   │   ├── components/
│   │   │   ├── ChatInterface.svelte    # Main conversation UI
│   │   │   └── ReasoningPhase.svelte   # 4-phase thinking visualizer
│   │   └── stores/
│   │       └── websocket.ts            # WebSocket state management
│   └── routes/
│       ├── +layout.svelte              # Global layout
│       └── +page.svelte                # Main page
├── package.json
└── vite.config.ts
```

## 🚀 Quick Start

### 1. Start Backend (in separate terminal)

```bash
cd /c/Projects/asymm_urbanlens
./urbanlens.exe
# Server runs on http://localhost:8080
```

### 2. Start Frontend

```bash
cd /c/Projects/asymm_urbanlens/frontend
npm run dev
# Frontend runs on http://localhost:5173
```

### 3. Open Browser

Navigate to: **http://localhost:5173**

The frontend will automatically connect to the WebSocket at `ws://localhost:8080/ws`

## 🎨 Design System

### Colors (Logo-Derived)

- **Paper**: `#F5F0E6` - Background
- **Gold**: `#C5A059` - Primary accent
- **Ink**: `#3D3835` - Text
- **Forest**: `#4A6B52` - Success/Active
- **Seal**: `#8B5A3C` - Warm accent

### Typography

- **Display**: Cinzel (headings)
- **Body**: Lora (conversation)
- **UI**: Outfit (labels, buttons)

### Spacing (Fibonacci)

- 8px, 13px, 21px, 34px, 55px, 89px, 144px

### Timing (Fibonacci ms)

- Instant: 89ms
- Fast: 144ms
- Normal: 233ms
- Slow: 377ms

## 🔌 WebSocket Protocol

### Client → Server

```json
{
  "type": "query",
  "input": "Your question here",
  "timestamp": "2025-12-24T12:15:00Z"
}
```

### Server → Client

```json
{
  "type": "phase_update",
  "phase": "intake" | "analysis" | "synthesis" | "insight" | "complete"
}
```

```json
{
  "type": "thinking" | "response",
  "content": "Streaming text...",
  "timestamp": "2025-12-24T12:15:01Z"
}
```

```json
{
  "type": "complete",
  "phase": "insight"
}
```

## 📦 Components

### ChatInterface.svelte

Main conversation UI with:
- Message history
- Streaming text with cursor animation
- Auto-scroll to latest message
- Input with auto-resize
- Connection status indicator

### ReasoningPhase.svelte

Visual indicator showing 4 phases:
1. **Intake** - Understanding your question
2. **Analysis** - Examining data and patterns
3. **Synthesis** - Connecting insights
4. **Insight** - Formulating response

Includes:
- Progress circles with checkmarks
- Active phase highlighting
- Animated connectors
- Thinking pulse indicator

## 🛠️ Development

### Build for Production

```bash
npm run build
```

### Preview Production Build

```bash
npm run preview
```

### Type Checking

```bash
npm run check
```

## 🎯 Features

✅ **Real-time streaming** - Text appears as it's generated
✅ **Transparent reasoning** - See AI thinking process
✅ **Auto-reconnect** - WebSocket reconnects if disconnected
✅ **Keyboard shortcuts** - Enter to send, Shift+Enter for newline
✅ **Auto-scroll** - Always shows latest message
✅ **Example queries** - Click to try common questions
✅ **Clear conversation** - Reset anytime
✅ **Connection status** - Visual indicator of WebSocket state

## 🌟 IIHS Context

Built as a gift for IIHS Urban Informatics Lab (Bangalore), where Commander worked 2013-2015.

**Designed for researchers working on:**
- Economic Census enhancement
- Bangalore Enterprise Mapping
- Population estimation
- Remote sensing ML
- Flood monitoring
- Survey validation

**Language:** Neutral academic terminology (no spiritual references in code)

## 📝 Notes

- Backend must be running on port 8080
- WebSocket connects automatically on mount
- Frontend uses Svelte 5 with TypeScript
- Vite for fast development and building
- No external UI libraries - pure CSS with Wabi-Sabi aesthetic

---

**Built with love for urban researchers** 🏙️

*Om Lokah Samastah Sukhino Bhavantu*
*May all beings benefit from this work.*
