# Backend Integration Notes

## WebSocket Message Format Mapping

### Current Backend Types (pkg/streaming/websocket.go)
```go
const (
    MsgPhaseUpdate   = "phase_update"
    MsgThinkingStep  = "thinking_step"
    MsgProgress      = "progress"
    MsgResult        = "result"
    MsgError         = "error"
    MsgSystemStatus  = "system_status"
)
```

### Frontend Expected Types (stores/websocket.ts)
```typescript
type: 'phase_update' | 'thinking' | 'response' | 'error' | 'complete'
```

### Mapping Needed

| Backend Type | Frontend Expects | Mapping |
|--------------|------------------|---------|
| `phase_update` | `phase_update` | ✅ Direct match |
| `thinking_step` | `thinking` | 🔧 Map `thinking_step` → `thinking` |
| `result` | `response` | 🔧 Map `result` → `response` |
| `error` | `error` | ✅ Direct match |
| (none) | `complete` | 🔧 Add new type when done |

### Recommended Backend Changes

#### Option 1: Update Backend Types (Minimal)
```go
// In pkg/streaming/websocket.go
const (
    MsgPhaseUpdate   MessageType = "phase_update"
    MsgThinking      MessageType = "thinking"        // Changed from thinking_step
    MsgResponse      MessageType = "response"        // Changed from result
    MsgComplete      MessageType = "complete"        // New
    MsgError         MessageType = "error"
)
```

#### Option 2: Update Frontend Store (Alternative)
If you prefer to keep backend unchanged, update frontend:

```typescript
// In src/lib/stores/websocket.ts
function handleMessage(message: StreamMessage) {
    // Map backend types to frontend types
    const type = message.type === 'thinking_step' ? 'thinking' :
                 message.type === 'result' ? 'response' :
                 message.type;

    switch (type) {
        case 'phase_update':
            // ...
        case 'thinking':
        case 'response':
            // ...
    }
}
```

### Message Structure

#### Backend Sends (Current)
```json
{
  "type": "phase_update",
  "phase": "analysis",
  "content": "Examining patterns...",
  "progress": 0.5,
  "confidence": 0.87,
  "timestamp": "2025-12-24T12:15:00Z",
  "data": {},
  "proof_badge": "Quaternion S³ verified",
  "proof_detail": "Convergence proven via Lyapunov"
}
```

#### Frontend Expects (Current)
```json
{
  "type": "phase_update",
  "phase": "intake" | "analysis" | "synthesis" | "insight" | "complete",
  "content": "Optional text",
  "timestamp": "2025-12-24T12:15:00Z"
}
```

### Client → Server Messages

#### Frontend Sends
```json
{
  "type": "query",
  "input": "User question here",
  "timestamp": "2025-12-24T12:15:00Z"
}
```

#### Backend Expects (Current)
```json
{
  "action": "query",
  "input": "User question here"
}
```

### Recommended Alignment

**Update backend to match frontend expectations:**

```go
// In pkg/streaming/websocket.go - ReadPump
var request struct {
    Type  string `json:"type"`   // Changed from "action"
    Input string `json:"input"`
}

if request.Type == "query" {
    // Process query
}
```

---

## Testing Checklist

### Phase 1: Connection
- [ ] Frontend connects to ws://localhost:8080/ws
- [ ] Backend accepts connection
- [ ] Connection status shows "connected"

### Phase 2: Query
- [ ] User types message
- [ ] Click Send or press Enter
- [ ] Frontend sends JSON with `type: "query"`
- [ ] Backend receives and parses

### Phase 3: Response Stream
- [ ] Backend sends `phase_update` with phase name
- [ ] Frontend shows reasoning phase indicator
- [ ] Backend sends thinking/response chunks
- [ ] Frontend accumulates streaming text
- [ ] Backend sends complete signal
- [ ] Frontend saves final message

### Phase 4: Error Handling
- [ ] Test disconnect/reconnect
- [ ] Test malformed JSON
- [ ] Test error messages
- [ ] Frontend shows friendly error UI

---

## Quick Fix Recommendations

### Backend (Minimal Changes)
```go
// 1. Update message types in pkg/streaming/websocket.go
const (
    MsgPhaseUpdate MessageType = "phase_update"
    MsgThinking    MessageType = "thinking"    // was thinking_step
    MsgResponse    MessageType = "response"    // was result
    MsgComplete    MessageType = "complete"    // new
    MsgError       MessageType = "error"
)

// 2. Update ReadPump to expect "type" field
var request struct {
    Type  string `json:"type"`   // was "action"
    Input string `json:"input"`
}

// 3. Send "complete" message when done
c.Send <- Message{
    Type:      MsgComplete,
    Phase:     "insight",
    Timestamp: time.Now(),
}
```

### Frontend (Alternative if backend unchanged)
```typescript
// Add type mapping in websocket.ts
const typeMap: Record<string, string> = {
    'thinking_step': 'thinking',
    'result': 'response',
    'phase_update': 'phase_update',
    'error': 'error'
};

function handleMessage(rawMessage: any) {
    const message = {
        ...rawMessage,
        type: typeMap[rawMessage.type] || rawMessage.type
    };
    // Continue with mapped type...
}
```

---

## Integration Priority

1. **P0 (Critical)**: Message type alignment
2. **P1 (High)**: Phase name consistency
3. **P2 (Medium)**: Error handling
4. **P3 (Nice-to-have)**: Progress/confidence display

---

## Expected Flow

```
User opens http://localhost:5173
  ↓
Frontend: connect to ws://localhost:8080/ws
  ↓
Backend: Accept connection, register client
  ↓
Frontend: Show "connected" status
  ↓
User: Types "Analyze census data" + Send
  ↓
Frontend: Send { type: "query", input: "...", timestamp: "..." }
  ↓
Backend: Receive query, start processing
  ↓
Backend: Send { type: "phase_update", phase: "intake" }
  ↓
Frontend: Show "Intake" phase active
  ↓
Backend: Send { type: "thinking", content: "Understanding..." }
  ↓
Frontend: Accumulate streaming text
  ↓
Backend: Send { type: "phase_update", phase: "analysis" }
  ↓
Frontend: Move to "Analysis" phase
  ↓
Backend: Send { type: "response", content: "Census data shows..." }
  ↓
Frontend: Continue streaming
  ↓
Backend: Send { type: "complete", phase: "insight" }
  ↓
Frontend: Finalize message, clear streaming
  ↓
User sees complete response!
```

---

**Status**: Integration mapping documented
**Next Step**: Update either backend types OR frontend mapping
**Estimated**: 5-10 minutes to align
