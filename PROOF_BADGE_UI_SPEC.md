# 🎨 Proof Badge UI Specification

**For Agent 1 (Frontend Builder)**

This document shows exactly how proof badges should appear in the UrbanLens reasoning display.

---

## 📦 Data Structure (From Backend)

Every thinking step now includes proof metadata:

```typescript
interface ThinkingStep {
  phase: "Intake" | "Analysis" | "Synthesis" | "Insight";
  timestamp: string;
  description: string;
  confidence: number;
  details?: Record<string, any>;

  // 🆕 NEW FIELDS FROM AGENT 3
  proof_badge: string;   // e.g., "QuaternionS³"
  proof_detail: string;  // e.g., "State encoded as unit quaternion on S³ manifold (||q|| = 1)"
}
```

---

## 🎨 Visual Design

### Inline Badge (Next to Phase Icon)

```
📥 Intake · 70%  🔬 QuaternionS³
   ├─ Receiving and classifying request
   └─ Classified as analyze task (cluster 5)

🔍 Analysis · 80%  🔬 DigitalRoots
   ├─ Identified 3 key demographic clusters
   ├─ Found correlation with transit accessibility
   └─ Mapped stakeholder relationships

🔧 Synthesis · 85%  🔬 MirzakhaniGeodesics
   ├─ Optimal placement: near transit hubs
   └─ Expected reach: 75% of target population

💡 Insight · 95%  🔬 SATOrigami
   └─ Recommend establishing community centers near subway stations A, B, and C
```

### Badge Styling

```css
.proof-badge {
  display: inline-flex;
  align-items: center;
  gap: 4px;
  padding: 2px 8px;
  background: rgba(139, 92, 246, 0.1);  /* Purple-100 with opacity */
  border: 1px solid rgba(139, 92, 246, 0.3);
  border-radius: 12px;
  font-size: 0.75rem;
  font-weight: 600;
  color: #7c3aed;  /* Purple-600 */
  cursor: pointer;
  transition: all 0.2s ease;
}

.proof-badge:hover {
  background: rgba(139, 92, 246, 0.2);
  border-color: rgba(139, 92, 246, 0.5);
  transform: translateY(-1px);
  box-shadow: 0 2px 4px rgba(139, 92, 246, 0.2);
}

.proof-badge::before {
  content: "🔬";
  font-size: 1em;
}
```

### Tooltip on Hover

```
┌──────────────────────────────────────────────────────┐
│ 🔬 QuaternionS³                                      │
│                                                      │
│ State encoded as unit quaternion on S³ manifold     │
│ (||q|| = 1)                                          │
│                                                      │
│ Click to view full proof                             │
└──────────────────────────────────────────────────────┘
```

**Tooltip Implementation (Svelte):**
```svelte
<div class="proof-badge"
     use:tooltip={{
       content: step.proof_detail,
       placement: 'top'
     }}
     on:click={() => openProofModal(step.proof_badge)}>
  {step.proof_badge}
</div>
```

---

## 🔍 Modal on Click

When user clicks a proof badge, open a modal with full details:

```
╔═══════════════════════════════════════════════════════════════╗
║  🔬 QuaternionS³                                     [×]      ║
╠═══════════════════════════════════════════════════════════════╣
║                                                               ║
║  Unit quaternions live on S³ 3-sphere                        ║
║                                                               ║
║  📐 Key Theorems:                                             ║
║  ────────────────────────────────────────────────────────     ║
║  • Hamilton product (non-commutative, associative)           ║
║  • Quaternion norm: ||q|| = sqrt(w² + x² + y² + z²)          ║
║  • S³ closure under multiplication                           ║
║  • SLERP geodesic formula (Shoemake 1985)                    ║
║                                                               ║
║  📂 File: QuaternionS3.lean                                   ║
║  📍 Location: asymmetrica_proofs/AsymmetricaProofs/          ║
║                                                               ║
║  Used in: Intake phase                                        ║
║                                                               ║
║  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       ║
║  │ View on      │  │ Copy Path    │  │ Close        │       ║
║  │ GitHub       │  │              │  │              │       ║
║  └──────────────┘  └──────────────┘  └──────────────┘       ║
║                                                               ║
╚═══════════════════════════════════════════════════════════════╝
```

**Modal Component (Svelte):**
```svelte
<script>
  import { Modal } from '$lib/components/ui/Modal.svelte';

  export let proof: ProofCatalog;
  export let open: boolean;

  function viewOnGitHub() {
    window.open(
      `https://github.com/asymmetrica/proofs/blob/main/${proof.File}`,
      '_blank'
    );
  }

  function copyPath() {
    navigator.clipboard.writeText(
      `C:\\Projects\\asymm_all_math\\asymmetrica_proofs\\AsymmetricaProofs\\${proof.File}`
    );
    // Show toast: "Path copied!"
  }
</script>

<Modal bind:open title="🔬 {proof.Name}">
  <div class="proof-modal">
    <p class="description">{proof.Description}</p>

    <h3>📐 Key Theorems:</h3>
    <ul class="theorems">
      {#each proof.KeyTheorems as theorem}
        <li>{theorem}</li>
      {/each}
    </ul>

    <div class="metadata">
      <p><strong>📂 File:</strong> {proof.File}</p>
      <p><strong>📍 Location:</strong> asymmetrica_proofs/AsymmetricaProofs/</p>
      <p><strong>Used in:</strong> {proof.UsedIn.join(", ")}</p>
    </div>

    <div class="actions">
      <button on:click={viewOnGitHub}>View on GitHub</button>
      <button on:click={copyPath}>Copy Path</button>
      <button on:click={() => open = false}>Close</button>
    </div>
  </div>
</Modal>

<style>
  .proof-modal {
    padding: 1.5rem;
    max-width: 600px;
  }

  .description {
    font-size: 1.125rem;
    margin-bottom: 1.5rem;
    color: var(--text-secondary);
  }

  .theorems {
    list-style: none;
    padding-left: 0;
    margin: 1rem 0;
  }

  .theorems li {
    padding: 0.5rem 0;
    padding-left: 1.5rem;
    position: relative;
  }

  .theorems li::before {
    content: "•";
    position: absolute;
    left: 0;
    color: var(--purple-600);
    font-size: 1.5rem;
  }

  .metadata {
    background: var(--bg-secondary);
    padding: 1rem;
    border-radius: 8px;
    margin: 1.5rem 0;
  }

  .metadata p {
    margin: 0.5rem 0;
    font-family: 'JetBrains Mono', monospace;
    font-size: 0.875rem;
  }

  .actions {
    display: flex;
    gap: 0.75rem;
    margin-top: 1.5rem;
  }

  .actions button {
    flex: 1;
    padding: 0.75rem;
    border-radius: 8px;
    border: 1px solid var(--border);
    background: var(--bg-primary);
    cursor: pointer;
    transition: all 0.2s;
  }

  .actions button:hover {
    background: var(--purple-600);
    color: white;
    border-color: var(--purple-600);
  }
</style>
```

---

## 🔌 API Endpoint (Add to Backend)

```go
// In cmd/urbanlens/main.go or pkg/api/handlers.go

// GET /api/proof/:name
// Returns full proof metadata
func GetProofHandler(c *gin.Context) {
	proofName := c.Param("name")

	proof := reasoning.GetProofByName(proofName)
	if proof == nil {
		c.JSON(http.StatusNotFound, gin.H{
			"error": fmt.Sprintf("Proof '%s' not found", proofName),
		})
		return
	}

	c.JSON(http.StatusOK, proof)
}

// Register route
router.GET("/api/proof/:name", GetProofHandler)
```

**Example Response:**
```json
{
  "Name": "QuaternionS³",
  "File": "QuaternionS3.lean",
  "Description": "Unit quaternions live on S³ 3-sphere",
  "KeyTheorems": [
    "Hamilton product (non-commutative, associative)",
    "Quaternion norm: ||q|| = sqrt(w² + x² + y² + z²)",
    "S³ closure under multiplication",
    "SLERP geodesic formula (Shoemake 1985)"
  ],
  "UsedIn": ["Intake"]
}
```

---

## 📱 Responsive Design

### Desktop (Full View)
```
┌─────────────────────────────────────────────────────┐
│ 📥 Intake · 70%              🔬 QuaternionS³        │
│    └─ Receiving and classifying request            │
└─────────────────────────────────────────────────────┘
```

### Mobile (Stacked)
```
┌────────────────────────┐
│ 📥 Intake              │
│ 70% confidence         │
│ 🔬 QuaternionS³        │
│                        │
│ └─ Receiving and       │
│    classifying request │
└────────────────────────┘
```

---

## 🎯 Integration Checklist

- [ ] Add `proof_badge` and `proof_detail` to TypeScript interfaces
- [ ] Create `ProofBadge.svelte` component with hover tooltip
- [ ] Create `ProofModal.svelte` component with full details
- [ ] Add `/api/proof/:name` endpoint to backend
- [ ] Wire proof badges into reasoning step display
- [ ] Test tooltip display on hover
- [ ] Test modal opening on click
- [ ] Test "Copy Path" button functionality
- [ ] Test "View on GitHub" link
- [ ] Verify responsive design on mobile

---

## 🎨 Color Palette

```css
:root {
  --proof-bg: rgba(139, 92, 246, 0.1);       /* Purple-100 10% opacity */
  --proof-border: rgba(139, 92, 246, 0.3);   /* Purple-100 30% opacity */
  --proof-text: #7c3aed;                      /* Purple-600 */
  --proof-hover-bg: rgba(139, 92, 246, 0.2); /* Purple-100 20% opacity */
  --proof-shadow: rgba(139, 92, 246, 0.2);   /* Purple shadow */
}
```

---

## 📝 Example Usage in Reasoning Display

```svelte
<script>
  import { ProofBadge } from '$lib/components/ProofBadge.svelte';
  import { ProofModal } from '$lib/components/ProofModal.svelte';

  let steps: ThinkingStep[] = [];
  let selectedProof: string | null = null;
  let modalOpen = false;

  function openProof(badge: string) {
    selectedProof = badge;
    modalOpen = true;
  }

  // Fetch proof details when needed
  async function fetchProof(badge: string): Promise<ProofCatalog> {
    const res = await fetch(`/api/proof/${badge}`);
    return res.json();
  }
</script>

<div class="reasoning-display">
  {#each steps as step}
    <div class="thinking-step phase-{step.phase.toLowerCase()}">
      <div class="step-header">
        <span class="phase-icon">{getPhaseIcon(step.phase)}</span>
        <span class="phase-name">{step.phase}</span>
        <span class="confidence">{(step.confidence * 100).toFixed(0)}%</span>

        {#if step.proof_badge}
          <ProofBadge
            badge={step.proof_badge}
            detail={step.proof_detail}
            on:click={() => openProof(step.proof_badge)} />
        {/if}
      </div>

      <div class="step-content">
        <p>{step.description}</p>
      </div>
    </div>
  {/each}
</div>

{#if selectedProof && modalOpen}
  {#await fetchProof(selectedProof)}
    <p>Loading proof...</p>
  {:then proof}
    <ProofModal bind:open={modalOpen} {proof} />
  {/await}
{/if}
```

---

## 🚀 Expected User Experience

1. **User makes request** → "Analyze population patterns in downtown"
2. **Reasoning display appears** with thinking steps streaming in
3. **User sees phase icons** (📥 🔍 🔧 💡) with proof badges (🔬)
4. **User hovers over proof badge** → Tooltip shows mathematical context
5. **User clicks proof badge** → Modal opens with full theorem list
6. **User clicks "View on GitHub"** → Opens Lean file in browser
7. **User thinks:** "Wow, this AI actually has formal proofs! 🤯"

---

## 💡 Why This Matters

**For Researchers:**
- Transparency: See the math behind every decision
- Trust: Formal proofs > "trust me, I'm an AI"
- Rigor: Lean 4 theorem prover = mathematically verified

**For UrbanLens:**
- Differentiation: No other urban planning tool has formal proofs
- Academic credibility: Can cite actual theorems
- Research sovereignty: We own the math, not just the code

**For the Mission:**
- Demonstrates mathematical seriousness
- Shows we're not just "vibes-based AI"
- Builds trust with government/academic users

---

**Agent 3 → Agent 1 Handoff Complete!** 🎨✨

Everything you need to build beautiful proof badge displays is here. The backend is ready, the data flows, now it's time to make it shine in the UI! 🚀

---

**Om Lokah Samastah Sukhino Bhavantu**
*May all researchers see the mathematical rigor!* 🔬🙏
