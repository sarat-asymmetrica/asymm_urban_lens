<script lang="ts">
    /**
     * ProofViewer - Display Lean proofs with syntax highlighting and verification status
     * Celebrates successful verification with animations
     */
    import { onMount } from 'svelte';
    import hljs from 'highlight.js';

    export let proof: LeanProof;
    export let onExplain: (() => void) | null = null;

    interface LeanProof {
        id: string;
        theorem: string;
        code: string;
        status: 'pending' | 'verifying' | 'verified' | 'error';
        error?: string;
        timestamp: Date;
    }

    let codeElement: HTMLElement;
    let copied = false;
    let showCelebration = false;

    // Highlight Lean code
    function highlightCode(code: string): string {
        try {
            // Use Haskell highlighting for Lean (similar syntax)
            return hljs.highlight(code, { language: 'haskell' }).value;
        } catch (err) {
            console.error('Highlight error:', err);
            return code;
        }
    }

    function copyToClipboard() {
        navigator.clipboard.writeText(proof.code);
        copied = true;
        setTimeout(() => (copied = false), 2000);
    }

    function handleExplain() {
        if (onExplain) {
            onExplain();
        }
    }

    // Trigger celebration when verified
    $: if (proof.status === 'verified' && !showCelebration) {
        showCelebration = true;
        setTimeout(() => {
            showCelebration = false;
        }, 3000);
    }

    $: highlightedCode = highlightCode(proof.code);
</script>

<div class="proof-viewer" data-status={proof.status}>
    <!-- Header -->
    <div class="proof-header">
        <div class="proof-title">
            <span class="proof-icon">
                {#if proof.status === 'verified'}
                    ✅
                {:else if proof.status === 'verifying'}
                    ⏳
                {:else if proof.status === 'error'}
                    ❌
                {:else}
                    📐
                {/if}
            </span>
            <span class="theorem-name">{proof.theorem}</span>
        </div>

        <div class="proof-status" class:verified={proof.status === 'verified'} class:error={proof.status === 'error'}>
            {#if proof.status === 'pending'}
                <span class="status-text">Draft</span>
            {:else if proof.status === 'verifying'}
                <span class="status-text">
                    <span class="spinner"></span>
                    Verifying...
                </span>
            {:else if proof.status === 'verified'}
                <span class="status-text verified-text">Verified!</span>
            {:else if proof.status === 'error'}
                <span class="status-text error-text">Verification Failed</span>
            {/if}
        </div>
    </div>

    <!-- Code Block -->
    <div class="code-container">
        <pre><code bind:this={codeElement}>{@html highlightedCode}</code></pre>

        <!-- Copy Button -->
        <button class="copy-btn" on:click={copyToClipboard} title="Copy code">
            {#if copied}
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <polyline points="20 6 9 17 4 12"></polyline>
                </svg>
            {:else}
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                    <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                </svg>
            {/if}
        </button>
    </div>

    <!-- Error Message -->
    {#if proof.status === 'error' && proof.error}
        <div class="error-message">
            <div class="error-header">
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <circle cx="12" cy="12" r="10"></circle>
                    <line x1="12" y1="8" x2="12" y2="12"></line>
                    <line x1="12" y1="16" x2="12.01" y2="16"></line>
                </svg>
                <span>Error Details</span>
            </div>
            <pre class="error-content">{proof.error}</pre>
        </div>
    {/if}

    <!-- Actions -->
    <div class="proof-actions">
        {#if onExplain}
            <button class="btn-explain" on:click={handleExplain}>
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <circle cx="12" cy="12" r="10"></circle>
                    <path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"></path>
                    <line x1="12" y1="17" x2="12.01" y2="17"></line>
                </svg>
                Explain this proof
            </button>
        {/if}

        {#if proof.status === 'verified'}
            <a
                href="https://leanprover.github.io/theorem_proving_in_lean4/"
                target="_blank"
                rel="noopener noreferrer"
                class="btn-learn"
            >
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <path d="M2 3h6a4 4 0 0 1 4 4v14a3 3 0 0 0-3-3H2z"></path>
                    <path d="M22 3h-6a4 4 0 0 0-4 4v14a3 3 0 0 1 3-3h7z"></path>
                </svg>
                Learn More About Lean
            </a>
        {/if}
    </div>

    <!-- Celebration Animation -->
    {#if showCelebration}
        <div class="celebration">
            <div class="confetti-container">
                {#each Array(30) as _, i}
                    <div
                        class="confetti"
                        style="
                            left: {Math.random() * 100}%;
                            animation-delay: {Math.random() * 0.5}s;
                            background: {['#C5A059', '#4A6B52', '#8B5A3C'][i % 3]};
                        "
                    ></div>
                {/each}
            </div>
            <div class="celebration-message">
                <div class="celebration-icon">🎉</div>
                <div class="celebration-text">Proof Verified!</div>
                <div class="celebration-subtext">You've formalized scientific truth!</div>
            </div>
        </div>
    {/if}
</div>

<style>
    .proof-viewer {
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 21px;
        margin: 21px 0;
        transition: all 233ms ease;
        position: relative;
        overflow: hidden;
    }

    .proof-viewer[data-status="verified"] {
        border-color: #4A6B52;
        box-shadow: 0 0 0 2px rgba(74, 107, 82, 0.1);
    }

    .proof-viewer[data-status="error"] {
        border-color: #DC2626;
        box-shadow: 0 0 0 2px rgba(220, 38, 38, 0.1);
    }

    .proof-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 13px;
        padding-bottom: 13px;
        border-bottom: 1px solid #E8E0D0;
    }

    .proof-title {
        display: flex;
        align-items: center;
        gap: 8px;
    }

    .proof-icon {
        font-size: 20px;
    }

    .theorem-name {
        font-family: 'Cinzel', serif;
        font-size: 16px;
        font-weight: 600;
        color: #3D3835;
    }

    .proof-status {
        display: flex;
        align-items: center;
        gap: 5px;
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        padding: 5px 10px;
        border-radius: 8px;
        background: #F5F0E6;
        color: #8A8580;
    }

    .proof-status.verified {
        background: rgba(74, 107, 82, 0.1);
        color: #4A6B52;
        animation: glow 1s ease-in-out;
    }

    @keyframes glow {
        0%, 100% { box-shadow: 0 0 0 0 rgba(74, 107, 82, 0); }
        50% { box-shadow: 0 0 13px 3px rgba(74, 107, 82, 0.3); }
    }

    .proof-status.error {
        background: rgba(220, 38, 38, 0.1);
        color: #DC2626;
    }

    .spinner {
        display: inline-block;
        width: 12px;
        height: 12px;
        border: 2px solid #E8E0D0;
        border-top-color: #4A6B52;
        border-radius: 50%;
        animation: spin 1s linear infinite;
    }

    @keyframes spin {
        to { transform: rotate(360deg); }
    }

    .verified-text {
        font-weight: 600;
        animation: pulse 1s ease;
    }

    @keyframes pulse {
        0%, 100% { opacity: 1; }
        50% { opacity: 0.7; }
    }

    /* Code Container */
    .code-container {
        position: relative;
        background: rgba(61, 56, 53, 0.03);
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        margin-bottom: 13px;
        overflow: hidden;
    }

    pre {
        margin: 0;
        padding: 21px;
        overflow-x: auto;
        font-family: 'Courier New', monospace;
        font-size: 13px;
        line-height: 1.6;
    }

    code {
        color: #3D3835;
    }

    /* Syntax highlighting (Lean/Haskell-style) */
    code :global(.hljs-keyword) { color: #4A6B52; font-weight: 600; }
    code :global(.hljs-type) { color: #8B5A3C; }
    code :global(.hljs-title) { color: #C5A059; font-weight: 600; }
    code :global(.hljs-string) { color: #3A5542; }
    code :global(.hljs-number) { color: #A68542; }
    code :global(.hljs-comment) { color: #A8A098; font-style: italic; }
    code :global(.hljs-built_in) { color: #5D8066; }

    .copy-btn {
        position: absolute;
        top: 13px;
        right: 13px;
        background: rgba(245, 240, 230, 0.95);
        border: 1px solid #E8E0D0;
        border-radius: 6px;
        padding: 8px;
        color: #5A5550;
        cursor: pointer;
        opacity: 0;
        transition: all 144ms ease;
        backdrop-filter: blur(4px);
    }

    .code-container:hover .copy-btn {
        opacity: 1;
    }

    .copy-btn:hover {
        background: white;
        color: #C5A059;
        transform: scale(1.1);
    }

    /* Error Message */
    .error-message {
        background: rgba(220, 38, 38, 0.05);
        border: 1px solid rgba(220, 38, 38, 0.2);
        border-radius: 8px;
        padding: 13px;
        margin-bottom: 13px;
    }

    .error-header {
        display: flex;
        align-items: center;
        gap: 8px;
        color: #DC2626;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        font-weight: 600;
        margin-bottom: 8px;
    }

    .error-content {
        font-family: 'Courier New', monospace;
        font-size: 12px;
        color: #B91C1C;
        white-space: pre-wrap;
        margin: 0;
        padding: 8px;
        background: rgba(255, 255, 255, 0.5);
        border-radius: 4px;
    }

    /* Actions */
    .proof-actions {
        display: flex;
        gap: 13px;
        flex-wrap: wrap;
    }

    .btn-explain,
    .btn-learn {
        display: flex;
        align-items: center;
        gap: 8px;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        padding: 8px 13px;
        border-radius: 8px;
        cursor: pointer;
        transition: all 144ms ease;
        text-decoration: none;
    }

    .btn-explain {
        background: #F5F0E6;
        border: 1px solid #E8E0D0;
        color: #5A5550;
    }

    .btn-explain:hover {
        background: white;
        border-color: #C5A059;
        color: #3D3835;
        transform: translateY(-1px);
    }

    .btn-learn {
        background: rgba(74, 107, 82, 0.1);
        border: 1px solid #4A6B52;
        color: #4A6B52;
    }

    .btn-learn:hover {
        background: #4A6B52;
        color: white;
        transform: translateY(-1px);
    }

    /* Celebration */
    .celebration {
        position: absolute;
        inset: 0;
        pointer-events: none;
        z-index: 10;
    }

    .confetti-container {
        position: absolute;
        inset: 0;
        overflow: hidden;
    }

    .confetti {
        position: absolute;
        width: 8px;
        height: 8px;
        top: -10px;
        animation: confetti-fall 3s ease-out forwards;
    }

    @keyframes confetti-fall {
        0% {
            transform: translateY(0) rotate(0deg);
            opacity: 1;
        }
        100% {
            transform: translateY(600px) rotate(720deg);
            opacity: 0;
        }
    }

    .celebration-message {
        position: absolute;
        top: 50%;
        left: 50%;
        transform: translate(-50%, -50%);
        text-align: center;
        background: rgba(255, 255, 255, 0.98);
        padding: 34px;
        border-radius: 13px;
        border: 2px solid #4A6B52;
        box-shadow: 0 8px 32px rgba(0, 0, 0, 0.15);
        animation: celebrationPop 0.6s cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes celebrationPop {
        0% {
            transform: translate(-50%, -50%) scale(0);
            opacity: 0;
        }
        50% {
            transform: translate(-50%, -50%) scale(1.1);
        }
        100% {
            transform: translate(-50%, -50%) scale(1);
            opacity: 1;
        }
    }

    .celebration-icon {
        font-size: 55px;
        margin-bottom: 13px;
        animation: bounce 1s ease infinite;
    }

    @keyframes bounce {
        0%, 100% { transform: translateY(0); }
        50% { transform: translateY(-10px); }
    }

    .celebration-text {
        font-family: 'Cinzel', serif;
        font-size: 24px;
        font-weight: 600;
        color: #4A6B52;
        margin-bottom: 5px;
    }

    .celebration-subtext {
        font-family: 'Lora', serif;
        font-size: 14px;
        color: #5A5550;
        font-style: italic;
    }

    /* Scrollbar */
    pre::-webkit-scrollbar {
        height: 6px;
    }

    pre::-webkit-scrollbar-track {
        background: transparent;
    }

    pre::-webkit-scrollbar-thumb {
        background: rgba(197, 160, 89, 0.3);
        border-radius: 3px;
    }

    pre::-webkit-scrollbar-thumb:hover {
        background: rgba(197, 160, 89, 0.5);
    }
</style>
