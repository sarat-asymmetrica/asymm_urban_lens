<script lang="ts">
    /**
     * Message - Enhanced message component with markdown, LaTeX, code highlighting, and images
     * Inspired by INDRA but customized for Urban Lens research aesthetic
     */
    import { onMount } from 'svelte';
    import { marked } from 'marked';
    import hljs from 'highlight.js';
    import katex from 'katex';
    import type { ConversationMessage } from '$lib/stores/websocket';

    export let message: ConversationMessage;

    let contentElement: HTMLDivElement;
    let showCopy = false;
    let copied = false;

    // Configure marked for code highlighting
    marked.setOptions({
        highlight: function(code, lang) {
            if (lang && hljs.getLanguage(lang)) {
                try {
                    return hljs.highlight(code, { language: lang }).value;
                } catch (err) {
                    console.error('Highlight error:', err);
                }
            }
            return hljs.highlightAuto(code).value;
        },
        breaks: true,
        gfm: true
    });

    function renderContent(content: string): string {
        // First, protect LaTeX expressions from markdown processing
        const latexBlocks: string[] = [];
        let processed = content;

        // Extract display math: $$...$$
        processed = processed.replace(/\$\$([\s\S]+?)\$\$/g, (match, latex) => {
            latexBlocks.push(`DISPLAYMATH_${latexBlocks.length}`);
            return `DISPLAYMATH_${latexBlocks.length - 1}`;
        });

        // Extract inline math: $...$
        processed = processed.replace(/\$([^\n$]+?)\$/g, (match, latex) => {
            latexBlocks.push(`INLINEMATH_${latexBlocks.length}`);
            return `INLINEMATH_${latexBlocks.length - 1}`;
        });

        // Render markdown
        processed = marked.parse(processed) as string;

        // Restore and render LaTeX
        latexBlocks.forEach((placeholder, index) => {
            const isDisplay = placeholder.startsWith('DISPLAYMATH');
            const latex = content.match(isDisplay ? /\$\$([\s\S]+?)\$\$/g : /\$([^\n$]+?)\$/g)?.[index];

            if (latex) {
                const cleaned = latex.replace(/\$\$/g, '').replace(/\$/g, '');
                try {
                    const rendered = katex.renderToString(cleaned, {
                        displayMode: isDisplay,
                        throwOnError: false,
                        strict: false
                    });
                    processed = processed.replace(placeholder, rendered);
                } catch (err) {
                    console.error('KaTeX error:', err);
                    processed = processed.replace(placeholder, `<code class="math-error">${cleaned}</code>`);
                }
            }
        });

        return processed;
    }

    function handleCopy() {
        navigator.clipboard.writeText(message.content);
        copied = true;
        setTimeout(() => (copied = false), 2000);
    }

    function formatTimestamp(date: Date): string {
        return date.toLocaleTimeString('en-US', {
            hour: '2-digit',
            minute: '2-digit'
        });
    }

    // Add copy buttons to code blocks after mount
    onMount(() => {
        if (!contentElement) return;

        const codeBlocks = contentElement.querySelectorAll('pre code');
        codeBlocks.forEach((block) => {
            const pre = block.parentElement;
            if (!pre) return;

            // Create copy button for code block
            const copyBtn = document.createElement('button');
            copyBtn.className = 'code-copy-btn';
            copyBtn.innerHTML = `
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                    <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                </svg>
            `;
            copyBtn.title = 'Copy code';

            copyBtn.addEventListener('click', () => {
                const code = block.textContent || '';
                navigator.clipboard.writeText(code);
                copyBtn.innerHTML = `
                    <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <polyline points="20 6 9 17 4 12"></polyline>
                    </svg>
                `;
                setTimeout(() => {
                    copyBtn.innerHTML = `
                        <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                            <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                            <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                        </svg>
                    `;
                }, 2000);
            });

            pre.style.position = 'relative';
            pre.appendChild(copyBtn);
        });
    });

    $: isUser = message.role === 'user';
    $: isAssistant = message.role === 'assistant';
    $: renderedContent = renderContent(message.content);
</script>

<div class="message" class:user={isUser} class:assistant={isAssistant}>
    <div class="message-role">
        {#if isUser}
            <span class="icon">👤</span>
            <span class="label">You</span>
        {:else}
            <span class="icon">🔬</span>
            <span class="label">Urban Lens</span>
        {/if}
    </div>

    <div
        class="message-content"
        class:user-content={isUser}
        class:assistant-content={isAssistant}
        on:mouseenter={() => showCopy = true}
        on:mouseleave={() => showCopy = false}
    >
        <div class="content-inner" bind:this={contentElement}>
            {@html renderedContent}
        </div>

        <!-- Copy button (appears on hover) -->
        {#if showCopy}
            <button
                class="copy-button"
                on:click={handleCopy}
                title="Copy message"
            >
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
        {/if}
    </div>

    <div class="message-timestamp">
        {formatTimestamp(message.timestamp)}
    </div>
</div>

<style>
    .message {
        margin-bottom: 34px;
        animation: fadeIn 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes fadeIn {
        from {
            opacity: 0;
            transform: translateY(8px);
        }
        to {
            opacity: 1;
            transform: translateY(0);
        }
    }

    .message-role {
        display: flex;
        align-items: center;
        gap: 8px;
        margin-bottom: 8px;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        font-weight: 500;
    }

    .message.user .message-role {
        color: #4A6B52;
    }

    .message.assistant .message-role {
        color: #C5A059;
    }

    .message-content {
        position: relative;
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 21px;
        transition: all 144ms ease;
    }

    .message-content:hover {
        box-shadow: 0 2px 12px rgba(0, 0, 0, 0.08);
    }

    .user-content {
        background: #F5F0E6;
        border-color: #4A6B52;
    }

    .assistant-content {
        background: white;
        border-color: #E8E0D0;
    }

    .content-inner {
        font-size: 15px;
        line-height: 1.618; /* Golden ratio */
        color: #3D3835;
    }

    /* Markdown styling */
    .content-inner :global(p) {
        margin: 0 0 1em 0;
    }

    .content-inner :global(p:last-child) {
        margin-bottom: 0;
    }

    .content-inner :global(h1),
    .content-inner :global(h2),
    .content-inner :global(h3) {
        font-family: 'Cinzel', serif;
        color: #3D3835;
        margin: 1.618em 0 0.618em 0;
        line-height: 1.3;
    }

    .content-inner :global(h1) { font-size: 1.8em; }
    .content-inner :global(h2) { font-size: 1.5em; }
    .content-inner :global(h3) { font-size: 1.2em; }

    .content-inner :global(ul),
    .content-inner :global(ol) {
        margin: 0.618em 0;
        padding-left: 1.618em;
    }

    .content-inner :global(li) {
        margin: 0.382em 0;
    }

    /* Code blocks */
    .content-inner :global(pre) {
        background: rgba(61, 56, 53, 0.05);
        border: 1px solid #E8E0D0;
        border-left: 3px solid #C5A059;
        border-radius: 8px;
        padding: 1em;
        margin: 1em 0;
        overflow-x: auto;
        font-family: 'Courier New', monospace;
        font-size: 0.9em;
        line-height: 1.5;
    }

    .content-inner :global(code) {
        font-family: 'Courier New', monospace;
        font-size: 0.9em;
    }

    .content-inner :global(pre code) {
        background: transparent;
        border: none;
        padding: 0;
    }

    .content-inner :global(:not(pre) > code) {
        background: rgba(197, 160, 89, 0.1);
        color: #8A5A2A;
        padding: 0.2em 0.4em;
        border-radius: 4px;
        border: 1px solid rgba(197, 160, 89, 0.2);
    }

    /* Links */
    .content-inner :global(a) {
        color: #4A6B52;
        text-decoration: none;
        border-bottom: 1px dotted #4A6B52;
        transition: all 144ms ease;
    }

    .content-inner :global(a:hover) {
        color: #C5A059;
        border-bottom-color: #C5A059;
    }

    /* Strong/Bold */
    .content-inner :global(strong) {
        font-weight: 600;
        color: #C5A059;
    }

    /* Emphasis/Italic */
    .content-inner :global(em) {
        font-style: italic;
        opacity: 0.95;
    }

    /* Blockquotes */
    .content-inner :global(blockquote) {
        border-left: 3px solid #C5A059;
        padding-left: 1em;
        margin: 1em 0;
        color: #5A5550;
        font-style: italic;
    }

    /* Tables */
    .content-inner :global(table) {
        border-collapse: collapse;
        width: 100%;
        margin: 1em 0;
        font-size: 0.95em;
    }

    .content-inner :global(th),
    .content-inner :global(td) {
        border: 1px solid #E8E0D0;
        padding: 8px 13px;
        text-align: left;
    }

    .content-inner :global(th) {
        background: #F5F0E6;
        font-weight: 600;
        color: #3D3835;
    }

    /* Images */
    .content-inner :global(img) {
        max-width: 100%;
        height: auto;
        border-radius: 8px;
        margin: 1em 0;
        box-shadow: 0 2px 8px rgba(0, 0, 0, 0.1);
        transition: transform 233ms ease;
    }

    .content-inner :global(img:hover) {
        transform: scale(1.02);
    }

    /* LaTeX math */
    .content-inner :global(.katex) {
        font-size: 1.1em;
    }

    .content-inner :global(.katex-display) {
        margin: 1em 0;
        overflow-x: auto;
        overflow-y: hidden;
    }

    .content-inner :global(.math-error) {
        background: rgba(220, 38, 38, 0.1);
        color: #DC2626;
        padding: 0.2em 0.4em;
        border-radius: 4px;
    }

    /* Copy buttons */
    .copy-button {
        position: absolute;
        top: 13px;
        right: 13px;
        background: rgba(245, 240, 230, 0.9);
        border: 1px solid #E8E0D0;
        border-radius: 6px;
        padding: 6px;
        color: #5A5550;
        cursor: pointer;
        opacity: 0;
        transition: all 144ms ease;
        backdrop-filter: blur(4px);
    }

    .message-content:hover .copy-button {
        opacity: 1;
    }

    .copy-button:hover {
        background: white;
        color: #C5A059;
        transform: scale(1.1);
    }

    .content-inner :global(.code-copy-btn) {
        position: absolute;
        top: 8px;
        right: 8px;
        background: rgba(245, 240, 230, 0.9);
        border: 1px solid #E8E0D0;
        border-radius: 4px;
        padding: 4px 8px;
        color: #5A5550;
        cursor: pointer;
        opacity: 0;
        transition: all 144ms ease;
        font-size: 12px;
        backdrop-filter: blur(4px);
    }

    .content-inner :global(pre:hover .code-copy-btn) {
        opacity: 1;
    }

    .content-inner :global(.code-copy-btn:hover) {
        background: white;
        color: #C5A059;
    }

    .message-timestamp {
        margin-top: 5px;
        font-family: 'Outfit', sans-serif;
        font-size: 11px;
        color: #A8A098;
        opacity: 0.6;
        transition: opacity 144ms ease;
    }

    .message:hover .message-timestamp {
        opacity: 1;
    }

    /* Scrollbar for code blocks */
    .content-inner :global(pre)::-webkit-scrollbar {
        height: 6px;
    }

    .content-inner :global(pre)::-webkit-scrollbar-track {
        background: transparent;
    }

    .content-inner :global(pre)::-webkit-scrollbar-thumb {
        background: rgba(197, 160, 89, 0.3);
        border-radius: 3px;
    }

    .content-inner :global(pre)::-webkit-scrollbar-thumb:hover {
        background: rgba(197, 160, 89, 0.5);
    }
</style>
