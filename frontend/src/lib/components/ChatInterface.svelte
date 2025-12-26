<script lang="ts">
    /**
     * ChatInterface - "Her"-style conversational UI
     * Streaming text display with elegant, research-appropriate aesthetics
     */
    import { onMount, onDestroy, tick } from 'svelte';
    import {
        connect,
        disconnect,
        sendMessage,
        clearConversation,
        conversations,
        streamingContent,
        connectionStatus,
        isStreaming
    } from '$lib/stores/websocket';
    import ReasoningPhase from './ReasoningPhase.svelte';
    import Message from './Message.svelte';
    import LoadingState from './LoadingState.svelte';
    import PhaseIndicator from './PhaseIndicator.svelte';

    let inputText = '';
    let messagesContainer: HTMLDivElement;
    let inputElement: HTMLTextAreaElement;

    // Auto-scroll to bottom when new messages arrive
    $: if ($conversations || $streamingContent) {
        tick().then(() => {
            if (messagesContainer) {
                messagesContainer.scrollTop = messagesContainer.scrollHeight;
            }
        });
    }

    onMount(() => {
        // Connect to WebSocket on mount
        connect();

        // Focus input
        inputElement?.focus();
    });

    onDestroy(() => {
        // Clean disconnect on unmount
        disconnect();
    });

    function handleSubmit() {
        const message = inputText.trim();
        if (!message) return;

        sendMessage(message);
        inputText = '';

        // Resize textarea back to single line
        if (inputElement) {
            inputElement.style.height = 'auto';
        }
    }

    function handleKeyDown(e: KeyboardEvent) {
        if (e.key === 'Enter' && !e.shiftKey) {
            e.preventDefault();
            handleSubmit();
        }
    }

    function handleInput() {
        // Auto-resize textarea
        if (inputElement) {
            inputElement.style.height = 'auto';
            inputElement.style.height = inputElement.scrollHeight + 'px';
        }
    }

    function formatTimestamp(date: Date): string {
        return date.toLocaleTimeString('en-US', {
            hour: '2-digit',
            minute: '2-digit'
        });
    }
</script>

<div class="chat-interface">
    <!-- Header -->
    <div class="chat-header">
        <div class="header-content">
            <h1>Urban Lens</h1>
            <p class="subtitle">Research Intelligence for Urban Informatics</p>
        </div>

        <div class="header-status">
            <div class="status-indicator" class:connected={$connectionStatus === 'connected'}>
                <span class="dot"></span>
                <span class="text">{$connectionStatus}</span>
            </div>

            <button class="btn-clear" on:click={clearConversation} title="Clear conversation">
                <svg width="16" height="16" viewBox="0 0 16 16" fill="none">
                    <path d="M3 4h10M5 4V3a1 1 0 011-1h4a1 1 0 011 1v1m1 0v9a1 1 0 01-1 1H5a1 1 0 01-1-1V4h8z" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/>
                </svg>
            </button>
        </div>
    </div>

    <!-- Messages -->
    <div class="messages-container" bind:this={messagesContainer}>
        <div class="messages">
            {#if $conversations.length === 0}
                <div class="welcome">
                    <div class="welcome-icon">🏙️</div>
                    <h2>Welcome to Urban Lens</h2>
                    <p>Ask me anything about urban research, census data, surveys, or spatial analysis.</p>
                    <div class="example-queries">
                        <button on:click={() => inputText = 'How can I enhance census data for Bangalore?'}>
                            Enhance census data
                        </button>
                        <button on:click={() => inputText = 'Validate survey responses against codebook'}>
                            Validate survey
                        </button>
                        <button on:click={() => inputText = 'Analyze spatial clusters in city data'}>
                            Spatial analysis
                        </button>
                    </div>
                </div>
            {:else}
                {#each $conversations as message (message.id)}
                    <Message {message} />
                {/each}

                <!-- Streaming message -->
                {#if $isStreaming}
                    <LoadingState />
                {/if}
            {/if}
        </div>
    </div>

    <!-- Phase Indicator (Void → Flow → Solution) -->
    <PhaseIndicator />

    <!-- Reasoning Phase (shows when streaming) -->
    {#if $isStreaming}
        <ReasoningPhase />
    {/if}

    <!-- Input Area -->
    <div class="input-area">
        <textarea
            bind:this={inputElement}
            bind:value={inputText}
            on:keydown={handleKeyDown}
            on:input={handleInput}
            placeholder="Ask about urban research, census data, surveys..."
            disabled={$connectionStatus !== 'connected'}
            rows="1"
        ></textarea>

        <button
            class="btn-send"
            on:click={handleSubmit}
            disabled={!inputText.trim() || $connectionStatus !== 'connected'}
            title="Send message"
        >
            <svg width="20" height="20" viewBox="0 0 20 20" fill="none">
                <path d="M18 2L9 11M18 2l-6 16-3-7-7-3 16-6z" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
            </svg>
        </button>
    </div>
</div>

<style>
    .chat-interface {
        display: flex;
        flex-direction: column;
        height: 100vh;
        background: #F5F0E6;
        font-family: 'Lora', serif;
    }

    /* Header */
    .chat-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        padding: 21px 34px;
        background: white;
        border-bottom: 1px solid #E8E0D0;
    }

    .header-content h1 {
        font-family: 'Cinzel', serif;
        font-size: 24px;
        font-weight: 600;
        color: #3D3835;
        margin: 0 0 3px 0;
    }

    .subtitle {
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        color: #8A8580;
        margin: 0;
    }

    .header-status {
        display: flex;
        align-items: center;
        gap: 13px;
    }

    .status-indicator {
        display: flex;
        align-items: center;
        gap: 8px;
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        color: #8A8580;
        text-transform: capitalize;
    }

    .status-indicator .dot {
        width: 8px;
        height: 8px;
        border-radius: 50%;
        background: #E8E0D0;
        transition: background 233ms ease;
    }

    .status-indicator.connected .dot {
        background: #4A6B52;
        animation: pulse 2s ease-in-out infinite;
    }

    .btn-clear {
        background: transparent;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        padding: 8px;
        color: #8A8580;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .btn-clear:hover {
        background: #F5F0E6;
        color: #5A5550;
    }

    /* Messages */
    .messages-container {
        flex: 1;
        overflow-y: auto;
        padding: 34px;
        scroll-behavior: smooth;
    }

    .messages {
        max-width: 875px; /* 87.5% of 1000px */
        margin: 0 auto;
    }

    .welcome {
        text-align: center;
        padding: 89px 34px;
    }

    .welcome-icon {
        font-size: 55px;
        margin-bottom: 21px;
    }

    .welcome h2 {
        font-family: 'Cinzel', serif;
        font-size: 28px;
        color: #3D3835;
        margin-bottom: 13px;
    }

    .welcome p {
        font-size: 16px;
        color: #5A5550;
        margin-bottom: 34px;
    }

    .example-queries {
        display: flex;
        gap: 13px;
        justify-content: center;
        flex-wrap: wrap;
    }

    .example-queries button {
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 13px 21px;
        font-family: 'Outfit', sans-serif;
        font-size: 14px;
        color: #5A5550;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .example-queries button:hover {
        background: #F5F0E6;
        border-color: #C5A059;
        color: #3D3835;
    }


    /* Input Area */
    .input-area {
        display: flex;
        gap: 13px;
        padding: 21px 34px;
        background: white;
        border-top: 1px solid #E8E0D0;
    }

    textarea {
        flex: 1;
        background: #F5F0E6;
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 13px 21px;
        font-family: 'Lora', serif;
        font-size: 15px;
        color: #3D3835;
        resize: none;
        max-height: 200px;
        overflow-y: auto;
        transition: border-color 144ms ease;
    }

    textarea:focus {
        outline: none;
        border-color: #C5A059;
    }

    textarea:disabled {
        opacity: 0.5;
        cursor: not-allowed;
    }

    textarea::placeholder {
        color: #A8A098;
    }

    .btn-send {
        align-self: flex-end;
        background: #4A6B52;
        border: none;
        border-radius: 13px;
        padding: 13px 21px;
        color: white;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .btn-send:hover:not(:disabled) {
        background: #3A5542;
        transform: translateY(-1px);
    }

    .btn-send:disabled {
        opacity: 0.5;
        cursor: not-allowed;
    }

    /* Scrollbar styling */
    .messages-container::-webkit-scrollbar {
        width: 8px;
    }

    .messages-container::-webkit-scrollbar-track {
        background: #F5F0E6;
    }

    .messages-container::-webkit-scrollbar-thumb {
        background: #E8E0D0;
        border-radius: 8px;
    }

    .messages-container::-webkit-scrollbar-thumb:hover {
        background: #C5A059;
    }
</style>
