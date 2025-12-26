<script lang="ts">
    /**
     * VisualizationRequest - Request AI-generated images for concepts
     * Shows loading states, image display with zoom, and AI captions
     */
    import { createEventDispatcher } from 'svelte';

    export let concept: string = '';
    export let isLoading: boolean = false;
    export let imageUrl: string | null = null;
    export let caption: string | null = null;
    export let error: string | null = null;

    const dispatch = createEventDispatcher<{
        visualize: { concept: string };
    }>();

    let isZoomed = false;
    let loadingMessages: string[] = [
        'Imagining the concept...',
        'Painting with pixels...',
        'Weaving visual patterns...',
        'Crystallizing the idea...',
        'Almost there...'
    ];
    let currentMessageIndex = 0;

    function requestVisualization() {
        if (!concept.trim()) return;

        dispatch('visualize', { concept: concept.trim() });
    }

    function toggleZoom() {
        isZoomed = !isZoomed;
    }

    function handleKeyDown(e: KeyboardEvent) {
        if (e.key === 'Escape' && isZoomed) {
            isZoomed = false;
        }
    }

    // Rotate loading messages
    $: if (isLoading) {
        const interval = setInterval(() => {
            currentMessageIndex = (currentMessageIndex + 1) % loadingMessages.length;
        }, 2000);

        return () => clearInterval(interval);
    }

    $: currentMessage = loadingMessages[currentMessageIndex];
</script>

<svelte:window on:keydown={handleKeyDown} />

<div class="visualization-request">
    <!-- Request Form (if no image yet) -->
    {#if !imageUrl && !isLoading && !error}
        <button class="visualize-btn" on:click={requestVisualization}>
            <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <rect x="3" y="3" width="18" height="18" rx="2" ry="2"></rect>
                <circle cx="8.5" cy="8.5" r="1.5"></circle>
                <polyline points="21 15 16 10 5 21"></polyline>
            </svg>
            <span>Visualize this concept</span>
        </button>
    {/if}

    <!-- Loading State -->
    {#if isLoading}
        <div class="loading-state">
            <div class="loading-animation">
                <!-- Animated brush strokes -->
                <svg width="120" height="120" viewBox="0 0 120 120">
                    <!-- Circular brush stroke -->
                    <circle
                        cx="60"
                        cy="60"
                        r="40"
                        fill="none"
                        stroke="#C5A059"
                        stroke-width="3"
                        stroke-dasharray="251.2"
                        stroke-dashoffset="0"
                        opacity="0.6"
                    >
                        <animate
                            attributeName="stroke-dashoffset"
                            from="0"
                            to="251.2"
                            dur="2s"
                            repeatCount="indefinite"
                        />
                    </circle>

                    <!-- Inner circle -->
                    <circle
                        cx="60"
                        cy="60"
                        r="30"
                        fill="none"
                        stroke="#4A6B52"
                        stroke-width="2"
                        stroke-dasharray="188.4"
                        stroke-dashoffset="188.4"
                        opacity="0.4"
                    >
                        <animate
                            attributeName="stroke-dashoffset"
                            from="188.4"
                            to="0"
                            dur="2s"
                            repeatCount="indefinite"
                        />
                    </circle>

                    <!-- Center pulse -->
                    <circle cx="60" cy="60" r="8" fill="#C5A059" opacity="0.8">
                        <animate
                            attributeName="r"
                            values="6;12;6"
                            dur="1.5s"
                            repeatCount="indefinite"
                        />
                        <animate
                            attributeName="opacity"
                            values="0.8;0.3;0.8"
                            dur="1.5s"
                            repeatCount="indefinite"
                        />
                    </circle>
                </svg>
            </div>

            <div class="loading-message">
                {currentMessage}
            </div>

            <div class="loading-concept">
                "{concept}"
            </div>
        </div>
    {/if}

    <!-- Error State -->
    {#if error}
        <div class="error-state">
            <div class="error-icon">⚠️</div>
            <div class="error-message">{error}</div>
            <button class="retry-btn" on:click={requestVisualization}>
                <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                    <polyline points="23 4 23 10 17 10"></polyline>
                    <path d="M20.49 15a9 9 0 1 1-2.12-9.36L23 10"></path>
                </svg>
                Try Again
            </button>
        </div>
    {/if}

    <!-- Image Display -->
    {#if imageUrl && !isLoading}
        <div class="image-display">
            <!-- Image with zoom -->
            <div class="image-container" on:click={toggleZoom} role="button" tabindex="0">
                <img
                    src={imageUrl}
                    alt={caption || concept}
                    class="visualization-image"
                    class:zoomed={isZoomed}
                />

                <div class="zoom-hint" class:hidden={isZoomed}>
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <circle cx="11" cy="11" r="8"></circle>
                        <path d="m21 21-4.35-4.35"></path>
                        <line x1="11" y1="8" x2="11" y2="14"></line>
                        <line x1="8" y1="11" x2="14" y2="11"></line>
                    </svg>
                    Click to zoom
                </div>
            </div>

            <!-- Caption -->
            {#if caption}
                <div class="image-caption">
                    <div class="caption-icon">🎨</div>
                    <div class="caption-text">{caption}</div>
                </div>
            {/if}

            <!-- Actions -->
            <div class="image-actions">
                <button class="action-btn" on:click={() => window.open(imageUrl, '_blank')}>
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"></path>
                        <polyline points="7 10 12 15 17 10"></polyline>
                        <line x1="12" y1="15" x2="12" y2="3"></line>
                    </svg>
                    Download
                </button>

                <button class="action-btn" on:click={() => imageUrl = null}>
                    <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <path d="M3 6h18"></path>
                        <path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"></path>
                    </svg>
                    Remove
                </button>
            </div>
        </div>
    {/if}

    <!-- Zoom Overlay -->
    {#if isZoomed}
        <div class="zoom-overlay" on:click={toggleZoom}>
            <div class="zoom-content">
                <img src={imageUrl} alt={caption || concept} />
                <button class="close-zoom" on:click={toggleZoom}>
                    <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                        <line x1="18" y1="6" x2="6" y2="18"></line>
                        <line x1="6" y1="6" x2="18" y2="18"></line>
                    </svg>
                </button>
            </div>
        </div>
    {/if}
</div>

<style>
    .visualization-request {
        margin: 21px 0;
    }

    /* Request Button */
    .visualize-btn {
        display: flex;
        align-items: center;
        gap: 8px;
        padding: 13px 21px;
        background: linear-gradient(135deg, #C5A059 0%, #A68542 100%);
        border: none;
        border-radius: 13px;
        color: white;
        font-family: 'Outfit', sans-serif;
        font-size: 14px;
        font-weight: 500;
        cursor: pointer;
        transition: all 233ms cubic-bezier(0.4, 0.0, 0.2, 1);
        box-shadow: 0 2px 8px rgba(197, 160, 89, 0.3);
    }

    .visualize-btn:hover {
        transform: translateY(-2px);
        box-shadow: 0 4px 16px rgba(197, 160, 89, 0.4);
    }

    .visualize-btn:active {
        transform: translateY(0);
    }

    /* Loading State */
    .loading-state {
        display: flex;
        flex-direction: column;
        align-items: center;
        padding: 34px;
        background: rgba(245, 240, 230, 0.5);
        border: 1px dashed #E8E0D0;
        border-radius: 13px;
        animation: fadeIn 377ms ease;
    }

    @keyframes fadeIn {
        from { opacity: 0; transform: translateY(-8px); }
        to { opacity: 1; transform: translateY(0); }
    }

    .loading-animation {
        margin-bottom: 21px;
    }

    .loading-message {
        font-family: 'Outfit', sans-serif;
        font-size: 15px;
        color: #5A5550;
        margin-bottom: 8px;
        animation: messageFade 2s ease infinite;
    }

    @keyframes messageFade {
        0%, 100% { opacity: 1; }
        50% { opacity: 0.6; }
    }

    .loading-concept {
        font-family: 'Lora', serif;
        font-size: 14px;
        color: #8A8580;
        font-style: italic;
        text-align: center;
        max-width: 300px;
    }

    /* Error State */
    .error-state {
        text-align: center;
        padding: 34px;
        background: rgba(220, 38, 38, 0.05);
        border: 1px solid rgba(220, 38, 38, 0.2);
        border-radius: 13px;
        animation: fadeIn 377ms ease;
    }

    .error-icon {
        font-size: 48px;
        margin-bottom: 13px;
    }

    .error-message {
        font-family: 'Lora', serif;
        font-size: 14px;
        color: #DC2626;
        margin-bottom: 21px;
    }

    .retry-btn {
        display: inline-flex;
        align-items: center;
        gap: 8px;
        padding: 8px 13px;
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        color: #5A5550;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .retry-btn:hover {
        background: #F5F0E6;
        border-color: #C5A059;
        transform: translateY(-1px);
    }

    /* Image Display */
    .image-display {
        animation: fadeIn 377ms ease;
    }

    .image-container {
        position: relative;
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        overflow: hidden;
        cursor: zoom-in;
        transition: all 233ms ease;
        margin-bottom: 13px;
    }

    .image-container:hover {
        box-shadow: 0 4px 16px rgba(0, 0, 0, 0.1);
    }

    .visualization-image {
        width: 100%;
        height: auto;
        display: block;
        transition: transform 233ms ease;
    }

    .image-container:hover .visualization-image {
        transform: scale(1.02);
    }

    .zoom-hint {
        position: absolute;
        bottom: 13px;
        right: 13px;
        display: flex;
        align-items: center;
        gap: 5px;
        padding: 8px 13px;
        background: rgba(255, 255, 255, 0.95);
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        color: #5A5550;
        opacity: 0;
        transition: opacity 144ms ease;
        backdrop-filter: blur(4px);
    }

    .image-container:hover .zoom-hint {
        opacity: 1;
    }

    .zoom-hint.hidden {
        display: none;
    }

    /* Caption */
    .image-caption {
        background: rgba(197, 160, 89, 0.1);
        border: 1px solid rgba(197, 160, 89, 0.3);
        border-radius: 8px;
        padding: 13px;
        margin-bottom: 13px;
        display: flex;
        gap: 13px;
        align-items: flex-start;
    }

    .caption-icon {
        font-size: 20px;
        flex-shrink: 0;
    }

    .caption-text {
        font-family: 'Lora', serif;
        font-size: 14px;
        line-height: 1.6;
        color: #3D3835;
        font-style: italic;
    }

    /* Image Actions */
    .image-actions {
        display: flex;
        gap: 8px;
    }

    .action-btn {
        display: flex;
        align-items: center;
        gap: 8px;
        padding: 8px 13px;
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        color: #5A5550;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .action-btn:hover {
        background: #F5F0E6;
        border-color: #C5A059;
        transform: translateY(-1px);
    }

    /* Zoom Overlay */
    .zoom-overlay {
        position: fixed;
        inset: 0;
        background: rgba(0, 0, 0, 0.9);
        display: flex;
        align-items: center;
        justify-content: center;
        z-index: 1000;
        cursor: zoom-out;
        animation: fadeIn 233ms ease;
        backdrop-filter: blur(8px);
    }

    .zoom-content {
        position: relative;
        max-width: 90vw;
        max-height: 90vh;
        animation: zoomIn 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes zoomIn {
        from {
            opacity: 0;
            transform: scale(0.8);
        }
        to {
            opacity: 1;
            transform: scale(1);
        }
    }

    .zoom-content img {
        max-width: 100%;
        max-height: 90vh;
        border-radius: 8px;
        box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
    }

    .close-zoom {
        position: absolute;
        top: -50px;
        right: 0;
        background: rgba(255, 255, 255, 0.1);
        border: 1px solid rgba(255, 255, 255, 0.3);
        border-radius: 50%;
        width: 40px;
        height: 40px;
        display: flex;
        align-items: center;
        justify-content: center;
        color: white;
        cursor: pointer;
        transition: all 144ms ease;
        backdrop-filter: blur(4px);
    }

    .close-zoom:hover {
        background: rgba(255, 255, 255, 0.2);
        transform: scale(1.1);
    }
</style>
