<script lang="ts">
    /**
     * ReasoningPhase - Visual indicator of AI thinking process
     * Shows transparent "thinking out loud" with 4 phases
     */
    import { currentPhase, isStreaming } from '$lib/stores/websocket';
    import type { ReasoningPhase } from '$lib/stores/websocket';

    const phases: { name: ReasoningPhase; label: string; description: string }[] = [
        {
            name: 'intake',
            label: 'Intake',
            description: 'Understanding your question'
        },
        {
            name: 'analysis',
            label: 'Analysis',
            description: 'Examining data and patterns'
        },
        {
            name: 'synthesis',
            label: 'Synthesis',
            description: 'Connecting insights'
        },
        {
            name: 'insight',
            label: 'Insight',
            description: 'Formulating response'
        }
    ];

    function getPhaseIndex(phase: ReasoningPhase): number {
        return phases.findIndex(p => p.name === phase);
    }

    $: currentIndex = getPhaseIndex($currentPhase);
</script>

<div class="reasoning-phase" class:active={$isStreaming}>
    <div class="phase-header">
        <div class="thinking-indicator">
            <span class="pulse"></span>
            <span class="text">Thinking...</span>
        </div>
    </div>

    <div class="phase-steps">
        {#each phases as phase, index}
            <div
                class="step"
                class:active={index === currentIndex && $isStreaming}
                class:complete={index < currentIndex}
            >
                <div class="step-circle">
                    {#if index < currentIndex}
                        <span class="check">✓</span>
                    {:else if index === currentIndex && $isStreaming}
                        <span class="spinner"></span>
                    {:else}
                        <span class="number">{index + 1}</span>
                    {/if}
                </div>

                <div class="step-content">
                    <div class="step-label">{phase.label}</div>
                    <div class="step-description">{phase.description}</div>
                </div>

                {#if index < phases.length - 1}
                    <div class="step-connector" class:active={index < currentIndex}></div>
                {/if}
            </div>
        {/each}
    </div>
</div>

<style>
    .reasoning-phase {
        background: rgba(245, 240, 230, 0.6);
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 21px;
        margin-bottom: 21px;
        opacity: 0;
        transform: translateY(-8px);
        transition: all 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    .reasoning-phase.active {
        opacity: 1;
        transform: translateY(0);
    }

    .phase-header {
        display: flex;
        align-items: center;
        margin-bottom: 21px;
    }

    .thinking-indicator {
        display: flex;
        align-items: center;
        gap: 8px;
        font-family: 'Outfit', sans-serif;
        font-size: 14px;
        color: #5A5550;
    }

    .pulse {
        width: 8px;
        height: 8px;
        background: #4A6B52;
        border-radius: 50%;
        animation: pulse 2s cubic-bezier(0.4, 0.0, 0.6, 1) infinite;
    }

    @keyframes pulse {
        0%, 100% {
            opacity: 1;
            transform: scale(1);
        }
        50% {
            opacity: 0.6;
            transform: scale(1.2);
        }
    }

    .phase-steps {
        display: flex;
        gap: 13px;
    }

    .step {
        flex: 1;
        position: relative;
        display: flex;
        flex-direction: column;
        align-items: center;
        opacity: 0.5;
        transition: opacity 233ms ease;
    }

    .step.active {
        opacity: 1;
    }

    .step.complete {
        opacity: 0.8;
    }

    .step-circle {
        width: 34px;
        height: 34px;
        border-radius: 50%;
        background: white;
        border: 2px solid #E8E0D0;
        display: flex;
        align-items: center;
        justify-content: center;
        font-weight: 600;
        font-size: 14px;
        color: #8A8580;
        transition: all 233ms ease;
        margin-bottom: 8px;
    }

    .step.active .step-circle {
        border-color: #4A6B52;
        background: #F5F0E6;
        box-shadow: 0 0 0 3px rgba(74, 107, 82, 0.1);
    }

    .step.complete .step-circle {
        border-color: #4A6B52;
        background: #4A6B52;
        color: white;
    }

    .check {
        font-size: 16px;
    }

    .spinner {
        width: 16px;
        height: 16px;
        border: 2px solid #E8E0D0;
        border-top-color: #4A6B52;
        border-radius: 50%;
        animation: spin 1s linear infinite;
    }

    @keyframes spin {
        to { transform: rotate(360deg); }
    }

    .step-content {
        text-align: center;
    }

    .step-label {
        font-family: 'Outfit', sans-serif;
        font-weight: 500;
        font-size: 13px;
        color: #3D3835;
        margin-bottom: 3px;
    }

    .step-description {
        font-size: 11px;
        color: #8A8580;
        line-height: 1.3;
    }

    .step-connector {
        position: absolute;
        top: 17px;
        left: calc(50% + 17px);
        right: calc(-50% + 17px);
        height: 2px;
        background: #E8E0D0;
        transition: background 377ms ease;
    }

    .step-connector.active {
        background: #4A6B52;
    }

    /* Fibonacci timing for phase transitions */
    .step:nth-child(1) { transition-delay: 0ms; }
    .step:nth-child(2) { transition-delay: 89ms; }
    .step:nth-child(3) { transition-delay: 144ms; }
    .step:nth-child(4) { transition-delay: 233ms; }
</style>
