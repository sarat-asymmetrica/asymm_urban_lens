<script lang="ts">
    /**
     * PhaseIndicator - Visual representation of the Void → Flow → Solution journey
     * Shows current phase with animated transitions and tooltips
     */
    import { currentPhase, isStreaming } from '$lib/stores/websocket';
    import type { ReasoningPhase } from '$lib/stores/websocket';

    // Map reasoning phases to journey phases
    const journeyPhases = [
        {
            id: 'void',
            name: 'Void',
            description: 'Exploring possibilities, opening to the unknown',
            phases: ['intake'] as ReasoningPhase[],
            color: '#8A8580',
            icon: '∅'
        },
        {
            id: 'flow',
            name: 'Flow',
            description: 'Analyzing patterns, connecting insights',
            phases: ['analysis', 'synthesis'] as ReasoningPhase[],
            color: '#4A6B52',
            icon: '≈'
        },
        {
            id: 'solution',
            name: 'Solution',
            description: 'Crystallizing understanding, formulating answers',
            phases: ['insight', 'complete'] as ReasoningPhase[],
            color: '#C5A059',
            icon: '✦'
        }
    ];

    function getCurrentJourneyPhase(phase: ReasoningPhase): number {
        return journeyPhases.findIndex(jp => jp.phases.includes(phase));
    }

    $: currentJourneyIndex = getCurrentJourneyPhase($currentPhase);
    $: showIndicator = $isStreaming;
</script>

<div class="phase-indicator" class:visible={showIndicator}>
    <div class="journey-path">
        {#each journeyPhases as phase, index}
            <div
                class="journey-phase"
                class:active={index === currentJourneyIndex}
                class:complete={index < currentJourneyIndex}
                style="--phase-color: {phase.color}"
            >
                <!-- Icon circle -->
                <div class="phase-circle" title={phase.description}>
                    <span class="phase-icon">{phase.icon}</span>

                    {#if index === currentJourneyIndex}
                        <!-- Animated ring for active phase -->
                        <svg class="active-ring" width="60" height="60" viewBox="0 0 60 60">
                            <circle
                                cx="30"
                                cy="30"
                                r="28"
                                fill="none"
                                stroke={phase.color}
                                stroke-width="2"
                                opacity="0.3"
                                stroke-dasharray="175.929"
                                stroke-dashoffset="0"
                            >
                                <animate
                                    attributeName="stroke-dashoffset"
                                    from="0"
                                    to="175.929"
                                    dur="3s"
                                    repeatCount="indefinite"
                                />
                            </circle>
                        </svg>
                    {/if}
                </div>

                <!-- Label -->
                <div class="phase-label">{phase.name}</div>

                <!-- Connector line -->
                {#if index < journeyPhases.length - 1}
                    <div
                        class="phase-connector"
                        class:active={index < currentJourneyIndex}
                    ></div>
                {/if}
            </div>
        {/each}
    </div>

    <!-- Current phase description -->
    {#if currentJourneyIndex >= 0}
        <div class="phase-description">
            {journeyPhases[currentJourneyIndex].description}
        </div>
    {/if}
</div>

<style>
    .phase-indicator {
        background: rgba(255, 255, 255, 0.6);
        border: 1px solid #E8E0D0;
        border-radius: 13px;
        padding: 21px;
        margin-bottom: 21px;
        opacity: 0;
        transform: translateY(-13px);
        transition: all 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
        pointer-events: none;
        backdrop-filter: blur(8px);
    }

    .phase-indicator.visible {
        opacity: 1;
        transform: translateY(0);
        pointer-events: auto;
    }

    .journey-path {
        display: flex;
        justify-content: center;
        align-items: center;
        gap: 8px;
        margin-bottom: 13px;
    }

    .journey-phase {
        position: relative;
        display: flex;
        flex-direction: column;
        align-items: center;
        opacity: 0.4;
        transition: opacity 233ms ease;
    }

    .journey-phase.active {
        opacity: 1;
    }

    .journey-phase.complete {
        opacity: 0.7;
    }

    .phase-circle {
        position: relative;
        width: 60px;
        height: 60px;
        background: white;
        border: 2px solid #E8E0D0;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        margin-bottom: 8px;
        transition: all 233ms cubic-bezier(0.4, 0.0, 0.2, 1);
        cursor: help;
    }

    .journey-phase.active .phase-circle {
        border-color: var(--phase-color);
        background: rgba(255, 255, 255, 0.95);
        box-shadow: 0 0 0 4px rgba(var(--phase-color-rgb), 0.1);
        transform: scale(1.1);
    }

    .journey-phase.complete .phase-circle {
        border-color: var(--phase-color);
        background: var(--phase-color);
    }

    .phase-icon {
        font-size: 24px;
        font-weight: 300;
        color: #8A8580;
        transition: color 233ms ease;
    }

    .journey-phase.active .phase-icon {
        color: var(--phase-color);
        font-weight: 400;
    }

    .journey-phase.complete .phase-icon {
        color: white;
    }

    .active-ring {
        position: absolute;
        top: 0;
        left: 0;
        pointer-events: none;
    }

    .phase-label {
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        font-weight: 500;
        color: #8A8580;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        transition: color 233ms ease;
    }

    .journey-phase.active .phase-label {
        color: var(--phase-color);
    }

    .phase-connector {
        width: 55px;
        height: 2px;
        background: #E8E0D0;
        margin: 0 -8px;
        margin-top: -38px;
        transition: background 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    .phase-connector.active {
        background: #4A6B52;
    }

    .phase-description {
        text-align: center;
        font-family: 'Outfit', sans-serif;
        font-size: 13px;
        color: #5A5550;
        font-style: italic;
        padding: 0 21px;
        animation: fadeIn 377ms ease;
    }

    @keyframes fadeIn {
        from {
            opacity: 0;
        }
        to {
            opacity: 1;
        }
    }

    /* Responsive */
    @media (max-width: 600px) {
        .journey-path {
            flex-direction: column;
            gap: 21px;
        }

        .phase-connector {
            width: 2px;
            height: 34px;
            margin: -8px 0;
        }
    }
</style>
