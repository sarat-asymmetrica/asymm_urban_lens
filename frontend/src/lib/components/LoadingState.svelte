<script lang="ts">
    /**
     * LoadingState - Creative loading indicators that change based on phase
     * Brings personality and delight to the thinking process
     */
    import { onMount } from 'svelte';
    import { spring } from 'svelte/motion';
    import { currentPhase } from '$lib/stores/websocket';
    import type { ReasoningPhase } from '$lib/stores/websocket';

    // Creative messages for each phase
    const phaseMessages: Record<ReasoningPhase, string[]> = {
        intake: [
            'Listening deeply...',
            'Understanding your question...',
            'Receiving your inquiry...',
            'Opening to possibility...'
        ],
        analysis: [
            'Exploring the data landscape...',
            'Connecting the dots...',
            'Searching for patterns...',
            'Diving into the numbers...',
            'Analyzing relationships...'
        ],
        synthesis: [
            'Weaving insights together...',
            'Connecting across domains...',
            'Finding coherence...',
            'Building the narrative...',
            'Crystallizing understanding...'
        ],
        insight: [
            'Forming recommendations...',
            'Articulating findings...',
            'Preparing response...',
            'Sharing insights...'
        ],
        complete: [
            'Complete!'
        ]
    };

    // Particle animation
    const particles = Array.from({ length: 8 }, (_, i) => ({
        angle: (i * Math.PI * 2) / 8,
        radius: spring(0, { stiffness: 0.05, damping: 0.3 }),
        opacity: spring(0, { stiffness: 0.05, damping: 0.3 })
    }));

    let mounted = false;
    let currentMessage = '';
    let messageIndex = 0;

    // Rotate through messages for current phase
    function rotateMessage() {
        const messages = phaseMessages[$currentPhase];
        currentMessage = messages[messageIndex % messages.length];
        messageIndex++;
    }

    // Animate particles
    function animateParticles() {
        const t = Date.now() / 1000;

        particles.forEach((p, i) => {
            const phase = (i * Math.PI * 2) / particles.length;
            const radiusVariation = 0.618 * Math.sin(t * 2 + phase); // Golden ratio variation
            p.radius.set(34 + radiusVariation * 13);
            p.opacity.set(0.3 + 0.4 * Math.sin(t * 3 + phase));
        });

        if (mounted) {
            requestAnimationFrame(animateParticles);
        }
    }

    onMount(() => {
        mounted = true;
        rotateMessage();
        animateParticles();

        // Change message every 3 seconds
        const messageInterval = setInterval(rotateMessage, 3000);

        return () => {
            mounted = false;
            clearInterval(messageInterval);
        };
    });

    // Update message when phase changes
    $: if ($currentPhase) {
        messageIndex = 0;
        rotateMessage();
    }
</script>

<div class="loading-state">
    <!-- Animated particle field -->
    <div class="particle-field">
        <svg width="100" height="100" viewBox="0 0 100 100">
            <!-- Center pulse -->
            <circle
                cx="50"
                cy="50"
                r="8"
                fill="#C5A059"
                opacity="0.8"
            >
                <animate
                    attributeName="r"
                    values="6;10;6"
                    dur="2s"
                    repeatCount="indefinite"
                />
                <animate
                    attributeName="opacity"
                    values="0.8;1;0.8"
                    dur="2s"
                    repeatCount="indefinite"
                />
            </circle>

            <!-- Orbiting particles -->
            {#each particles as particle, i}
                <circle
                    cx={50 + $particle.radius * Math.cos(particle.angle)}
                    cy={50 + $particle.radius * Math.sin(particle.angle)}
                    r="3"
                    fill="#4A6B52"
                    opacity={$particle.opacity}
                />
            {/each}
        </svg>
    </div>

    <!-- Phase-based message -->
    <div class="message">
        {currentMessage}
    </div>

    <!-- Subtle progress indicator -->
    <div class="progress-dots">
        <span class="dot" class:active={$currentPhase === 'intake'}></span>
        <span class="dot" class:active={$currentPhase === 'analysis'}></span>
        <span class="dot" class:active={$currentPhase === 'synthesis'}></span>
        <span class="dot" class:active={$currentPhase === 'insight'}></span>
    </div>
</div>

<style>
    .loading-state {
        display: flex;
        flex-direction: column;
        align-items: center;
        gap: 21px;
        padding: 34px;
        animation: fadeIn 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes fadeIn {
        from {
            opacity: 0;
            transform: translateY(-8px);
        }
        to {
            opacity: 1;
            transform: translateY(0);
        }
    }

    .particle-field {
        position: relative;
        width: 100px;
        height: 100px;
    }

    .message {
        font-family: 'Outfit', sans-serif;
        font-size: 14px;
        color: #5A5550;
        text-align: center;
        min-height: 21px;
        animation: messageFade 377ms ease;
    }

    @keyframes messageFade {
        from {
            opacity: 0;
        }
        to {
            opacity: 1;
        }
    }

    .progress-dots {
        display: flex;
        gap: 8px;
        margin-top: 8px;
    }

    .dot {
        width: 6px;
        height: 6px;
        border-radius: 50%;
        background: #E8E0D0;
        transition: all 233ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    .dot.active {
        background: #4A6B52;
        transform: scale(1.5);
        box-shadow: 0 0 8px rgba(74, 107, 82, 0.5);
    }
</style>
