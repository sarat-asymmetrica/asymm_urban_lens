<script lang="ts">
    /**
     * DiscoveryJournal - Sidebar showing user's discovery journey
     * Tracks observations, insights, connections, and milestones
     */
    import { onMount } from 'svelte';

    export let discoveries: Discovery[] = [];
    export let currentPath: string[] = [];
    export let domainsExplored: Set<string> = new Set();
    export let isCollapsed: boolean = false;

    interface Discovery {
        id: string;
        type: 'observation' | 'insight' | 'connection' | 'theorem' | 'milestone';
        content: string;
        timestamp: Date;
        domain?: string;
        relatedTo?: string[]; // IDs of related discoveries
    }

    interface Milestone {
        name: string;
        achieved: boolean;
        description: string;
        icon: string;
    }

    const milestones: Milestone[] = [
        {
            name: 'First Observation',
            achieved: false,
            description: 'Made your first scientific observation',
            icon: '👀'
        },
        {
            name: 'Why Chain',
            achieved: false,
            description: 'Asked "why" 5 times in a row',
            icon: '🤔'
        },
        {
            name: 'Cross-Domain',
            achieved: false,
            description: 'Connected insights across 2+ domains',
            icon: '🌉'
        },
        {
            name: 'First Theorem',
            achieved: false,
            description: 'Formalized your first theorem in Lean',
            icon: '🎓'
        },
        {
            name: 'Verified Proof',
            achieved: false,
            description: 'Had a proof successfully verified',
            icon: '✅'
        }
    ];

    function toggleCollapse() {
        isCollapsed = !isCollapsed;
    }

    function getDiscoveryIcon(type: Discovery['type']): string {
        const icons = {
            observation: '👁️',
            insight: '💡',
            connection: '🔗',
            theorem: '📐',
            milestone: '🏆'
        };
        return icons[type] || '•';
    }

    function formatTime(date: Date): string {
        const now = new Date();
        const diff = now.getTime() - date.getTime();
        const minutes = Math.floor(diff / 60000);

        if (minutes < 1) return 'just now';
        if (minutes < 60) return `${minutes}m ago`;

        const hours = Math.floor(minutes / 60);
        if (hours < 24) return `${hours}h ago`;

        const days = Math.floor(hours / 24);
        return `${days}d ago`;
    }

    // Update milestones based on discoveries
    $: {
        if (discoveries.length > 0) {
            milestones[0].achieved = discoveries.some(d => d.type === 'observation');
            milestones[1].achieved = currentPath.length >= 5;
            milestones[2].achieved = domainsExplored.size >= 2;
            milestones[3].achieved = discoveries.some(d => d.type === 'theorem');
            // Milestone 4 would be updated from external verified event
        }
    }

    $: totalDiscoveries = discoveries.length;
    $: recentDiscoveries = discoveries.slice(-8).reverse();
</script>

<aside class="discovery-journal" class:collapsed={isCollapsed}>
    <!-- Toggle button -->
    <button class="toggle-btn" on:click={toggleCollapse} title={isCollapsed ? 'Expand' : 'Collapse'}>
        {#if isCollapsed}
            <svg width="16" height="16" viewBox="0 0 16 16" fill="none">
                <path d="M6 12l4-4-4-4" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
            </svg>
        {:else}
            <svg width="16" height="16" viewBox="0 0 16 16" fill="none">
                <path d="M10 12L6 8l4-4" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
            </svg>
        {/if}
    </button>

    {#if !isCollapsed}
        <div class="journal-content">
            <!-- Header -->
            <div class="journal-header">
                <h3>Your Journey</h3>
                <div class="discovery-count">{totalDiscoveries} discoveries</div>
            </div>

            <!-- Current Path (breadcrumbs) -->
            {#if currentPath.length > 0}
                <div class="current-path">
                    <div class="path-label">Current Path</div>
                    <div class="breadcrumbs">
                        {#each currentPath as step, i}
                            <span class="breadcrumb" class:active={i === currentPath.length - 1}>
                                {step}
                            </span>
                            {#if i < currentPath.length - 1}
                                <span class="separator">→</span>
                            {/if}
                        {/each}
                    </div>
                </div>
            {/if}

            <!-- Domains Explored -->
            {#if domainsExplored.size > 0}
                <div class="domains-explored">
                    <div class="section-label">Domains Explored</div>
                    <div class="domain-tags">
                        {#each Array.from(domainsExplored) as domain}
                            <span class="domain-tag">{domain}</span>
                        {/each}
                    </div>
                </div>
            {/if}

            <!-- Milestones -->
            <div class="milestones">
                <div class="section-label">Milestones</div>
                <div class="milestone-grid">
                    {#each milestones as milestone}
                        <div
                            class="milestone"
                            class:achieved={milestone.achieved}
                            title={milestone.description}
                        >
                            <span class="milestone-icon">{milestone.icon}</span>
                            <span class="milestone-name">{milestone.name}</span>
                        </div>
                    {/each}
                </div>
            </div>

            <!-- Recent Discoveries -->
            {#if recentDiscoveries.length > 0}
                <div class="recent-discoveries">
                    <div class="section-label">Recent Discoveries</div>
                    <div class="discoveries-list">
                        {#each recentDiscoveries as discovery}
                            <div class="discovery-item" data-type={discovery.type}>
                                <div class="discovery-header">
                                    <span class="discovery-icon">{getDiscoveryIcon(discovery.type)}</span>
                                    <span class="discovery-type">{discovery.type}</span>
                                    <span class="discovery-time">{formatTime(discovery.timestamp)}</span>
                                </div>
                                <div class="discovery-content">
                                    {discovery.content}
                                </div>
                                {#if discovery.domain}
                                    <span class="discovery-domain">{discovery.domain}</span>
                                {/if}
                            </div>
                        {/each}
                    </div>
                </div>
            {:else}
                <div class="empty-state">
                    <div class="empty-icon">🌱</div>
                    <p>Your journey begins with a single observation...</p>
                </div>
            {/if}

            <!-- Connection Graph Placeholder -->
            {#if discoveries.length > 5}
                <div class="connection-graph">
                    <div class="section-label">Connection Map</div>
                    <div class="graph-preview">
                        <svg width="100%" height="150" viewBox="0 0 200 150">
                            <!-- Simple visualization: nodes connected by lines -->
                            {#each discoveries.slice(-6) as discovery, i}
                                {@const x = 30 + (i % 3) * 70}
                                {@const y = 40 + Math.floor(i / 3) * 70}

                                <!-- Connections -->
                                {#if discovery.relatedTo && discovery.relatedTo.length > 0}
                                    {#each discovery.relatedTo as relatedId}
                                        {@const relatedIndex = discoveries.findIndex(d => d.id === relatedId)}
                                        {#if relatedIndex >= discoveries.length - 6 && relatedIndex >= 0}
                                            {@const rx = 30 + ((relatedIndex % 6) % 3) * 70}
                                            {@const ry = 40 + Math.floor((relatedIndex % 6) / 3) * 70}
                                            <line
                                                x1={x} y1={y}
                                                x2={rx} y2={ry}
                                                stroke="#E8E0D0"
                                                stroke-width="1"
                                                opacity="0.5"
                                            />
                                        {/if}
                                    {/each}
                                {/if}

                                <!-- Node -->
                                <circle
                                    cx={x}
                                    cy={y}
                                    r="8"
                                    fill={discovery.type === 'theorem' ? '#C5A059' : '#4A6B52'}
                                    stroke="white"
                                    stroke-width="2"
                                />
                                <text
                                    x={x}
                                    y={y + 20}
                                    text-anchor="middle"
                                    font-size="8"
                                    fill="#8A8580"
                                >
                                    {getDiscoveryIcon(discovery.type)}
                                </text>
                            {/each}
                        </svg>
                        <div class="graph-hint">Click to explore full connection graph</div>
                    </div>
                </div>
            {/if}
        </div>
    {/if}
</aside>

<style>
    .discovery-journal {
        position: fixed;
        top: 0;
        right: 0;
        width: 320px;
        height: 100vh;
        background: rgba(255, 255, 255, 0.95);
        border-left: 1px solid #E8E0D0;
        overflow-y: auto;
        transition: transform 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
        z-index: 100;
        backdrop-filter: blur(8px);
    }

    .discovery-journal.collapsed {
        transform: translateX(calc(100% - 44px));
    }

    .toggle-btn {
        position: absolute;
        left: -44px;
        top: 50%;
        transform: translateY(-50%);
        width: 44px;
        height: 89px;
        background: rgba(255, 255, 255, 0.95);
        border: 1px solid #E8E0D0;
        border-right: none;
        border-radius: 13px 0 0 13px;
        display: flex;
        align-items: center;
        justify-content: center;
        cursor: pointer;
        color: #8A8580;
        transition: all 144ms ease;
    }

    .toggle-btn:hover {
        background: white;
        color: #C5A059;
    }

    .journal-content {
        padding: 21px;
        animation: fadeIn 233ms ease;
    }

    @keyframes fadeIn {
        from { opacity: 0; }
        to { opacity: 1; }
    }

    .journal-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 21px;
        padding-bottom: 13px;
        border-bottom: 1px solid #E8E0D0;
    }

    .journal-header h3 {
        font-family: 'Cinzel', serif;
        font-size: 20px;
        color: #3D3835;
        margin: 0;
    }

    .discovery-count {
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        color: #8A8580;
        background: #F5F0E6;
        padding: 4px 8px;
        border-radius: 8px;
    }

    .section-label {
        font-family: 'Outfit', sans-serif;
        font-size: 11px;
        font-weight: 600;
        color: #8A8580;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        margin-bottom: 8px;
    }

    /* Current Path */
    .current-path {
        margin-bottom: 21px;
        padding: 13px;
        background: rgba(74, 107, 82, 0.05);
        border-radius: 8px;
        border-left: 3px solid #4A6B52;
    }

    .path-label {
        font-family: 'Outfit', sans-serif;
        font-size: 11px;
        font-weight: 600;
        color: #4A6B52;
        margin-bottom: 8px;
    }

    .breadcrumbs {
        display: flex;
        flex-wrap: wrap;
        gap: 5px;
        align-items: center;
        font-size: 12px;
    }

    .breadcrumb {
        color: #5A5550;
        padding: 2px 6px;
        border-radius: 4px;
        background: rgba(255, 255, 255, 0.8);
    }

    .breadcrumb.active {
        background: #4A6B52;
        color: white;
        font-weight: 500;
    }

    .separator {
        color: #A8A098;
        font-size: 10px;
    }

    /* Domains */
    .domains-explored {
        margin-bottom: 21px;
    }

    .domain-tags {
        display: flex;
        flex-wrap: wrap;
        gap: 5px;
    }

    .domain-tag {
        font-family: 'Outfit', sans-serif;
        font-size: 11px;
        padding: 4px 8px;
        background: #F5F0E6;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        color: #5A5550;
    }

    /* Milestones */
    .milestones {
        margin-bottom: 21px;
    }

    .milestone-grid {
        display: grid;
        grid-template-columns: 1fr;
        gap: 8px;
    }

    .milestone {
        display: flex;
        align-items: center;
        gap: 8px;
        padding: 8px;
        background: #F5F0E6;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        opacity: 0.5;
        transition: all 233ms ease;
        cursor: help;
    }

    .milestone.achieved {
        opacity: 1;
        background: rgba(197, 160, 89, 0.1);
        border-color: #C5A059;
    }

    .milestone-icon {
        font-size: 16px;
        filter: grayscale(1);
        transition: filter 233ms ease;
    }

    .milestone.achieved .milestone-icon {
        filter: grayscale(0);
        animation: pop 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes pop {
        0% { transform: scale(1); }
        50% { transform: scale(1.3); }
        100% { transform: scale(1); }
    }

    .milestone-name {
        font-family: 'Outfit', sans-serif;
        font-size: 12px;
        color: #5A5550;
    }

    /* Discoveries */
    .recent-discoveries {
        margin-bottom: 21px;
    }

    .discoveries-list {
        display: flex;
        flex-direction: column;
        gap: 8px;
    }

    .discovery-item {
        padding: 13px;
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        transition: all 144ms ease;
        animation: slideIn 377ms cubic-bezier(0.4, 0.0, 0.2, 1);
    }

    @keyframes slideIn {
        from {
            opacity: 0;
            transform: translateX(13px);
        }
        to {
            opacity: 1;
            transform: translateX(0);
        }
    }

    .discovery-item:hover {
        box-shadow: 0 2px 8px rgba(0, 0, 0, 0.08);
        transform: translateX(-2px);
    }

    .discovery-item[data-type="theorem"] {
        border-left: 3px solid #C5A059;
    }

    .discovery-item[data-type="insight"] {
        border-left: 3px solid #4A6B52;
    }

    .discovery-header {
        display: flex;
        align-items: center;
        gap: 5px;
        margin-bottom: 5px;
    }

    .discovery-icon {
        font-size: 14px;
    }

    .discovery-type {
        font-family: 'Outfit', sans-serif;
        font-size: 10px;
        font-weight: 600;
        color: #8A8580;
        text-transform: uppercase;
        letter-spacing: 0.05em;
        flex: 1;
    }

    .discovery-time {
        font-family: 'Outfit', sans-serif;
        font-size: 10px;
        color: #A8A098;
    }

    .discovery-content {
        font-family: 'Lora', serif;
        font-size: 13px;
        line-height: 1.5;
        color: #3D3835;
        margin-bottom: 5px;
    }

    .discovery-domain {
        font-family: 'Outfit', sans-serif;
        font-size: 10px;
        color: #C5A059;
        background: rgba(197, 160, 89, 0.1);
        padding: 2px 6px;
        border-radius: 4px;
    }

    /* Empty State */
    .empty-state {
        text-align: center;
        padding: 34px 13px;
        color: #8A8580;
    }

    .empty-icon {
        font-size: 48px;
        margin-bottom: 13px;
        opacity: 0.5;
    }

    .empty-state p {
        font-family: 'Lora', serif;
        font-size: 14px;
        font-style: italic;
        line-height: 1.5;
    }

    /* Connection Graph */
    .connection-graph {
        margin-top: 21px;
        padding-top: 21px;
        border-top: 1px solid #E8E0D0;
    }

    .graph-preview {
        background: white;
        border: 1px solid #E8E0D0;
        border-radius: 8px;
        padding: 13px;
        cursor: pointer;
        transition: all 144ms ease;
    }

    .graph-preview:hover {
        box-shadow: 0 2px 8px rgba(0, 0, 0, 0.08);
    }

    .graph-hint {
        font-family: 'Outfit', sans-serif;
        font-size: 10px;
        color: #A8A098;
        text-align: center;
        margin-top: 8px;
    }

    /* Scrollbar */
    .discovery-journal::-webkit-scrollbar {
        width: 6px;
    }

    .discovery-journal::-webkit-scrollbar-track {
        background: rgba(245, 240, 230, 0.3);
    }

    .discovery-journal::-webkit-scrollbar-thumb {
        background: #E8E0D0;
        border-radius: 3px;
    }

    .discovery-journal::-webkit-scrollbar-thumb:hover {
        background: #C5A059;
    }

    /* Responsive */
    @media (max-width: 768px) {
        .discovery-journal {
            width: 280px;
        }

        .discovery-journal.collapsed {
            transform: translateX(100%);
        }

        .toggle-btn {
            left: auto;
            right: 0;
            border-radius: 13px 0 0 13px;
        }
    }
</style>
