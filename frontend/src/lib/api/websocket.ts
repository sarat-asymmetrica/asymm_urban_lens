/**
 * AsyaWebSocket - Enhanced WebSocket client for Asya conversation engine
 * Provides streaming responses, phase tracking, discovery events, and visualization
 */

import { writable, get } from 'svelte/store';
import type { Writable } from 'svelte/store';

export type ConnectionStatus = 'disconnected' | 'connecting' | 'connected' | 'error';

export type ConversationState =
    | 'GREETING'
    | 'ANCHORING'
    | 'WHY_CHAINING'
    | 'SYNTHESIZING'
    | 'FORMALIZING'
    | 'CELEBRATING';

export type VoidFlowPhase = 'VOID' | 'FLOW' | 'SOLUTION';

export interface Discovery {
    id: string;
    type: 'observation' | 'insight' | 'connection' | 'theorem' | 'milestone';
    content: string;
    timestamp: Date;
    domain?: string;
    relatedTo?: string[];
}

export interface LeanProof {
    id: string;
    theorem: string;
    code: string;
    status: 'pending' | 'verifying' | 'verified' | 'error';
    error?: string;
    timestamp: Date;
}

export interface VisualizationResult {
    imageUrl: string;
    caption: string;
    concept: string;
    timestamp: Date;
}

export interface AsyaMessage {
    action: string;
    session_id?: string;
    message?: string;
    concept?: string;
    [key: string]: any;
}

export interface AsyaEvent {
    type: string;
    session_id?: string;
    token?: string;
    phase?: VoidFlowPhase;
    state?: ConversationState;
    discovery?: Discovery;
    proof?: LeanProof;
    visualization?: VisualizationResult;
    error?: string;
    [key: string]: any;
}

export class AsyaWebSocket {
    private ws: WebSocket | null = null;
    private url: string;
    private reconnectTimer: number | null = null;
    private reconnectAttempts: number = 0;
    private maxReconnectAttempts: number = 10;

    // Stores
    public connectionStatus: Writable<ConnectionStatus> = writable('disconnected');
    public sessionId: Writable<string | null> = writable(null);
    public currentPhase: Writable<VoidFlowPhase> = writable('VOID');
    public currentState: Writable<ConversationState> = writable('GREETING');
    public streamingContent: Writable<string> = writable('');
    public discoveries: Writable<Discovery[]> = writable([]);
    public proofs: Writable<LeanProof[]> = writable([]);

    // Callbacks
    private tokenCallbacks: Set<(token: string) => void> = new Set();
    private phaseChangeCallbacks: Set<(phase: VoidFlowPhase) => void> = new Set();
    private stateChangeCallbacks: Set<(state: ConversationState) => void> = new Set();
    private discoveryCallbacks: Set<(discovery: Discovery) => void> = new Set();
    private proofCallbacks: Set<(proof: LeanProof) => void> = new Set();
    private imageCallbacks: Set<(result: VisualizationResult) => void> = new Set();
    private completeCallbacks: Set<() => void> = new Set();
    private errorCallbacks: Set<(error: string) => void> = new Set();

    constructor(url: string = 'ws://localhost:8080/ws') {
        this.url = url;
    }

    /**
     * Connect to WebSocket server
     */
    connect(sessionId?: string): Promise<void> {
        return new Promise((resolve, reject) => {
            if (this.ws?.readyState === WebSocket.OPEN) {
                console.log('Already connected');
                resolve();
                return;
            }

            this.connectionStatus.set('connecting');

            try {
                this.ws = new WebSocket(this.url);

                this.ws.onopen = () => {
                    console.log('✅ Connected to Asya');
                    this.connectionStatus.set('connected');
                    this.reconnectAttempts = 0;

                    if (this.reconnectTimer) {
                        clearTimeout(this.reconnectTimer);
                        this.reconnectTimer = null;
                    }

                    // Create or resume session
                    if (sessionId) {
                        this.sessionId.set(sessionId);
                    } else {
                        this.createSession();
                    }

                    resolve();
                };

                this.ws.onmessage = (event) => {
                    try {
                        const eventData: AsyaEvent = JSON.parse(event.data);
                        this.handleEvent(eventData);
                    } catch (error) {
                        console.error('Failed to parse event:', error);
                    }
                };

                this.ws.onerror = (error) => {
                    console.error('WebSocket error:', error);
                    this.connectionStatus.set('error');
                    reject(error);
                };

                this.ws.onclose = () => {
                    console.log('WebSocket closed');
                    this.connectionStatus.set('disconnected');
                    this.attemptReconnect();
                };
            } catch (error) {
                console.error('Failed to connect:', error);
                this.connectionStatus.set('error');
                reject(error);
            }
        });
    }

    /**
     * Disconnect from server
     */
    disconnect(): void {
        if (this.ws) {
            this.ws.close();
            this.ws = null;
        }

        if (this.reconnectTimer) {
            clearTimeout(this.reconnectTimer);
            this.reconnectTimer = null;
        }

        this.connectionStatus.set('disconnected');
        this.reconnectAttempts = 0;
    }

    /**
     * Attempt to reconnect
     */
    private attemptReconnect(): void {
        if (this.reconnectAttempts >= this.maxReconnectAttempts) {
            console.error('Max reconnect attempts reached');
            this.connectionStatus.set('error');
            return;
        }

        const delay = Math.min(1000 * Math.pow(2, this.reconnectAttempts), 30000);
        this.reconnectAttempts++;

        console.log(`Reconnecting in ${delay}ms (attempt ${this.reconnectAttempts})`);

        this.reconnectTimer = window.setTimeout(() => {
            const currentSessionId = get(this.sessionId);
            this.connect(currentSessionId || undefined);
        }, delay);
    }

    /**
     * Create new conversation session
     */
    private createSession(): void {
        this.send({
            action: 'create_session'
        });
    }

    /**
     * Send message to Asya
     */
    sendMessage(content: string): void {
        const sessionId = get(this.sessionId);

        if (!sessionId) {
            console.error('No active session');
            return;
        }

        this.send({
            action: 'send_message',
            session_id: sessionId,
            message: content
        });

        // Reset streaming content
        this.streamingContent.set('');
    }

    /**
     * Request a hint
     */
    requestHint(): void {
        const sessionId = get(this.sessionId);

        if (!sessionId) {
            console.error('No active session');
            return;
        }

        this.send({
            action: 'request_hint',
            session_id: sessionId
        });
    }

    /**
     * Request visualization
     */
    requestVisualization(concept: string): void {
        const sessionId = get(this.sessionId);

        if (!sessionId) {
            console.error('No active session');
            return;
        }

        this.send({
            action: 'visualize',
            session_id: sessionId,
            concept
        });
    }

    /**
     * Send generic message
     */
    private send(message: AsyaMessage): void {
        if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
            console.error('WebSocket not connected');
            return;
        }

        this.ws.send(JSON.stringify(message));
    }

    /**
     * Handle incoming events
     */
    private handleEvent(event: AsyaEvent): void {
        switch (event.type) {
            case 'welcome':
                if (event.session_id) {
                    this.sessionId.set(event.session_id);
                }
                break;

            case 'token':
                if (event.token) {
                    this.streamingContent.update((content) => content + event.token);
                    this.tokenCallbacks.forEach((cb) => cb(event.token!));
                }
                break;

            case 'phase_change':
                if (event.phase) {
                    this.currentPhase.set(event.phase);
                    this.phaseChangeCallbacks.forEach((cb) => cb(event.phase!));
                }
                break;

            case 'state_change':
                if (event.state) {
                    this.currentState.set(event.state);
                    this.stateChangeCallbacks.forEach((cb) => cb(event.state!));
                }
                break;

            case 'discovery':
                if (event.discovery) {
                    const discovery: Discovery = {
                        ...event.discovery,
                        timestamp: new Date(event.discovery.timestamp)
                    };
                    this.discoveries.update((list) => [...list, discovery]);
                    this.discoveryCallbacks.forEach((cb) => cb(discovery));
                }
                break;

            case 'proof':
                if (event.proof) {
                    const proof: LeanProof = {
                        ...event.proof,
                        timestamp: new Date(event.proof.timestamp)
                    };
                    this.proofs.update((list) => {
                        const existing = list.findIndex((p) => p.id === proof.id);
                        if (existing >= 0) {
                            list[existing] = proof;
                            return [...list];
                        } else {
                            return [...list, proof];
                        }
                    });
                    this.proofCallbacks.forEach((cb) => cb(proof));
                }
                break;

            case 'visualization':
                if (event.visualization) {
                    const result: VisualizationResult = {
                        ...event.visualization,
                        timestamp: new Date()
                    };
                    this.imageCallbacks.forEach((cb) => cb(result));
                }
                break;

            case 'complete':
                this.streamingContent.set('');
                this.completeCallbacks.forEach((cb) => cb());
                break;

            case 'error':
                const errorMsg = event.error || 'Unknown error';
                console.error('Server error:', errorMsg);
                this.errorCallbacks.forEach((cb) => cb(errorMsg));
                break;

            default:
                console.log('Unknown event type:', event.type);
        }
    }

    // Callback registration methods

    onToken(callback: (token: string) => void): () => void {
        this.tokenCallbacks.add(callback);
        return () => this.tokenCallbacks.delete(callback);
    }

    onPhaseChange(callback: (phase: VoidFlowPhase) => void): () => void {
        this.phaseChangeCallbacks.add(callback);
        return () => this.phaseChangeCallbacks.delete(callback);
    }

    onStateChange(callback: (state: ConversationState) => void): () => void {
        this.stateChangeCallbacks.add(callback);
        return () => this.stateChangeCallbacks.delete(callback);
    }

    onDiscovery(callback: (discovery: Discovery) => void): () => void {
        this.discoveryCallbacks.add(callback);
        return () => this.discoveryCallbacks.delete(callback);
    }

    onProof(callback: (proof: LeanProof) => void): () => void {
        this.proofCallbacks.add(callback);
        return () => this.proofCallbacks.delete(callback);
    }

    onImage(callback: (result: VisualizationResult) => void): () => void {
        this.imageCallbacks.add(callback);
        return () => this.imageCallbacks.delete(callback);
    }

    onComplete(callback: () => void): () => void {
        this.completeCallbacks.add(callback);
        return () => this.completeCallbacks.delete(callback);
    }

    onError(callback: (error: string) => void): () => void {
        this.errorCallbacks.add(callback);
        return () => this.errorCallbacks.delete(callback);
    }
}

// Export singleton instance
export const asyaWebSocket = new AsyaWebSocket();
