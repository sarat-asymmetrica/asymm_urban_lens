/**
 * WebSocket Store - Real-time connection to UrbanLens backend
 * Provides streaming conversation updates with "Her"-style responsiveness
 */

import { writable, derived } from 'svelte/store';

export type ConnectionStatus = 'disconnected' | 'connecting' | 'connected' | 'error';

export type ReasoningPhase = 'intake' | 'analysis' | 'synthesis' | 'insight' | 'complete';

export interface StreamMessage {
    type: 'phase_update' | 'thinking' | 'response' | 'error' | 'complete';
    phase?: ReasoningPhase;
    content?: string;
    timestamp?: string;
}

export interface ConversationMessage {
    id: string;
    role: 'user' | 'assistant';
    content: string;
    timestamp: Date;
    phase?: ReasoningPhase;
    isStreaming?: boolean;
}

// Connection state
export const connectionStatus = writable<ConnectionStatus>('disconnected');
export const currentPhase = writable<ReasoningPhase>('intake');
export const streamingContent = writable<string>('');
export const conversations = writable<ConversationMessage[]>([]);

// WebSocket instance (stored globally)
let ws: WebSocket | null = null;
let reconnectTimer: number | null = null;

/**
 * Connect to UrbanLens WebSocket server
 */
export function connect(url: string = 'ws://localhost:8080/ws') {
    if (ws?.readyState === WebSocket.OPEN) {
        console.log('WebSocket already connected');
        return;
    }

    connectionStatus.set('connecting');

    try {
        ws = new WebSocket(url);

        ws.onopen = () => {
            console.log('✅ Connected to UrbanLens');
            connectionStatus.set('connected');
            if (reconnectTimer) {
                clearTimeout(reconnectTimer);
                reconnectTimer = null;
            }
        };

        ws.onmessage = (event) => {
            try {
                const message: StreamMessage = JSON.parse(event.data);
                handleMessage(message);
            } catch (error) {
                console.error('Failed to parse message:', error);
            }
        };

        ws.onerror = (error) => {
            console.error('WebSocket error:', error);
            connectionStatus.set('error');
        };

        ws.onclose = () => {
            console.log('WebSocket closed, will reconnect...');
            connectionStatus.set('disconnected');

            // Auto-reconnect after 2 seconds
            reconnectTimer = window.setTimeout(() => {
                connect(url);
            }, 2000);
        };

    } catch (error) {
        console.error('Failed to connect:', error);
        connectionStatus.set('error');
    }
}

/**
 * Handle incoming WebSocket messages
 */
function handleMessage(message: StreamMessage) {
    switch (message.type) {
        case 'phase_update':
            if (message.phase) {
                currentPhase.set(message.phase);
            }
            break;

        case 'thinking':
        case 'response':
            // Accumulate streaming content
            if (message.content) {
                streamingContent.update(current => current + message.content);
            }
            break;

        case 'complete':
            // Finalize the assistant message
            streamingContent.update(current => {
                const finalContent = current;

                conversations.update(msgs => [
                    ...msgs,
                    {
                        id: crypto.randomUUID(),
                        role: 'assistant',
                        content: finalContent,
                        timestamp: new Date(),
                        phase: message.phase,
                        isStreaming: false
                    }
                ]);

                return ''; // Clear streaming content
            });

            currentPhase.set('complete');
            break;

        case 'error':
            console.error('Error from server:', message.content);
            conversations.update(msgs => [
                ...msgs,
                {
                    id: crypto.randomUUID(),
                    role: 'assistant',
                    content: `Error: ${message.content}`,
                    timestamp: new Date(),
                    isStreaming: false
                }
            ]);
            streamingContent.set('');
            break;
    }
}

/**
 * Send a message to the backend
 */
export function sendMessage(content: string) {
    if (!ws || ws.readyState !== WebSocket.OPEN) {
        console.error('WebSocket not connected');
        return;
    }

    // Add user message to conversation
    conversations.update(msgs => [
        ...msgs,
        {
            id: crypto.randomUUID(),
            role: 'user',
            content,
            timestamp: new Date()
        }
    ]);

    // Send to backend
    const message = {
        type: 'query',
        input: content,
        timestamp: new Date().toISOString()
    };

    ws.send(JSON.stringify(message));

    // Reset streaming state
    streamingContent.set('');
    currentPhase.set('intake');
}

/**
 * Disconnect WebSocket
 */
export function disconnect() {
    if (ws) {
        ws.close();
        ws = null;
    }

    if (reconnectTimer) {
        clearTimeout(reconnectTimer);
        reconnectTimer = null;
    }

    connectionStatus.set('disconnected');
}

/**
 * Clear conversation history
 */
export function clearConversation() {
    conversations.set([]);
    streamingContent.set('');
    currentPhase.set('intake');
}

// Derived store: is currently streaming?
export const isStreaming = derived(
    streamingContent,
    $content => $content.length > 0
);
