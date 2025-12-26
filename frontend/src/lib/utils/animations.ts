/**
 * GSAP Animation Utilities for Urban Lens
 * φ-based timing and easing for natural, research-appropriate motion
 */
import { gsap } from 'gsap';

// Golden ratio timing constants
const PHI = 1.618033988749;
const DURATION_FAST = 0.233;  // Fibonacci-based
const DURATION_NORMAL = 0.377;
const DURATION_SLOW = 0.610;

// Custom easing based on φ
const phiEase = `power2.out`;

/**
 * Fade in an element with slide up motion
 */
export function fadeInUp(element: HTMLElement, delay = 0): gsap.core.Tween {
    return gsap.fromTo(element,
        { opacity: 0, y: 20 },
        { 
            opacity: 1, 
            y: 0, 
            duration: DURATION_NORMAL,
            delay,
            ease: phiEase
        }
    );
}

/**
 * Fade in an element
 */
export function fadeIn(element: HTMLElement, delay = 0): gsap.core.Tween {
    return gsap.fromTo(element,
        { opacity: 0 },
        { 
            opacity: 1, 
            duration: DURATION_FAST,
            delay,
            ease: phiEase
        }
    );
}

/**
 * Stagger fade in for multiple elements
 */
export function staggerFadeIn(elements: HTMLElement[], staggerDelay = 0.089): gsap.core.Tween {
    return gsap.fromTo(elements,
        { opacity: 0, y: 10 },
        { 
            opacity: 1, 
            y: 0, 
            duration: DURATION_NORMAL,
            stagger: staggerDelay,
            ease: phiEase
        }
    );
}

/**
 * Typing indicator pulse animation
 */
export function typingPulse(element: HTMLElement): gsap.core.Tween {
    return gsap.to(element, {
        opacity: 0.3,
        duration: 0.5,
        repeat: -1,
        yoyo: true,
        ease: 'sine.inOut'
    });
}

/**
 * Phase transition animation (for reasoning phases)
 */
export function phaseTransition(
    outElement: HTMLElement | null, 
    inElement: HTMLElement
): gsap.core.Timeline {
    const tl = gsap.timeline();
    
    if (outElement) {
        tl.to(outElement, {
            opacity: 0,
            x: -10,
            duration: DURATION_FAST,
            ease: 'power2.in'
        });
    }
    
    tl.fromTo(inElement,
        { opacity: 0, x: 10 },
        { 
            opacity: 1, 
            x: 0, 
            duration: DURATION_NORMAL,
            ease: phiEase
        }
    );
    
    return tl;
}

/**
 * Breathing animation (φ-based 8-second cycle)
 */
export function breathe(element: HTMLElement): gsap.core.Tween {
    return gsap.to(element, {
        scale: 1.008,
        opacity: 1,
        duration: 4,
        repeat: -1,
        yoyo: true,
        ease: 'sine.inOut'
    });
}

/**
 * Subtle glow pulse for active elements
 */
export function glowPulse(element: HTMLElement): gsap.core.Tween {
    return gsap.to(element, {
        boxShadow: '0 0 21px 8px rgba(197, 160, 89, 0.15)',
        duration: 4,
        repeat: -1,
        yoyo: true,
        ease: 'sine.inOut'
    });
}

/**
 * Message appear animation
 */
export function messageAppear(element: HTMLElement, isUser: boolean): gsap.core.Tween {
    const xOffset = isUser ? 20 : -20;
    
    return gsap.fromTo(element,
        { opacity: 0, x: xOffset, scale: 0.98 },
        { 
            opacity: 1, 
            x: 0, 
            scale: 1,
            duration: DURATION_NORMAL,
            ease: 'back.out(1.2)'
        }
    );
}

/**
 * Scroll to element smoothly
 */
export function scrollToElement(container: HTMLElement, target: HTMLElement): void {
    gsap.to(container, {
        scrollTop: target.offsetTop,
        duration: DURATION_SLOW,
        ease: 'power2.out'
    });
}

/**
 * Kill all animations on an element
 */
export function killAnimations(element: HTMLElement): void {
    gsap.killTweensOf(element);
}
