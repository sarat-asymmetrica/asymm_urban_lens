/** @type {import('tailwindcss').Config} */
export default {
  content: ['./src/**/*.{html,js,svelte,ts}'],
  theme: {
    extend: {
      colors: {
        // φ-based color palette (golden ratio harmony)
        'phi-primary': '#1a1a2e',
        'phi-secondary': '#16213e',
        'phi-accent': '#0f3460',
        'phi-highlight': '#e94560',
        'phi-text': '#eaeaea',
        'phi-muted': '#a0a0a0',
        // Research-appropriate colors
        'research-bg': '#0d1117',
        'research-card': '#161b22',
        'research-border': '#30363d',
        'research-text': '#c9d1d9',
        'research-accent': '#58a6ff',
      },
      fontFamily: {
        'sans': ['Inter', 'system-ui', 'sans-serif'],
        'mono': ['JetBrains Mono', 'Fira Code', 'monospace'],
      },
      animation: {
        'fade-in': 'fadeIn 0.3s ease-out',
        'slide-up': 'slideUp 0.4s ease-out',
        'pulse-soft': 'pulseSoft 2s ease-in-out infinite',
        'typing': 'typing 1s ease-in-out infinite',
      },
      keyframes: {
        fadeIn: {
          '0%': { opacity: '0' },
          '100%': { opacity: '1' },
        },
        slideUp: {
          '0%': { opacity: '0', transform: 'translateY(10px)' },
          '100%': { opacity: '1', transform: 'translateY(0)' },
        },
        pulseSoft: {
          '0%, 100%': { opacity: '1' },
          '50%': { opacity: '0.7' },
        },
        typing: {
          '0%, 100%': { opacity: '1' },
          '50%': { opacity: '0.3' },
        },
      },
      spacing: {
        // Fibonacci spacing
        'fib-1': '1px',
        'fib-2': '2px',
        'fib-3': '3px',
        'fib-5': '5px',
        'fib-8': '8px',
        'fib-13': '13px',
        'fib-21': '21px',
        'fib-34': '34px',
        'fib-55': '55px',
        'fib-89': '89px',
      },
    },
  },
  plugins: [],
}
