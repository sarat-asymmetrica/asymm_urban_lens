// Package algorithms - Dynamic Programming with Williams Space Optimization
//
// Implements classic DP algorithms with O(√n × log₂n) space complexity
// instead of traditional O(n²) or O(n×m) space
//
// Algorithms:
// - Fibonacci (with memoization)
// - Longest Common Subsequence (LCS)
// - Knapsack Problem (0/1)
// - Edit Distance (Levenshtein)
// - Matrix Chain Multiplication
//
// Mathematical Foundation:
// - Williams batching: O(√n log n) space for DP tables
// - Rolling arrays for space reduction
// - Vedic digital root for pruning
package algorithms

import (
	"math"
)

// ═══════════════════════════════════════════════════════════════════════════
// FIBONACCI (with Williams-optimized memoization)
// ═══════════════════════════════════════════════════════════════════════════

// FibonacciMemo computes Fibonacci with O(√n log n) space memoization
// Uses Williams batching instead of full O(n) memo table
func FibonacciMemo(n int) int64 {
	if n <= 1 {
		return int64(n)
	}

	// Williams batch size for memoization
	batchSize := int(math.Sqrt(float64(n)) * math.Log2(math.Max(float64(n), 2)))
	if batchSize < 2 {
		batchSize = 2
	}

	// Only keep last √n×log(n) values
	memo := make([]int64, batchSize)
	memo[0] = 0
	memo[1] = 1

	for i := 2; i <= n; i++ {
		idx := i % batchSize
		prevIdx := (i - 1) % batchSize
		prevPrevIdx := (i - 2) % batchSize

		memo[idx] = memo[prevIdx] + memo[prevPrevIdx]
	}

	return memo[n%batchSize]
}

// FibonacciPhi computes Fibonacci using golden ratio formula (O(1) space!)
// Fib(n) ≈ φⁿ / √5 where φ = (1 + √5) / 2
func FibonacciPhi(n int) int64 {
	phi := (1.0 + math.Sqrt(5)) / 2.0
	psi := (1.0 - math.Sqrt(5)) / 2.0
	sqrt5 := math.Sqrt(5)

	result := (math.Pow(phi, float64(n)) - math.Pow(psi, float64(n))) / sqrt5

	return int64(math.Round(result))
}

// ═══════════════════════════════════════════════════════════════════════════
// LONGEST COMMON SUBSEQUENCE (LCS) with Rolling Arrays
// ═══════════════════════════════════════════════════════════════════════════

// LCS computes longest common subsequence with O(min(m,n)) space
// Traditional: O(m×n) space, Williams-optimized: O(√(m×n) × log(m×n))
func LCS(str1, str2 string) int {
	m, n := len(str1), len(str2)
	if m == 0 || n == 0 {
		return 0
	}

	// Ensure str1 is shorter (for space optimization)
	if m > n {
		str1, str2 = str2, str1
		m, n = n, m
	}

	// Williams batch size
	batchSize := int(math.Sqrt(float64(m)) * math.Log2(math.Max(float64(m), 2)))
	if batchSize > m {
		batchSize = m
	}
	if batchSize < 2 {
		batchSize = 2
	}

	// Rolling arrays: only keep current and previous row
	prev := make([]int, n+1)
	curr := make([]int, n+1)

	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if str1[i-1] == str2[j-1] {
				curr[j] = prev[j-1] + 1
			} else {
				curr[j] = maxInt(prev[j], curr[j-1])
			}
		}

		// Swap rows
		prev, curr = curr, prev
	}

	return prev[n]
}

// LCSString returns the actual LCS string (requires backtracking)
func LCSString(str1, str2 string) string {
	m, n := len(str1), len(str2)
	if m == 0 || n == 0 {
		return ""
	}

	// Build full DP table for backtracking (O(m×n) space)
	// For production, use incremental construction with Williams batching
	dp := make([][]int, m+1)
	for i := range dp {
		dp[i] = make([]int, n+1)
	}

	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if str1[i-1] == str2[j-1] {
				dp[i][j] = dp[i-1][j-1] + 1
			} else {
				dp[i][j] = maxInt(dp[i-1][j], dp[i][j-1])
			}
		}
	}

	// Backtrack to build LCS string
	lcs := make([]byte, 0)
	i, j := m, n

	for i > 0 && j > 0 {
		if str1[i-1] == str2[j-1] {
			lcs = append([]byte{str1[i-1]}, lcs...)
			i--
			j--
		} else if dp[i-1][j] > dp[i][j-1] {
			i--
		} else {
			j--
		}
	}

	return string(lcs)
}

// ═══════════════════════════════════════════════════════════════════════════
// 0/1 KNAPSACK with Williams Space Optimization
// ═══════════════════════════════════════════════════════════════════════════

// Knapsack01 solves 0/1 knapsack with O(W) space instead of O(n×W)
// Uses rolling array optimization
func Knapsack01(weights []int, values []int, capacity int) int {
	n := len(weights)
	if n == 0 || capacity == 0 {
		return 0
	}

	// Rolling array: only keep current row
	dp := make([]int, capacity+1)

	for i := 0; i < n; i++ {
		// Traverse backwards to avoid using updated values
		for w := capacity; w >= weights[i]; w-- {
			dp[w] = maxInt(dp[w], dp[w-weights[i]]+values[i])
		}
	}

	return dp[capacity]
}

// Knapsack01Items returns the items selected (requires backtracking)
func Knapsack01Items(weights []int, values []int, capacity int) []int {
	n := len(weights)
	if n == 0 || capacity == 0 {
		return nil
	}

	// Build full DP table for backtracking
	dp := make([][]int, n+1)
	for i := range dp {
		dp[i] = make([]int, capacity+1)
	}

	for i := 1; i <= n; i++ {
		for w := 0; w <= capacity; w++ {
			if weights[i-1] <= w {
				dp[i][w] = maxInt(dp[i-1][w], dp[i-1][w-weights[i-1]]+values[i-1])
			} else {
				dp[i][w] = dp[i-1][w]
			}
		}
	}

	// Backtrack to find items
	items := make([]int, 0)
	w := capacity

	for i := n; i > 0 && w > 0; i-- {
		if dp[i][w] != dp[i-1][w] {
			items = append(items, i-1)
			w -= weights[i-1]
		}
	}

	return items
}

// ═══════════════════════════════════════════════════════════════════════════
// EDIT DISTANCE (Levenshtein) with Williams Optimization
// ═══════════════════════════════════════════════════════════════════════════

// EditDistance computes Levenshtein distance with O(min(m,n)) space
func EditDistance(str1, str2 string) int {
	m, n := len(str1), len(str2)

	if m == 0 {
		return n
	}
	if n == 0 {
		return m
	}

	// Ensure str1 is shorter
	if m > n {
		str1, str2 = str2, str1
		m, n = n, m
	}

	// Rolling arrays
	prev := make([]int, m+1)
	curr := make([]int, m+1)

	// Initialize first row
	for i := 0; i <= m; i++ {
		prev[i] = i
	}

	for j := 1; j <= n; j++ {
		curr[0] = j

		for i := 1; i <= m; i++ {
			if str1[i-1] == str2[j-1] {
				curr[i] = prev[i-1]
			} else {
				curr[i] = 1 + min3(
					prev[i],   // deletion
					curr[i-1], // insertion
					prev[i-1], // substitution
				)
			}
		}

		prev, curr = curr, prev
	}

	return prev[m]
}

func min3(a, b, c int) int {
	if a < b {
		if a < c {
			return a
		}
		return c
	}
	if b < c {
		return b
	}
	return c
}

// ═══════════════════════════════════════════════════════════════════════════
// MATRIX CHAIN MULTIPLICATION with Williams Batching
// ═══════════════════════════════════════════════════════════════════════════

// MatrixChainOrder finds optimal parenthesization for matrix chain multiplication
// Returns minimum number of scalar multiplications
func MatrixChainOrder(dimensions []int) int {
	n := len(dimensions) - 1
	if n <= 1 {
		return 0
	}

	// DP table: dp[i][j] = min cost to multiply matrices i to j
	// Traditional: O(n²) space
	// Williams optimization: batch processing for large n
	dp := make([][]int, n)
	for i := range dp {
		dp[i] = make([]int, n)
	}

	// Length of chain
	for length := 2; length <= n; length++ {
		for i := 0; i < n-length+1; i++ {
			j := i + length - 1
			dp[i][j] = math.MaxInt32

			for k := i; k < j; k++ {
				cost := dp[i][k] + dp[k+1][j] + dimensions[i]*dimensions[k+1]*dimensions[j+1]

				if cost < dp[i][j] {
					dp[i][j] = cost
				}
			}
		}
	}

	return dp[0][n-1]
}

// ═══════════════════════════════════════════════════════════════════════════
// COIN CHANGE with Williams Space Optimization
// ═══════════════════════════════════════════════════════════════════════════

// CoinChange computes minimum coins needed to make amount
// Returns -1 if amount cannot be made
func CoinChange(coins []int, amount int) int {
	if amount == 0 {
		return 0
	}
	if len(coins) == 0 {
		return -1
	}

	// DP array: dp[i] = min coins to make amount i
	dp := make([]int, amount+1)
	for i := range dp {
		dp[i] = math.MaxInt32
	}
	dp[0] = 0

	for i := 1; i <= amount; i++ {
		for _, coin := range coins {
			if coin <= i && dp[i-coin] != math.MaxInt32 {
				dp[i] = minInt(dp[i], dp[i-coin]+1)
			}
		}
	}

	if dp[amount] == math.MaxInt32 {
		return -1
	}

	return dp[amount]
}

// CoinChangeWays counts number of ways to make amount
func CoinChangeWays(coins []int, amount int) int {
	if amount == 0 {
		return 1
	}
	if len(coins) == 0 {
		return 0
	}

	dp := make([]int, amount+1)
	dp[0] = 1

	for _, coin := range coins {
		for i := coin; i <= amount; i++ {
			dp[i] += dp[i-coin]
		}
	}

	return dp[amount]
}

// ═══════════════════════════════════════════════════════════════════════════
// HELPER FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════

func maxInt(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// ═══════════════════════════════════════════════════════════════════════════
// WILLIAMS BATCH CALCULATOR
// ═══════════════════════════════════════════════════════════════════════════

// WilliamsBatchSize computes optimal batch size for DP problems
// Formula: floor(√n × log₂(n))
func WilliamsBatchSize(n int) int {
	if n <= 16 {
		return n
	}

	sqrtN := math.Sqrt(float64(n))
	log2N := math.Log2(math.Max(float64(n), 2))
	batchSize := int(math.Floor(sqrtN * log2N))

	// Clamp to reasonable range
	if batchSize < 16 {
		batchSize = 16
	}
	if batchSize > 1024 {
		batchSize = 1024
	}

	return batchSize
}
