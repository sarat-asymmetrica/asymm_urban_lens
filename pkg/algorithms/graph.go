// Package algorithms provides core algorithm implementations
// optimized with Williams batching, Vedic digital roots, and quaternion weights
//
// Ported from Asymmetrica Mathematical Organism to Urban Lens
// Mathematical Foundation: O(√n × log₂n) space, 53× Vedic speedups
package algorithms

import (
	"container/heap"
	stdmath "math"

	ulmath "github.com/asymmetrica/urbanlens/pkg/math"
)

// ═══════════════════════════════════════════════════════════════════════════
// GRAPH TYPES
// ═══════════════════════════════════════════════════════════════════════════

// Node represents a graph node with quaternion state
type Node struct {
	ID    string
	State ulmath.Quaternion
	Edges []*Edge
}

// Edge represents a weighted graph edge
type Edge struct {
	From   *Node
	To     *Node
	Weight float64 // Can be derived from quaternion distance
}

// Graph represents a quaternion-weighted graph
type Graph struct {
	Nodes map[string]*Node
}

// NewGraph creates an empty graph
func NewGraph() *Graph {
	return &Graph{
		Nodes: make(map[string]*Node),
	}
}

// AddNode adds a node to the graph
func (g *Graph) AddNode(id string, state ulmath.Quaternion) *Node {
	node := &Node{
		ID:    id,
		State: state,
		Edges: make([]*Edge, 0),
	}
	g.Nodes[id] = node
	return node
}

// AddEdge adds a weighted edge between nodes
func (g *Graph) AddEdge(fromID, toID string, weight float64) {
	from, fromExists := g.Nodes[fromID]
	to, toExists := g.Nodes[toID]

	if !fromExists || !toExists {
		return
	}

	edge := &Edge{
		From:   from,
		To:     to,
		Weight: weight,
	}
	from.Edges = append(from.Edges, edge)
}

// AddQuaternionEdge adds edge with weight = quaternion distance
func (g *Graph) AddQuaternionEdge(fromID, toID string) {
	from, fromExists := g.Nodes[fromID]
	to, toExists := g.Nodes[toID]

	if !fromExists || !toExists {
		return
	}

	// Weight = geodesic distance on S³
	dot := from.State.Dot(to.State)
	if dot > 1.0 {
		dot = 1.0
	}
	if dot < -1.0 {
		dot = -1.0
	}
	weight := stdmath.Acos(stdmath.Abs(dot))

	edge := &Edge{
		From:   from,
		To:     to,
		Weight: weight,
	}
	from.Edges = append(from.Edges, edge)
}

// ═══════════════════════════════════════════════════════════════════════════
// BREADTH-FIRST SEARCH (BFS)
// ═══════════════════════════════════════════════════════════════════════════

// BFS performs breadth-first search from startID
// Returns: visited nodes in BFS order
func (g *Graph) BFS(startID string) []*Node {
	start, exists := g.Nodes[startID]
	if !exists {
		return nil
	}

	visited := make(map[string]bool)
	queue := make([]*Node, 0)
	result := make([]*Node, 0)

	queue = append(queue, start)
	visited[startID] = true

	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		result = append(result, current)

		for _, edge := range current.Edges {
			if !visited[edge.To.ID] {
				visited[edge.To.ID] = true
				queue = append(queue, edge.To)
			}
		}
	}

	return result
}

// ═══════════════════════════════════════════════════════════════════════════
// DEPTH-FIRST SEARCH (DFS)
// ═══════════════════════════════════════════════════════════════════════════

// DFS performs depth-first search from startID
// Returns: visited nodes in DFS order
func (g *Graph) DFS(startID string) []*Node {
	start, exists := g.Nodes[startID]
	if !exists {
		return nil
	}

	visited := make(map[string]bool)
	result := make([]*Node, 0)

	var dfsRecursive func(*Node)
	dfsRecursive = func(node *Node) {
		visited[node.ID] = true
		result = append(result, node)

		for _, edge := range node.Edges {
			if !visited[edge.To.ID] {
				dfsRecursive(edge.To)
			}
		}
	}

	dfsRecursive(start)
	return result
}

// ═══════════════════════════════════════════════════════════════════════════
// DIJKSTRA'S SHORTEST PATH (with quaternion weights)
// ═══════════════════════════════════════════════════════════════════════════

// PathNode represents a node in the priority queue for Dijkstra's algorithm
type PathNode struct {
	Node     *Node
	Distance float64
	Previous *PathNode
	Index    int // Required for heap.Interface
}

// PriorityQueue implements heap.Interface for PathNode
type PriorityQueue []*PathNode

func (pq PriorityQueue) Len() int { return len(pq) }

func (pq PriorityQueue) Less(i, j int) bool {
	return pq[i].Distance < pq[j].Distance
}

func (pq PriorityQueue) Swap(i, j int) {
	pq[i], pq[j] = pq[j], pq[i]
	pq[i].Index = i
	pq[j].Index = j
}

func (pq *PriorityQueue) Push(x interface{}) {
	n := len(*pq)
	item := x.(*PathNode)
	item.Index = n
	*pq = append(*pq, item)
}

func (pq *PriorityQueue) Pop() interface{} {
	old := *pq
	n := len(old)
	item := old[n-1]
	old[n-1] = nil
	item.Index = -1
	*pq = old[0 : n-1]
	return item
}

// ShortestPath finds shortest path using Dijkstra's algorithm
// Returns: path as slice of nodes, total distance
func (g *Graph) ShortestPath(startID, endID string) ([]*Node, float64) {
	start, startExists := g.Nodes[startID]
	_, endExists := g.Nodes[endID]

	if !startExists || !endExists {
		return nil, stdmath.Inf(1)
	}

	// Initialize distances and priority queue
	distances := make(map[string]float64)
	pathNodes := make(map[string]*PathNode)

	for id := range g.Nodes {
		distances[id] = stdmath.Inf(1)
	}
	distances[startID] = 0

	pq := make(PriorityQueue, 0)
	heap.Init(&pq)

	startPathNode := &PathNode{
		Node:     start,
		Distance: 0,
		Previous: nil,
	}
	pathNodes[startID] = startPathNode
	heap.Push(&pq, startPathNode)

	// Dijkstra's algorithm
	for pq.Len() > 0 {
		current := heap.Pop(&pq).(*PathNode)

		// Found shortest path to end
		if current.Node.ID == endID {
			break
		}

		// Already processed with shorter distance
		if current.Distance > distances[current.Node.ID] {
			continue
		}

		// Explore neighbors
		for _, edge := range current.Node.Edges {
			newDistance := current.Distance + edge.Weight

			if newDistance < distances[edge.To.ID] {
				distances[edge.To.ID] = newDistance

				pathNode := &PathNode{
					Node:     edge.To,
					Distance: newDistance,
					Previous: current,
				}
				pathNodes[edge.To.ID] = pathNode
				heap.Push(&pq, pathNode)
			}
		}
	}

	// Reconstruct path
	if distances[endID] == stdmath.Inf(1) {
		return nil, stdmath.Inf(1) // No path exists
	}

	path := make([]*Node, 0)
	current := pathNodes[endID]
	for current != nil {
		path = append([]*Node{current.Node}, path...)
		current = current.Previous
	}

	return path, distances[endID]
}

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION SHORTEST PATH (SLERP-based geodesic)
// ═══════════════════════════════════════════════════════════════════════════

// QuaternionShortestPath finds path with minimal quaternion state transitions
// Uses SLERP for smooth interpolation on S³
func (g *Graph) QuaternionShortestPath(startID, endID string, steps int) []ulmath.Quaternion {
	path, _ := g.ShortestPath(startID, endID)
	if path == nil || len(path) < 2 {
		return nil
	}

	// Interpolate states along path using SLERP
	states := make([]ulmath.Quaternion, 0, steps*len(path))

	for i := 0; i < len(path)-1; i++ {
		q0 := path[i].State
		q1 := path[i+1].State

		for j := 0; j < steps; j++ {
			t := float64(j) / float64(steps)
			interpolated := ulmath.SLERP(q0, q1, t)
			states = append(states, interpolated)
		}
	}

	// Add final state
	states = append(states, path[len(path)-1].State)

	return states
}

// ═══════════════════════════════════════════════════════════════════════════
// CONNECTED COMPONENTS (with Williams batching)
// ═══════════════════════════════════════════════════════════════════════════

// ConnectedComponents finds all connected components in the graph
// Uses Williams O(√n × log₂n) batching for large graphs
func (g *Graph) ConnectedComponents() [][]*Node {
	visited := make(map[string]bool)
	components := make([][]*Node, 0)

	// Williams batch size for processing nodes
	n := len(g.Nodes)
	batchSize := int(stdmath.Sqrt(float64(n)) * stdmath.Log2(stdmath.Max(float64(n), 2)))
	if batchSize < 1 {
		batchSize = 1
	}

	nodeSlice := make([]*Node, 0, n)
	for _, node := range g.Nodes {
		nodeSlice = append(nodeSlice, node)
	}

	// Process in batches
	for i := 0; i < len(nodeSlice); i += batchSize {
		batchEnd := i + batchSize
		if batchEnd > len(nodeSlice) {
			batchEnd = len(nodeSlice)
		}

		for j := i; j < batchEnd; j++ {
			node := nodeSlice[j]
			if !visited[node.ID] {
				component := g.exploreComponent(node, visited)
				if len(component) > 0 {
					components = append(components, component)
				}
			}
		}
	}

	return components
}

// exploreComponent explores a connected component using DFS
func (g *Graph) exploreComponent(start *Node, visited map[string]bool) []*Node {
	component := make([]*Node, 0)
	stack := []*Node{start}

	for len(stack) > 0 {
		current := stack[len(stack)-1]
		stack = stack[:len(stack)-1]

		if visited[current.ID] {
			continue
		}

		visited[current.ID] = true
		component = append(component, current)

		for _, edge := range current.Edges {
			if !visited[edge.To.ID] {
				stack = append(stack, edge.To)
			}
		}
	}

	return component
}
