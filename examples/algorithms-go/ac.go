// Package algorithms provides Aho-Corasick automaton in Go.
package algorithms

// ACNode represents a node in the AC automaton.
type ACNode struct {
	children map[byte]*ACNode
	fail     *ACNode
	output   []string
}

// AhoCorasick implements multi-pattern string matching.
type AhoCorasick struct {
	root *ACNode
}

// NewAhoCorasick creates a new AC automaton.
func NewAhoCorasick() *AhoCorasick {
	return &AhoCorasick{root: &ACNode{children: make(map[byte]*ACNode)}}
}

// Insert adds a pattern to the automaton.
func (ac *AhoCorasick) Insert(word string) {
	node := ac.root
	for i := 0; i < len(word); i++ {
		ch := word[i]
		if node.children[ch] == nil {
			node.children[ch] = &ACNode{children: make(map[byte]*ACNode)}
		}
		node = node.children[ch]
	}
	node.output = append(node.output, word)
}

// Build constructs failure links.
func (ac *AhoCorasick) Build() {
	q := make([]*ACNode, 0)
	for _, child := range ac.root.children {
		child.fail = ac.root
		q = append(q, child)
	}
	for front := 0; front < len(q); front++ {
		curr := q[front]
		for ch, child := range curr.children {
			fail := curr.fail
			for fail != ac.root && fail.children[ch] == nil {
				fail = fail.fail
			}
			if f, ok := fail.children[ch]; ok && f != child {
				child.fail = f
			} else {
				child.fail = ac.root
			}
			child.output = append(child.output, child.fail.output...)
			q = append(q, child)
		}
	}
}

// MatchResult stores a match position and matched patterns.
type MatchResult struct {
	Pos     int
	Patterns []string
}

// Search finds all patterns in text.
func (ac *AhoCorasick) Search(text string) []MatchResult {
	var res []MatchResult
	node := ac.root
	for i := 0; i < len(text); i++ {
		ch := text[i]
		for node != ac.root && node.children[ch] == nil {
			node = node.fail
		}
		if child, ok := node.children[ch]; ok {
			node = child
		} else {
			node = ac.root
		}
		if len(node.output) > 0 {
			res = append(res, MatchResult{Pos: i, Patterns: append([]string{}, node.output...)})
		}
	}
	return res
}
