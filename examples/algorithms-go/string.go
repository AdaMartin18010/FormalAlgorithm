// Package algorithms provides string algorithm implementations in Go.
package algorithms

/**
 * KMP前缀函数
 * 时间复杂度: O(m)
 */
func KMPPrefix(pattern string) []int {
	m := len(pattern)
	pi := make([]int, m)
	k := 0
	for q := 1; q < m; q++ {
		for k > 0 && pattern[k] != pattern[q] {
			k = pi[k-1]
		}
		if pattern[k] == pattern[q] {
			k++
		}
		pi[q] = k
	}
	return pi
}

/**
 * KMP搜索
 * 时间复杂度: O(n + m)
 */
func KMPSearch(text, pattern string) []int {
	if len(pattern) == 0 {
		return []int{}
	}
	pi := KMPPrefix(pattern)
	matches := []int{}
	q := 0
	for i := 0; i < len(text); i++ {
		for q > 0 && pattern[q] != text[i] {
			q = pi[q-1]
		}
		if pattern[q] == text[i] {
			q++
		}
		if q == len(pattern) {
			matches = append(matches, i-len(pattern)+1)
			q = pi[q-1]
		}
	}
	return matches
}

/**
 * Z函数
 * 时间复杂度: O(n)
 */
func ZFunction(s string) []int {
	n := len(s)
	z := make([]int, n)
	l, r := 0, 0
	for i := 1; i < n; i++ {
		if i <= r {
			if z[i-l] < r-i+1 {
				z[i] = z[i-l]
			} else {
				z[i] = r - i + 1
			}
		}
		for i+z[i] < n && s[z[i]] == s[i+z[i]] {
			z[i]++
		}
		if i+z[i]-1 > r {
			l = i
			r = i + z[i] - 1
		}
	}
	return z
}

/**
 * Manacher算法
 * 时间复杂度: O(n)
 */
func Manacher(s string) []int {
	t := make([]rune, 0, len(s)*2+3)
	t = append(t, '^', '#')
	for _, c := range s {
		t = append(t, c, '#')
	}
	t = append(t, '$')
	n := len(t)
	p := make([]int, n)
	c, r := 0, 0
	for i := 1; i < n-1; i++ {
		mirr := 2*c - i
		if i < r {
			if p[mirr] < r-i {
				p[i] = p[mirr]
			} else {
				p[i] = r - i
			}
		}
		for t[i+1+p[i]] == t[i-1-p[i]] {
			p[i]++
		}
		if i+p[i] > r {
			c = i
			r = i + p[i]
		}
	}
	return p
}
