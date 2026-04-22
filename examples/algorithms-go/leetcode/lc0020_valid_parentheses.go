package leetcode

// LeetCode 20. Valid Parentheses
// 有效的括号
//
// Given a string s containing just the characters '(', ')', '{', '}', '[' and ']',
// determine if the input string is valid.

// IsValid 使用栈进行括号匹配
// Stack-based parenthesis matching
// Time: O(n), Space: O(n)
func IsValid(s string) bool {
	stack := make([]rune, 0)
	pairs := map[rune]rune{')': '(', ']': '[', '}': '{'}

	for _, ch := range s {
		if open, ok := pairs[ch]; ok {
			// 遇到右括号，检查栈顶是否匹配
			// Encounter closing bracket, check stack top
			if len(stack) == 0 || stack[len(stack)-1] != open {
				return false
			}
			stack = stack[:len(stack)-1]
		} else {
			// 遇到左括号，入栈
			// Encounter opening bracket, push to stack
			stack = append(stack, ch)
		}
	}

	return len(stack) == 0
}
