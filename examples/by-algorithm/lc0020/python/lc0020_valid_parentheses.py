"""
LeetCode 20. Valid Parentheses
有效的括号

Given a string s containing just the characters '(', ')', '{', '}', '[' and ']',
determine if the input string is valid.

An input string is valid if:
1. Open brackets must be closed by the same type of brackets.
2. Open brackets must be closed in the correct order.
3. Every close bracket has a corresponding open bracket of the same type.
"""

from typing import List


class Solution:
    def isValid(self, s: str) -> bool:
        """
        使用栈进行括号匹配
        Stack-based parenthesis matching

        Time: O(n), Space: O(n)
        """
        stack: List[str] = []
        pairs = {')': '(', ']': '[', '}': '{'}

        for ch in s:
            if ch in pairs:
                # 遇到右括号，检查栈顶是否匹配
                # Encounter closing bracket, check stack top
                if not stack or stack[-1] != pairs[ch]:
                    return False
                stack.pop()
            else:
                # 遇到左括号，入栈
                # Encounter opening bracket, push to stack
                stack.append(ch)

        return not stack


# 简单测试 / Simple test
if __name__ == "__main__":
    sol = Solution()
    assert sol.isValid("()") is True
    assert sol.isValid("()[]{}") is True
    assert sol.isValid("(]") is False
    assert sol.isValid("([)]") is False
    assert sol.isValid("{[]}") is True
    print("All tests passed!")
