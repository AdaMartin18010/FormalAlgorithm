"""
LeetCode 155. Min Stack
最小栈

Design a stack that supports push, pop, top, and retrieving the minimum element in constant time.

Implement the MinStack class:
- MinStack() initializes the stack object.
- void push(int val) pushes the element val onto the stack.
- void pop() removes the element on the top of the stack.
- int top() gets the top element of the stack.
- int getMin() retrieves the minimum element in the stack.
"""


class MinStack:
    """
    主栈 + 辅助栈同步维护最小值
    Main stack + auxiliary stack maintaining minimum

    Auxiliary stack invariant: min_stack[-1] == min(main_stack)
    Time: O(1) per operation, Space: O(n)
    """

    def __init__(self):
        self.stack: list[int] = []      # 主栈 / Main stack
        self.min_stack: list[int] = []  # 辅助栈 / Auxiliary stack

    def push(self, val: int) -> None:
        self.stack.append(val)
        if not self.min_stack:
            self.min_stack.append(val)
        else:
            self.min_stack.append(min(val, self.min_stack[-1]))

    def pop(self) -> None:
        self.stack.pop()
        self.min_stack.pop()

    def top(self) -> int:
        return self.stack[-1]

    def getMin(self) -> int:
        return self.min_stack[-1]


# 简单测试 / Simple test
if __name__ == "__main__":
    min_stack = MinStack()
    min_stack.push(-2)
    min_stack.push(0)
    min_stack.push(-3)
    assert min_stack.getMin() == -3
    min_stack.pop()
    assert min_stack.top() == 0
    assert min_stack.getMin() == -2
    print("All tests passed!")
