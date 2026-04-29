"""
LeetCode 232. Implement Queue using Stacks
用栈实现队列

Implement a first in first out (FIFO) queue using only two stacks.
The implemented queue should support all the functions of a normal queue
(push, peek, pop, and empty).

Amortized O(1) per operation using two stacks.
"""


class MyQueue:
    """
    双栈法实现队列 FIFO 语义
    Two-stack approach for FIFO semantics

    in_stack: 接收输入 / Receives input
    out_stack: 负责输出 / Handles output
    Amortized Time: O(1), Space: O(n)
    """

    def __init__(self):
        self.in_stack: list[int] = []
        self.out_stack: list[int] = []

    def push(self, x: int) -> None:
        """入队 — 直接压入输入栈 / Enqueue — push to input stack"""
        self.in_stack.append(x)

    def pop(self) -> int:
        """出队 — 摊还 O(1) / Dequeue — amortized O(1)"""
        self.peek()
        return self.out_stack.pop()

    def peek(self) -> int:
        """查看队头 — 仅在输出栈空时转移 / Peek front — transfer only when out_stack empty"""
        if not self.out_stack:
            while self.in_stack:
                self.out_stack.append(self.in_stack.pop())
        return self.out_stack[-1]

    def empty(self) -> bool:
        return not self.in_stack and not self.out_stack


# 简单测试 / Simple test
if __name__ == "__main__":
    q = MyQueue()
    q.push(1)
    q.push(2)
    assert q.peek() == 1
    assert q.pop() == 1
    assert not q.empty()
    assert q.pop() == 2
    assert q.empty()
    print("All tests passed!")
