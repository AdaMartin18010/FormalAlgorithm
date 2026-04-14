"""栈 (Stack)

后进先出 (LIFO) 的线性数据结构。
"""

from typing import Generic, List, Optional, TypeVar

T = TypeVar("T")


class Stack(Generic[T]):
    """栈结构

    Example:
        >>> s = Stack[int]()
        >>> s.push(1)
        >>> s.push(2)
        >>> s.pop()
        2
        >>> s.peek()
        1
    """

    def __init__(self) -> None:
        self._data: List[T] = []

    def __len__(self) -> int:
        return len(self._data)

    def push(self, value: T) -> None:
        self._data.append(value)

    def pop(self) -> Optional[T]:
        return self._data.pop() if self._data else None

    def peek(self) -> Optional[T]:
        return self._data[-1] if self._data else None

    def is_empty(self) -> bool:
        return len(self._data) == 0

    def clear(self) -> None:
        self._data.clear()


def is_balanced(s: str) -> bool:
    """括号匹配检查

    Example:
        >>> is_balanced("({[]})")
        True
        >>> is_balanced("({[})")
        False
    """
    stack: List[str] = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for ch in s:
        if ch in "([{":
            stack.append(ch)
        elif ch in ")]}":
            if not stack or stack.pop() != pairs[ch]:
                return False
    return not stack
