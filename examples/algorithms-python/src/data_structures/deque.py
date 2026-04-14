"""双端队列 (Deque)

允许在队列两端进行插入和删除的线性数据结构。
"""

from typing import Generic, Optional, TypeVar

T = TypeVar("T")


class _DequeNode(Generic[T]):
    def __init__(self, value: T) -> None:
        self.value = value
        self.prev: Optional["_DequeNode[T]"] = None
        self.next: Optional["_DequeNode[T]"] = None


class Deque(Generic[T]):
    """基于双向链表实现的双端队列

    Example:
        >>> d = Deque[int]()
        >>> d.push_back(1)
        >>> d.push_back(2)
        >>> d.push_front(0)
        >>> d.pop_front()
        0
        >>> d.pop_back()
        2
    """

    def __init__(self) -> None:
        self.head: Optional[_DequeNode[T]] = None
        self.tail: Optional[_DequeNode[T]] = None
        self._len = 0

    def __len__(self) -> int:
        return self._len

    def push_front(self, value: T) -> None:
        node = _DequeNode(value)
        if self.head is None:
            self.head = self.tail = node
        else:
            node.next = self.head
            self.head.prev = node
            self.head = node
        self._len += 1

    def push_back(self, value: T) -> None:
        node = _DequeNode(value)
        if self.tail is None:
            self.head = self.tail = node
        else:
            node.prev = self.tail
            self.tail.next = node
            self.tail = node
        self._len += 1

    def pop_front(self) -> Optional[T]:
        if self.head is None:
            return None
        value = self.head.value
        self.head = self.head.next
        if self.head:
            self.head.prev = None
        else:
            self.tail = None
        self._len -= 1
        return value

    def pop_back(self) -> Optional[T]:
        if self.tail is None:
            return None
        value = self.tail.value
        self.tail = self.tail.prev
        if self.tail:
            self.tail.next = None
        else:
            self.head = None
        self._len -= 1
        return value

    def peek_front(self) -> Optional[T]:
        return self.head.value if self.head else None

    def peek_back(self) -> Optional[T]:
        return self.tail.value if self.tail else None

    def is_empty(self) -> bool:
        return self._len == 0

    def clear(self) -> None:
        self.head = self.tail = None
        self._len = 0


def is_palindrome(s: str) -> bool:
    """检查字符串是否为回文（使用双端队列）

    Example:
        >>> is_palindrome("racecar")
        True
        >>> is_palindrome("hello")
        False
    """
    d = Deque[str]()
    for ch in s:
        d.push_back(ch)
    while len(d) > 1:
        if d.pop_front() != d.pop_back():
            return False
    return True
