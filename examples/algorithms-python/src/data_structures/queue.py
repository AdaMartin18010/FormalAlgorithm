"""队列 (Queue)

先进先出 (FIFO) 的线性数据结构。
"""

from typing import Generic, Optional, TypeVar

T = TypeVar("T")


class _QueueNode(Generic[T]):
    def __init__(self, value: T) -> None:
        self.value = value
        self.next: Optional["_QueueNode[T]"] = None


class Queue(Generic[T]):
    """基于链表实现的队列

    Example:
        >>> q = Queue[int]()
        >>> q.enqueue(1)
        >>> q.enqueue(2)
        >>> q.dequeue()
        1
        >>> q.peek()
        2
    """

    def __init__(self) -> None:
        self.head: Optional[_QueueNode[T]] = None
        self.tail: Optional[_QueueNode[T]] = None
        self._len = 0

    def __len__(self) -> int:
        return self._len

    def enqueue(self, value: T) -> None:
        node = _QueueNode(value)
        if self.tail is None:
            self.head = self.tail = node
        else:
            self.tail.next = node
            self.tail = node
        self._len += 1

    def dequeue(self) -> Optional[T]:
        if self.head is None:
            return None
        value = self.head.value
        self.head = self.head.next
        if self.head is None:
            self.tail = None
        self._len -= 1
        return value

    def peek(self) -> Optional[T]:
        return self.head.value if self.head else None

    def is_empty(self) -> bool:
        return self._len == 0

    def clear(self) -> None:
        self.head = self.tail = None
        self._len = 0


class QueueWithTwoStacks(Generic[T]):
    """基于两个栈实现的队列（amortized O(1)）

    Example:
        >>> q = QueueWithTwoStacks[int]()
        >>> q.enqueue(1)
        >>> q.enqueue(2)
        >>> q.dequeue()
        1
        >>> q.dequeue()
        2
    """

    def __init__(self) -> None:
        self._in_stack: List[T] = []
        self._out_stack: List[T] = []

    def __len__(self) -> int:
        return len(self._in_stack) + len(self._out_stack)

    def enqueue(self, value: T) -> None:
        self._in_stack.append(value)

    def dequeue(self) -> Optional[T]:
        if not self._out_stack:
            while self._in_stack:
                self._out_stack.append(self._in_stack.pop())
        return self._out_stack.pop() if self._out_stack else None

    def peek(self) -> Optional[T]:
        if not self._out_stack:
            return self._in_stack[0] if self._in_stack else None
        return self._out_stack[-1]

    def is_empty(self) -> bool:
        return not self._in_stack and not self._out_stack
