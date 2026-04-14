"""链表 (Linked List)

提供单链表、双向链表、循环链表三种基础实现。
"""

from typing import Generic, Iterator, Optional, TypeVar

T = TypeVar("T")


class SllNode(Generic[T]):
    def __init__(self, value: T) -> None:
        self.value = value
        self.next: Optional["SllNode[T]"] = None


class SinglyLinkedList(Generic[T]):
    """单链表

    Example:
        >>> lst = SinglyLinkedList[int]()
        >>> lst.push_front(1)
        >>> lst.push_front(2)
        >>> lst.pop_front()
        2
    """

    def __init__(self) -> None:
        self.head: Optional[SllNode[T]] = None
        self._len = 0

    def __len__(self) -> int:
        return self._len

    def __iter__(self) -> Iterator[T]:
        current = self.head
        while current:
            yield current.value
            current = current.next

    def push_front(self, value: T) -> None:
        node = SllNode(value)
        node.next = self.head
        self.head = node
        self._len += 1

    def pop_front(self) -> Optional[T]:
        if self.head is None:
            return None
        value = self.head.value
        self.head = self.head.next
        self._len -= 1
        return value

    def peek_front(self) -> Optional[T]:
        return self.head.value if self.head else None

    def find(self, value: T) -> Optional[T]:
        current = self.head
        while current:
            if current.value == value:
                return current.value
            current = current.next
        return None


class DllNode(Generic[T]):
    def __init__(self, value: T) -> None:
        self.value = value
        self.prev: Optional["DllNode[T]"] = None
        self.next: Optional["DllNode[T]"] = None


class DoublyLinkedList(Generic[T]):
    """双向链表

    Example:
        >>> lst = DoublyLinkedList[int]()
        >>> lst.push_back(1)
        >>> lst.push_back(2)
        >>> lst.push_front(0)
        >>> lst.pop_front()
        0
        >>> lst.pop_back()
        2
    """

    def __init__(self) -> None:
        self.head: Optional[DllNode[T]] = None
        self.tail: Optional[DllNode[T]] = None
        self._len = 0

    def __len__(self) -> int:
        return self._len

    def push_front(self, value: T) -> None:
        node = DllNode(value)
        if self.head is None:
            self.head = self.tail = node
        else:
            node.next = self.head
            self.head.prev = node
            self.head = node
        self._len += 1

    def push_back(self, value: T) -> None:
        node = DllNode(value)
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


class CllNode(Generic[T]):
    def __init__(self, value: T) -> None:
        self.value = value
        self.next: Optional["CllNode[T]"] = None


class CircularLinkedList(Generic[T]):
    """循环链表（单向循环）

    Example:
        >>> lst = CircularLinkedList[int]()
        >>> lst.push(1)
        >>> lst.push(2)
        >>> lst.rotate()
        1
        >>> lst.rotate()
        2
    """

    def __init__(self) -> None:
        self.tail: Optional[CllNode[T]] = None
        self._len = 0

    def __len__(self) -> int:
        return self._len

    def push(self, value: T) -> None:
        node = CllNode(value)
        if self.tail is None:
            node.next = node
            self.tail = node
        else:
            node.next = self.tail.next
            self.tail.next = node
            self.tail = node
        self._len += 1

    def pop(self) -> Optional[T]:
        if self.tail is None:
            return None
        head = self.tail.next
        assert head is not None
        value = head.value
        if head == self.tail:
            self.tail = None
        else:
            self.tail.next = head.next
        self._len -= 1
        return value

    def rotate(self) -> Optional[T]:
        if self.tail is None:
            return None
        head = self.tail.next
        assert head is not None
        self.tail = head
        return head.value

    def peek(self) -> Optional[T]:
        if self.tail is None:
            return None
        head = self.tail.next
        assert head is not None
        return head.value
