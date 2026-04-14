from src.data_structures.linked_list import (
    CircularLinkedList,
    DoublyLinkedList,
    SinglyLinkedList,
)


def test_singly_linked_list():
    lst = SinglyLinkedList[int]()
    lst.push_front(1)
    lst.push_front(2)
    lst.push_front(3)
    assert len(lst) == 3
    assert lst.pop_front() == 3
    assert lst.pop_front() == 2
    assert lst.find(1) == 1
    assert lst.find(99) is None
    assert list(lst) == [1]


def test_doubly_linked_list():
    lst = DoublyLinkedList[int]()
    lst.push_back(1)
    lst.push_back(2)
    lst.push_front(0)
    assert lst.peek_front() == 0
    assert lst.peek_back() == 2
    assert lst.pop_front() == 0
    assert lst.pop_back() == 2
    assert lst.pop_front() == 1
    assert lst.is_empty()
    assert len(lst) == 0


def test_circular_linked_list():
    lst = CircularLinkedList[int]()
    lst.push(1)
    lst.push(2)
    lst.push(3)
    assert lst.peek() == 1
    assert lst.rotate() == 1
    assert lst.peek() == 2
    assert lst.pop() == 2
    assert len(lst) == 2
    assert lst.pop() == 3
    assert lst.pop() == 1
    assert lst.pop() is None
