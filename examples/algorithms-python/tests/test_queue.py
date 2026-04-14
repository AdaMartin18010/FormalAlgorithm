from src.data_structures.queue import Queue, QueueWithTwoStacks


def test_queue_basic():
    q = Queue[int]()
    q.enqueue(1)
    q.enqueue(2)
    q.enqueue(3)
    assert len(q) == 3
    assert q.peek() == 1
    assert q.dequeue() == 1
    assert q.dequeue() == 2
    assert q.dequeue() == 3
    assert q.dequeue() is None


def test_queue_clear():
    q = Queue[int]()
    q.enqueue(1)
    q.enqueue(2)
    q.clear()
    assert q.is_empty()
    assert q.dequeue() is None


def test_queue_with_two_stacks():
    q = QueueWithTwoStacks[int]()
    q.enqueue(1)
    q.enqueue(2)
    q.enqueue(3)
    assert q.dequeue() == 1
    q.enqueue(4)
    assert q.dequeue() == 2
    assert q.dequeue() == 3
    assert q.dequeue() == 4
    assert q.dequeue() is None
