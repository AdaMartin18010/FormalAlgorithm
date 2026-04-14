from src.data_structures.deque import Deque, is_palindrome


def test_deque_basic():
    d = Deque[int]()
    d.push_back(1)
    d.push_back(2)
    d.push_front(0)
    assert len(d) == 3
    assert d.peek_front() == 0
    assert d.peek_back() == 2
    assert d.pop_front() == 0
    assert d.pop_back() == 2
    assert d.pop_front() == 1
    assert d.is_empty()


def test_deque_clear():
    d = Deque[int]()
    d.push_back(1)
    d.push_front(2)
    d.clear()
    assert d.is_empty()
    assert d.pop_front() is None
    assert d.pop_back() is None


def test_is_palindrome():
    assert is_palindrome("racecar")
    assert is_palindrome("")
    assert is_palindrome("a")
    assert not is_palindrome("hello")
    assert not is_palindrome("ab")
