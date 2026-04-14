from src.data_structures.stack import Stack, is_balanced


def test_stack_operations():
    s = Stack[int]()
    assert s.is_empty()
    s.push(10)
    s.push(20)
    s.push(30)
    assert len(s) == 3
    assert s.peek() == 30
    assert s.pop() == 30
    assert s.pop() == 20
    assert s.pop() == 10
    assert s.pop() is None


def test_is_balanced():
    assert is_balanced("()")
    assert is_balanced("({[]})")
    assert is_balanced("")
    assert not is_balanced("(")
    assert not is_balanced("]")
    assert not is_balanced("({[})")
