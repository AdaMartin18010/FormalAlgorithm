import pytest
from src.data_structures.dynamic_array import DynamicArray


def test_push_and_pop():
    arr = DynamicArray[int]()
    arr.push(1)
    arr.push(2)
    arr.push(3)
    assert len(arr) == 3
    assert arr.pop() == 3
    assert arr.pop() == 2
    assert arr.pop() == 1
    assert arr.pop() is None


def test_get_and_set():
    arr = DynamicArray[int]()
    arr.push(10)
    arr.push(20)
    assert arr.get(0) == 10
    assert arr.get(1) == 20
    assert arr.get(2) is None
    arr.set(0, 100)
    assert arr.get(0) == 100


def test_insert_remove():
    arr = DynamicArray[int]()
    arr.push(1)
    arr.push(3)
    arr.insert(1, 2)
    assert arr.get(0) == 1
    assert arr.get(1) == 2
    assert arr.get(2) == 3
    assert arr.remove(1) == 2
    assert arr.get(1) == 3


def test_expand_and_contract():
    arr = DynamicArray[int](capacity=4)
    for i in range(10):
        arr.push(i)
    assert arr.capacity() >= 10
    for _ in range(8):
        arr.pop()
    assert arr.capacity() >= 2
    assert arr.capacity() < 10


def test_iter():
    arr = DynamicArray[int]()
    for i in range(5):
        arr.push(i)
    assert list(arr) == [0, 1, 2, 3, 4]


def test_index_error():
    arr = DynamicArray[int]()
    with pytest.raises(IndexError):
        arr.set(0, 1)
    with pytest.raises(IndexError):
        arr.remove(0)
    with pytest.raises(IndexError):
        arr.insert(1, 1)
