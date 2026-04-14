from src.data_structures.hash_table import (
    HashTableOpenAddressing,
    HashTableSeparateChaining,
)


def test_separate_chaining():
    ht = HashTableSeparateChaining[str, int]()
    ht.insert("apple", 5)
    ht.insert("banana", 6)
    ht.insert("cherry", 6)
    assert ht.get("apple") == 5
    assert ht.get("banana") == 6
    assert ht.remove("banana") == 6
    assert ht.get("banana") is None
    assert len(ht) == 2
    assert ht.contains_key("apple")
    assert not ht.contains_key("banana")


def test_open_addressing_linear():
    ht = HashTableOpenAddressing[str, int](use_quadratic=False)
    ht.insert("a", 1)
    ht.insert("b", 2)
    ht.insert("c", 3)
    assert ht.get("a") == 1
    assert ht.get("b") == 2
    assert ht.remove("b") == 2
    assert ht.get("b") is None


def test_open_addressing_quadratic():
    ht = HashTableOpenAddressing[int, str](use_quadratic=True)
    ht.insert(1, "one")
    ht.insert(2, "two")
    ht.insert(3, "three")
    assert ht.get(1) == "one"
    assert ht.get(2) == "two"
    assert ht.remove(2) == "two"
    assert ht.get(2) is None


def test_resize_behavior():
    ht = HashTableSeparateChaining[int, int]()
    for i in range(100):
        ht.insert(i, i * 2)
    for i in range(100):
        assert ht.get(i) == i * 2
