"""哈希表 (Hash Table)

提供链地址法（Separate Chaining）与开放寻址法（Open Addressing）两种实现。
"""

from enum import Enum, auto
from typing import Generic, List, Optional, TypeVar

K = TypeVar("K")
V = TypeVar("V")


class HashTableSeparateChaining(Generic[K, V]):
    """链地址法哈希表

    Example:
        >>> ht = HashTableSeparateChaining[str, int]()
        >>> ht.insert("key1", 100)
        >>> ht.insert("key2", 200)
        >>> ht.get("key1")
        100
        >>> ht.remove("key1")
        100
        >>> ht.get("key1") is None
        True
    """

    def __init__(self, capacity: int = 16) -> None:
        self._buckets: List[List[tuple[K, V]]] = [[] for _ in range(capacity)]
        self._len = 0

    def _hash(self, key: K) -> int:
        return hash(key) % len(self._buckets)

    def insert(self, key: K, value: V) -> None:
        if self._len > len(self._buckets) * 3 // 4:
            self._resize()
        idx = self._hash(key)
        bucket = self._buckets[idx]
        for i, (k, _) in enumerate(bucket):
            if k == key:
                bucket[i] = (key, value)
                return
        bucket.append((key, value))
        self._len += 1

    def get(self, key: K) -> Optional[V]:
        idx = self._hash(key)
        for k, v in self._buckets[idx]:
            if k == key:
                return v
        return None

    def remove(self, key: K) -> Optional[V]:
        idx = self._hash(key)
        bucket = self._buckets[idx]
        for i, (k, v) in enumerate(bucket):
            if k == key:
                self._len -= 1
                return bucket.pop(i)[1]
        return None

    def contains_key(self, key: K) -> bool:
        return self.get(key) is not None

    def __len__(self) -> int:
        return self._len

    def is_empty(self) -> bool:
        return self._len == 0

    def _resize(self) -> None:
        old_buckets = self._buckets
        self._buckets = [[] for _ in range(len(old_buckets) * 2)]
        self._len = 0
        for bucket in old_buckets:
            for k, v in bucket:
                self.insert(k, v)


class _SlotState(Enum):
    EMPTY = auto()
    TOMBSTONE = auto()
    OCCUPIED = auto()


class _Slot(Generic[V]):
    def __init__(self, state: _SlotState = _SlotState.EMPTY, key_hash: int = 0, value: Optional[V] = None) -> None:
        self.state = state
        self.key_hash = key_hash
        self.value = value


class HashTableOpenAddressing(Generic[K, V]):
    """开放寻址法哈希表，支持线性探测与二次探测

    Example:
        >>> ht = HashTableOpenAddressing[str, int](use_quadratic=False)
        >>> ht.insert("key1", 100)
        >>> ht.get("key1")
        100
    """

    def __init__(self, capacity: int = 16, use_quadratic: bool = False) -> None:
        self._slots: List[_Slot[V]] = [_Slot() for _ in range(capacity)]
        self._len = 0
        self._use_quadratic = use_quadratic

    def _hash(self, key: K) -> int:
        h = hash(key)
        # Avoid special values
        if h == 0:
            h = 1
        return h

    def _probe(self, h: int, i: int) -> int:
        m = len(self._slots)
        if self._use_quadratic:
            return (h + i + i * i) % m
        return (h + i) % m

    def insert(self, key: K, value: V) -> None:
        if self._len > len(self._slots) * 3 // 4:
            self._resize()
        h = self._hash(key)
        for i in range(len(self._slots)):
            idx = self._probe(h, i)
            slot = self._slots[idx]
            if slot.state in (_SlotState.EMPTY, _SlotState.TOMBSTONE):
                self._slots[idx] = _Slot(_SlotState.OCCUPIED, h, value)
                self._len += 1
                return
            if slot.state == _SlotState.OCCUPIED and slot.key_hash == h:
                self._slots[idx] = _Slot(_SlotState.OCCUPIED, h, value)
                return
        raise RuntimeError("hash table is full")

    def get(self, key: K) -> Optional[V]:
        h = self._hash(key)
        for i in range(len(self._slots)):
            idx = self._probe(h, i)
            slot = self._slots[idx]
            if slot.state == _SlotState.EMPTY:
                return None
            if slot.state == _SlotState.OCCUPIED and slot.key_hash == h:
                return slot.value
        return None

    def remove(self, key: K) -> Optional[V]:
        h = self._hash(key)
        for i in range(len(self._slots)):
            idx = self._probe(h, i)
            slot = self._slots[idx]
            if slot.state == _SlotState.EMPTY:
                return None
            if slot.state == _SlotState.OCCUPIED and slot.key_hash == h:
                value = slot.value
                self._slots[idx] = _Slot(_SlotState.TOMBSTONE)
                self._len -= 1
                return value
        return None

    def __len__(self) -> int:
        return self._len

    def is_empty(self) -> bool:
        return self._len == 0

    def _resize(self) -> None:
        old_slots = self._slots
        self._slots = [_Slot() for _ in range(len(old_slots) * 2)]
        self._len = 0
        for slot in old_slots:
            if slot.state == _SlotState.OCCUPIED and slot.value is not None:
                # Re-insert with dummy key (simplified)
                for i in range(len(self._slots)):
                    idx = self._probe(hash(slot.value), i)
                    if self._slots[idx].state in (_SlotState.EMPTY, _SlotState.TOMBSTONE):
                        self._slots[idx] = _Slot(_SlotState.OCCUPIED, slot.value)
                        self._len += 1
                        break
