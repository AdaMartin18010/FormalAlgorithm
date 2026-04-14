"""动态数组 (Dynamic Array)

支持均摊 O(1) 尾部插入的自动扩容/缩容数组实现。
"""

from typing import Generic, Iterator, List, Optional, TypeVar

T = TypeVar("T")


class DynamicArray(Generic[T]):
    """动态数组

    当元素数量达到容量上限时，按 growth factor（通常为 2）扩容。
    当元素数量低于一定比例时，按相同因子缩容，避免空间浪费。

    Example:
        >>> arr = DynamicArray[int]()
        >>> arr.push(10)
        >>> arr.push(20)
        >>> arr.get(0)
        10
        >>> arr.pop()
        20
    """

    def __init__(self, capacity: int = 0) -> None:
        self._data: List[Optional[T]] = [None] * capacity
        self._len = 0
        self._capacity = capacity

    def __len__(self) -> int:
        return self._len

    def __iter__(self) -> Iterator[T]:
        for i in range(self._len):
            yield self._data[i]  # type: ignore

    def __repr__(self) -> str:
        return f"DynamicArray({list(self)})"

    def capacity(self) -> int:
        return self._capacity

    def is_empty(self) -> bool:
        return self._len == 0

    def push(self, value: T) -> None:
        """在尾部追加元素，O(1) 均摊"""
        if self._len == self._capacity:
            new_cap = max(1, self._capacity * 2)
            new_data: List[Optional[T]] = [None] * new_cap
            for i in range(self._len):
                new_data[i] = self._data[i]
            self._data = new_data
            self._capacity = new_cap
        self._data[self._len] = value
        self._len += 1

    def pop(self) -> Optional[T]:
        """移除尾部元素并返回，O(1) 均摊"""
        if self._len == 0:
            return None
        self._len -= 1
        value = self._data[self._len]
        if self._capacity > 1 and self._len <= self._capacity // 4:
            new_cap = max(self._capacity // 2, 1)
            new_data: List[Optional[T]] = [None] * new_cap
            for i in range(self._len):
                new_data[i] = self._data[i]
            self._data = new_data
            self._capacity = new_cap
        return value

    def get(self, index: int) -> Optional[T]:
        """获取索引位置的元素"""
        if 0 <= index < self._len:
            return self._data[index]
        return None

    def set(self, index: int, value: T) -> None:
        """设置索引位置的元素"""
        if 0 <= index < self._len:
            self._data[index] = value
        else:
            raise IndexError("index out of bounds")

    def insert(self, index: int, value: T) -> None:
        """在指定位置插入元素，O(n)"""
        if not 0 <= index <= self._len:
            raise IndexError("index out of bounds")
        if self._len == self._capacity:
            new_cap = max(1, self._capacity * 2)
            new_data: List[Optional[T]] = [None] * new_cap
            for i in range(self._len):
                new_data[i] = self._data[i]
            self._data = new_data
            self._capacity = new_cap
        for i in range(self._len, index, -1):
            self._data[i] = self._data[i - 1]
        self._data[index] = value
        self._len += 1

    def remove(self, index: int) -> T:
        """移除指定位置的元素，O(n)"""
        if not 0 <= index < self._len:
            raise IndexError("index out of bounds")
        value = self._data[index]
        for i in range(index, self._len - 1):
            self._data[i] = self._data[i + 1]
        self._len -= 1
        if self._capacity > 1 and self._len <= self._capacity // 4:
            new_cap = max(self._capacity // 2, 1)
            new_data: List[Optional[T]] = [None] * new_cap
            for i in range(self._len):
                new_data[i] = self._data[i]
            self._data = new_data
            self._capacity = new_cap
        return value  # type: ignore
