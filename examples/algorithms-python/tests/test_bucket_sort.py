"""桶排序测试"""

from src.sorting.bucket_sort import bucket_sort, bucket_sort_by


def test_empty():
    arr = []
    bucket_sort(arr)
    assert arr == []


def test_single_element():
    arr = [0.5]
    bucket_sort(arr)
    assert arr == [0.5]


def test_basic():
    arr = [0.42, 0.32, 0.33, 0.52, 0.37, 0.47, 0.51]
    bucket_sort(arr)
    assert arr == [0.32, 0.33, 0.37, 0.42, 0.47, 0.51, 0.52]


def test_already_sorted():
    arr = [0.1, 0.2, 0.3, 0.4, 0.5]
    bucket_sort(arr)
    assert arr == [0.1, 0.2, 0.3, 0.4, 0.5]


def test_reverse_sorted():
    arr = [0.9, 0.7, 0.5, 0.3, 0.1]
    bucket_sort(arr)
    assert arr == [0.1, 0.3, 0.5, 0.7, 0.9]


def test_duplicates():
    arr = [0.5, 0.3, 0.5, 0.1, 0.3]
    bucket_sort(arr)
    assert arr == [0.1, 0.3, 0.3, 0.5, 0.5]


def test_uniform_sequence():
    arr = [i / 100.0 for i in range(99, -1, -1)]
    bucket_sort(arr)
    assert arr == [i / 100.0 for i in range(100)]


def test_bucket_sort_by():
    data = [(42, 0.42), (32, 0.32), (33, 0.33)]
    bucket_sort_by(data, lambda x: x[1])
    assert data == [(32, 0.32), (33, 0.33), (42, 0.42)]
