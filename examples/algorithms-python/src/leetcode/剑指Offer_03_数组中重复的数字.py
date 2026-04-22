"""
剑指 Offer 03. 数组中重复的数字
https://leetcode.cn/problems/shu-zu-zhong-zhong-fu-de-shu-zi-lcof/

Problem: In an array of length n where all numbers are in range [0, n-1],
some numbers are duplicated. Find any duplicate number.

Formal specification:
- Pre: nums.length = n, for all i: 0 <= nums[i] <= n-1
- Post: result is a value that appears more than once in nums

Algorithm 1: Hash set / counting. Time O(n), Space O(n).
Algorithm 2 (optimal): In-place swap to position i. Time O(n), Space O(1).

Proof of in-place algorithm:
Invariant: After processing index i, all elements in [0..i] satisfy nums[j] == j or
nums[j] is a duplicate.
When nums[i] != i, swap nums[i] with nums[nums[i]].
If nums[nums[i]] already equals nums[i], we found a duplicate.
Termination: Each swap places at least one element in its correct position.
At most n swaps needed.

Reference: docs/面试指南/06-面试专题/04-剑指Offer精选形式化证明.md
"""

from typing import List


def find_repeat_number_hash(nums: List[int]) -> int:
    """Hash set approach: O(n) time, O(n) space."""
    seen = set()
    for x in nums:
        if x in seen:
            return x
        seen.add(x)
    return -1


def find_repeat_number_inplace(nums: List[int]) -> int:
    """In-place swap: O(n) time, O(1) space.

    Loop invariant:
    - For all j < i: nums[j] == j OR nums[j] is a known duplicate.
    - Each swap places one element at its correct index.
    """
    i = 0
    while i < len(nums):
        if nums[i] == i:
            i += 1
            continue

        # nums[i] should be at index nums[i]
        target_idx = nums[i]
        if nums[target_idx] == nums[i]:
            # Found duplicate: two positions want the same value
            return nums[i]

        # Swap nums[i] to its correct position
        nums[i], nums[target_idx] = nums[target_idx], nums[i]
        # Do not increment i; check the new nums[i] again

    return -1


if __name__ == "__main__":
    assert find_repeat_number_hash([2, 3, 1, 0, 2, 5, 3]) in {2, 3}
    assert find_repeat_number_inplace([2, 3, 1, 0, 2, 5, 3]) in {2, 3}
    print("All tests passed for 剑指 Offer 03.")
