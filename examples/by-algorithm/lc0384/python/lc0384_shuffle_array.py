"""
LeetCode 384. Shuffle an Array

Given an integer array nums, design an algorithm to randomly shuffle the array.
All permutations of the array should be equally likely.

Approach: Fisher-Yates (Knuth) Shuffle
- Iterate from the last element down to the first.
- At step i, pick a random index j in [0, i] and swap nums[i] with nums[j].

Correctness Proof (by induction on n):
Base case: n=1, trivially uniform.
Inductive step: For array of length n, the first iteration places a uniformly
random element at position n-1 (probability 1/n for each element).
The remaining n-1 positions are filled by the inductive hypothesis applied
to the subarray of length n-1. Thus every permutation has probability 1/n!.

Time: O(n), Space: O(1)
"""

import random
from typing import List


class Solution:
    def __init__(self, nums: List[int]):
        self.original = nums[:]
        self.nums = nums[:]

    def reset(self) -> List[int]:
        """Resets the array to its original configuration and returns it."""
        self.nums = self.original[:]
        return self.nums

    def shuffle(self) -> List[int]:
        """Returns a random shuffling of the array."""
        n = len(self.nums)
        for i in range(n - 1, 0, -1):
            j = random.randint(0, i)
            self.nums[i], self.nums[j] = self.nums[j], self.nums[i]
        return self.nums


# --- Tests ---
if __name__ == "__main__":
    nums = [1, 2, 3]
    sol = Solution(nums)

    # Test reset
    assert sol.reset() == [1, 2, 3]

    # Test shuffle (statistical; just check it's a valid permutation)
    shuffled = sol.shuffle()
    assert sorted(shuffled) == sorted(nums)

    # Test multiple shuffles produce valid permutations
    counts = {}
    trials = 60000
    for _ in range(trials):
        sol.reset()
        s = tuple(sol.shuffle())
        counts[s] = counts.get(s, 0) + 1

    # There are 6 permutations of [1,2,3]
    assert len(counts) == 6
    expected = trials / 6
    for perm, count in counts.items():
        # Allow 20% deviation for statistical test
        assert abs(count - expected) / expected < 0.2, f"Permutation {perm} biased: {count} vs {expected}"

    print("All tests passed.")
