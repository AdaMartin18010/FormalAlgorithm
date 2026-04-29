"""LeetCode 15. 三数之和 — Python 实现

给你一个整数数组 nums，判断是否存在三元组 [nums[i], nums[j], nums[k]]
满足 i != j, i != k, j != k，且 nums[i] + nums[j] + nums[k] == 0。
返回所有和为 0 且不重复的三元组。

对标: LeetCode 15 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
"""

from typing import List


def three_sum(nums: List[int]) -> List[List[int]]:
    """找出数组中所有和为 0 的不重复三元组。

    前置条件 (Pre):
        - nums 为整数数组，长度 ∈ [0, 5000]，元素值 ∈ [-10^5, 10^5]。

    后置条件 (Post):
        - 返回所有满足 i < j < k 且 nums[i] + nums[j] + nums[k] == 0 的三元组列表。
        - 结果中不包含重复的三元组（即相同数值组合只保留一次）。
        - 每个三元组内部按非降序排列。

    算法框架:
        1. 将数组排序，得到非降序序列。
        2. 固定第一个元素 nums[i]，问题转化为在 i 右侧寻找两数之和为 -nums[i]。
        3. 使用对撞指针 l, r 在 [i+1, n-1] 范围内搜索。
        4. 通过排序后的去重策略保证结果唯一性。

    循环不变式（对撞指针阶段）:
        设固定 i，左指针 l = i+1，右指针 r = n-1。
        不变式：所有满足 j < l 或 k > r 的配对 (j,k) 均已被考察或不可能构成解。

        维护：
        - 初始 l = i+1, r = n-1，显然成立。
        - 计算 s = nums[i] + nums[l] + nums[r]：
          * s == 0：记录解，并收缩 l,r 以跳过重复值。
          * s < 0：nums[l] 太小，需要更大的左端点，l += 1。
          * s > 0：nums[r] 太大，需要更小的右端点，r -= 1。
        - 每次移动都排除了当前 l 或 r 不可能再参与构成解的情况。

    复杂度:
        时间复杂度: O(n^2) — 外层固定 i 为 O(n)，内层对撞指针为 O(n)。
        空间复杂度: O(1) — 不计输出空间，仅使用常数个指针和变量。
                   排序需要 O(log n) 栈空间（或 O(n) 若用非原地排序）。

    证明要点:
        - 不遗漏解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
        - 核心：排序后，对固定的 i，所有可能的两数之和解必在 [i+1, n-1] 内，
          且对撞指针的移动策略保证每个配对至多被跳过一次。

    Args:
        nums: 整数数组。

    Returns:
        所有不重复的三元组列表，每个三元组按升序排列。
    """
    nums.sort()
    n = len(nums)
    result: List[List[int]] = []

    for i in range(n - 2):
        # 去重：跳过相同的 nums[i]
        if i > 0 and nums[i] == nums[i - 1]:
            continue

        # 剪枝：若最小三数之和 > 0，后续不可能有解
        if nums[i] + nums[i + 1] + nums[i + 2] > 0:
            break
        # 剪枝：若当前 nums[i] 与最大两数之和 < 0，当前 i 无解
        if nums[i] + nums[n - 2] + nums[n - 1] < 0:
            continue

        target = -nums[i]
        left, right = i + 1, n - 1

        while left < right:
            total = nums[i] + nums[left] + nums[right]
            if total == 0:
                result.append([nums[i], nums[left], nums[right]])
                # 跳过重复值
                while left < right and nums[left] == nums[left + 1]:
                    left += 1
                while left < right and nums[right] == nums[right - 1]:
                    right -= 1
                left += 1
                right -= 1
            elif total < 0:
                left += 1
            else:
                right -= 1

    return result


if __name__ == "__main__":
    # 示例 1
    result1 = three_sum([-1, 0, 1, 2, -1, -4])
    expected1 = [[-1, -1, 2], [-1, 0, 1]]
    assert result1 == expected1, f"Example 1 failed: {result1}"

    # 示例 2
    result2 = three_sum([0, 1, 1])
    assert result2 == [], f"Example 2 failed: {result2}"

    # 示例 3
    result3 = three_sum([0, 0, 0])
    assert result3 == [[0, 0, 0]], f"Example 3 failed: {result3}"

    # 边界：空数组
    assert three_sum([]) == [], "Empty array"

    # 边界：不足三个元素
    assert three_sum([1, 2]) == [], "Less than 3 elements"

    # 边界：全正数
    assert three_sum([1, 2, 3]) == [], "All positive"

    # 边界：全负数
    assert three_sum([-3, -2, -1]) == [], "All negative"

    # 边界：大量重复
    result_dup = three_sum([0, 0, 0, 0, 0])
    assert result_dup == [[0, 0, 0]], f"Many duplicates: {result_dup}"

    print("All tests passed.")
