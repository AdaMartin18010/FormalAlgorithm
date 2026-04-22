"""LeetCode 312. 戳气球 / Burst Balloons — Python 实现

有 n 个气球，编号为 0 到 n-1，每个气球上都标有一个数字，这些数字存在数组 nums 中。

现在要求你戳破所有的气球。戳破第 i 个气球，你可以获得 nums[left] * nums[i] * nums[right] 个硬币。
这里的 left 和 right 表示和 i 相邻的两个气球的序号。注意当你戳破了气球 i 后，
气球 left 和气球 right 就变成了相邻的气球。

求所能获得硬币的最大数量。

题目链接: https://leetcode.com/problems/burst-balloons/
难度: Hard

对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.6
"""

from typing import List


def max_coins(nums: List[int]) -> int:
    """计算戳破所有气球能获得的最大硬币数。

    前置条件 (Pre):
        - nums 为非负整数数组，长度范围 [1, 300]，元素范围 [0, 100]。

    后置条件 (Post):
        - 返回最大可获得硬币数。

    核心思路:
        区间动态规划。关键技巧：逆向思考（加气球而非戳气球）。

        在数组两端添加虚拟气球 1：val = [1] + nums + [1]
        dp[i][j] = 开区间 (i, j) 内所有气球都戳破能获得的最大硬币数。

        状态转移：枚举 (i, j) 内最后一个被戳破的气球 k
        dp[i][j] = max(dp[i][k] + dp[k][j] + val[i] * val[k] * val[j])
          - dp[i][k]: 左子区间 (i, k) 的最优值
          - dp[k][j]: 右子区间 (k, j) 的最优值
          - val[i]*val[k]*val[j]: 最后戳破 k 获得的硬币（此时 i 和 j 相邻于 k 两侧）

        填表顺序：按区间长度从小到大，确保子区间已计算。

    复杂度:
        时间复杂度: O(n^3) — 区间长度 × 区间起点 × 分割点。
        空间复杂度: O(n^2) — 二维 DP 表。

    证明要点:
        - 最优子结构：设 k 为 (i, j) 内最后一个被戳破的气球。此时 (i, k) 和 (k, j)
          内的气球都已被戳破，i 和 j 相邻于 k 两侧，获得硬币 val[i]*val[k]*val[j]。
          两个子区间的戳破顺序相互独立，各自必为最优解，否则替换为更优子解可提升整体解。
        - 无后效性：dp[i][j] 只依赖于更小区间的 dp 值。
        - 区间归纳：对区间长度 len = j - i 归纳，基例 len=1 时 dp[i][j]=0 正确，
          归纳步骤由引理保证。

    Args:
        nums: 气球上的数字数组。

    Returns:
        最大可获得硬币数。
    """
    n = len(nums)
    # 扩展数组，两端添加虚拟气球 1
    val = [1] + nums + [1]
    m = n + 2

    # dp[i][j] = 开区间 (i, j) 能获得的最大硬币
    dp = [[0] * m for _ in range(m)]

    # 按区间长度从小到大填表
    for length in range(2, n + 2):  # length = j - i
        for i in range(m - length):
            j = i + length
            for k in range(i + 1, j):
                dp[i][j] = max(
                    dp[i][j],
                    dp[i][k] + dp[k][j] + val[i] * val[k] * val[j]
                )

    return dp[0][n + 1]


if __name__ == "__main__":
    # LeetCode 官方示例
    assert max_coins([3, 1, 5, 8]) == 167, "Example 1 failed"
    # nums = [3,1,5,8] --> [3,5,8] --> [3,8] --> [8] --> []
    # coins = 3*1*5 + 3*5*8 + 1*3*8 + 1*8*1 = 15 + 120 + 24 + 8 = 167

    assert max_coins([1, 5]) == 10, "Example 2 failed"  # 1*1*5 + 1*5*1 = 10

    # 边界条件
    assert max_coins([5]) == 5, "Single balloon"  # 1*5*1 = 5
    assert max_coins([3, 1]) == 6, "Two balloons"
    assert max_coins([1, 1, 1, 1]) == 4, "All ones"
    assert max_coins([0, 0]) == 0, "All zeros"

    print("All tests passed.")
