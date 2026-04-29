"""LeetCode 70. 爬楼梯 — Python 实现

假设你正在爬楼梯。需要 n 阶你才能到达楼顶。
每次你可以爬 1 或 2 个台阶。你有多少种不同的方法可以爬到楼顶呢？

对标: LeetCode 70 / docs/13-LeetCode算法面试专题/06-面试专题/03-高频Top100-DP与贪心.md
"""


def climb_stairs(n: int) -> int:
    """计算爬到第 n 阶楼梯的不同方法数。

    前置条件 (Pre):
        - n 为整数，范围 [1, 45]。

    后置条件 (Post):
        - 返回从第 0 阶到达第 n 阶的不同方法总数。

    核心思路:
        动态规划：设 dp[i] 为到达第 i 阶的方法数。
        状态转移：dp[i] = dp[i-1] + dp[i-2]（最后一步跨 1 阶或 2 阶）。
        初始条件：dp[0] = 1, dp[1] = 1。
        优化：由于 dp[i] 只依赖前两个状态，使用滚动变量将空间优化至 O(1)。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(1) — 滚动变量。

    证明要点:
        - 最优子结构：到达第 i 阶的最后一步只能是 1 阶（从 i-1）或 2 阶（从 i-2）。
          因此方法数等于到达 i-1 和 i-2 的方法数之和。
        - 无后效性：dp[i] 的值仅由 dp[i-1] 和 dp[i-2] 决定，与更前面的状态无关。
        - 数学本质：dp[n] = F_{n+1}，即第 n+1 个斐波那契数。

    Args:
        n: 目标台阶数。

    Returns:
        爬到第 n 阶的不同方法数。
    """
    if n <= 2:
        return n
    prev2, prev1 = 1, 2
    for _ in range(3, n + 1):
        curr = prev1 + prev2
        prev2 = prev1
        prev1 = curr
    return prev1


if __name__ == "__main__":
    # LeetCode 官方示例
    assert climb_stairs(2) == 2, "Example 1 failed"
    assert climb_stairs(3) == 3, "Example 2 failed"

    # 边界条件
    assert climb_stairs(1) == 1, "Single step"
    assert climb_stairs(4) == 5, "Four steps"

    # 斐波那契验证
    assert climb_stairs(10) == 89, "Fibonacci check"
    assert climb_stairs(45) == 1836311903, "Max constraint"

    print("All tests passed.")
