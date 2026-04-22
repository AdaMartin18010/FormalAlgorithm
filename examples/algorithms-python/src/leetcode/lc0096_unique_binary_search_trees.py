"""
LeetCode 96. Unique Binary Search Trees
链接: https://leetcode.com/problems/unique-binary-search-trees/
难度: Medium

题目描述:
给定一个整数 n，求恰由 n 个节点且节点值从 1 到 n 的二叉搜索树有多少种？

形式化规约:
  输入: n ∈ N
  输出: 结构不同的 BST 数量

最优解思路:
  卡特兰数 DP。对于每个根节点 i，左子树有 i-1 个节点，右子树有 n-i 个节点。
  dp[n] = Σ dp[i-1] * dp[n-i]，i = 1..n

复杂度:
  时间: O(n²)
  空间: O(n)

正确性要点:
  1. dp[0] = 1 表示空树有一种结构
  2. 以 i 为根时，左右子树独立组合，乘法原理
  3. 对所有可能的根求和，得到总方案数
"""


def num_trees(n: int) -> int:
    """
    卡特兰数动态规划求解不同的二叉搜索树数量。
    时间复杂度 O(n²)，空间复杂度 O(n)。
    """
    dp = [0] * (n + 1)
    dp[0] = 1  # 空树

    for nodes in range(1, n + 1):
        for root in range(1, nodes + 1):
            dp[nodes] += dp[root - 1] * dp[nodes - root]

    return dp[n]


if __name__ == "__main__":
    # 示例 1
    assert num_trees(3) == 5, f"Example 1 failed: {num_trees(3)}"
    # 示例 2
    assert num_trees(1) == 1, f"Example 2 failed: {num_trees(1)}"
    # 边界: n=0
    assert num_trees(0) == 1, f"Zero case failed: {num_trees(0)}"
    # 卡特兰数序列
    assert num_trees(2) == 2, f"C2 failed: {num_trees(2)}"
    assert num_trees(4) == 14, f"C4 failed: {num_trees(4)}"
    assert num_trees(5) == 42, f"C5 failed: {num_trees(5)}"

    print("All tests passed for LC 96 - Unique Binary Search Trees")
