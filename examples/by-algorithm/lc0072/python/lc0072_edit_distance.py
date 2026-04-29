"""LeetCode 72. 编辑距离 — Python 实现

给你两个单词 word1 和 word2，请返回将 word1 转换成 word2 所使用的最少操作数。
你可以对一个单词进行如下三种操作：插入一个字符、删除一个字符、替换一个字符。

对标: LeetCode 72 / docs/13-LeetCode算法面试专题/06-面试专题/03-高频Top100-DP与贪心.md
"""


def min_distance(word1: str, word2: str) -> int:
    """计算将 word1 转换为 word2 的最小编辑距离。

    前置条件 (Pre):
        - word1, word2 长度范围 [0, 500]。

    后置条件 (Post):
        - 返回最小操作数（插入/删除/替换），使得 word1 变为 word2。

    核心思路:
        动态规划：设 dp[i][j] 为 word1[0..i-1] 转换为 word2[0..j-1] 的最小操作数。
        状态转移：
        - 若 word1[i-1] == word2[j-1]：dp[i][j] = dp[i-1][j-1]（无需操作）
        - 否则：dp[i][j] = 1 + min(dp[i-1][j],    # 删除 word1[i-1]
                                   dp[i][j-1],    # 插入 word2[j-1]
                                   dp[i-1][j-1])  # 替换
        初始条件：dp[0][j] = j（全插入），dp[i][0] = i（全删除）。

    复杂度:
        时间复杂度: O(m * n) — m, n 分别为两单词长度。
        空间复杂度: O(n) — 滚动数组优化，仅保留当前行和上一行。

    证明要点:
        - 最优子结构：最优解的最后一步必为三种操作之一。
          若最后操作为删除，则前面部分必为 word1[0..i-2] -> word2[0..j-1] 的最优解。
        - 无后效性：dp[i][j] 仅依赖于左侧、上方、左上方的值。
        - 完备性：所有可能的编辑序列均可由 DP 的决策路径表示。

    Args:
        word1: 源字符串。
        word2: 目标字符串。

    Returns:
        最小编辑距离。
    """
    m, n = len(word1), len(word2)
    # 使用一维数组优化空间
    prev = list(range(n + 1))
    curr = [0] * (n + 1)

    for i in range(1, m + 1):
        curr[0] = i
        for j in range(1, n + 1):
            if word1[i - 1] == word2[j - 1]:
                curr[j] = prev[j - 1]
            else:
                curr[j] = 1 + min(prev[j], curr[j - 1], prev[j - 1])
        prev, curr = curr, prev

    return prev[n]


if __name__ == "__main__":
    # LeetCode 官方示例
    assert min_distance("horse", "ros") == 3, "Example 1 failed"
    assert min_distance("intention", "execution") == 5, "Example 2 failed"

    # 边界条件
    assert min_distance("", "") == 0, "Both empty"
    assert min_distance("abc", "") == 3, "Delete all"
    assert min_distance("", "abc") == 3, "Insert all"
    assert min_distance("abc", "abc") == 0, "Identical"
    assert min_distance("kitten", "sitting") == 3, "Classic example"

    print("All tests passed.")
