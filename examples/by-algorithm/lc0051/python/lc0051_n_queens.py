"""LeetCode 51. N 皇后 — Python 实现

在 n×n 的棋盘上放置 n 个皇后，使它们不能互相攻击（任意两个皇后不在同一行、同一列、同一斜线），返回所有 distinct 的解法。

对标: LeetCode 51 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md
"""

from typing import List


def solve_n_queens(n: int) -> List[List[str]]:
    """返回 n 皇后问题的所有解。

    前置条件 (Pre):
        - 1 <= n <= 9。

    后置条件 (Post):
        - 返回所有 distinct 的棋盘布局，每个布局为 n 个字符串的列表。
        - 每个字符串长度为 n，'Q' 表示皇后，'.' 表示空位。
        - 任意两个皇后不在同一行、同一列、同一斜线。

    回溯不变式 (Backtrack Invariant):
        设当前正在处理第 row 行，已放置皇后的列集合为 cols，主对角线集合为 diag1，副对角线集合为 diag2。
        - 已放置的皇后互不攻击。
        - 第 0 到 row-1 行每行恰好有一个皇后。
        - diag1 中保存的是 row - col，diag2 中保存的是 row + col。

    剪枝条件 (Pruning):
        对于候选列 col，若满足 col in cols 或 (row - col) in diag1 或 (row + col) in diag2，则剪枝。

    复杂度:
        时间复杂度: O(n!) — 第 0 行有 n 种选择，第 1 行最多 n-1 种，依此类推。
        空间复杂度: O(n) — 递归栈深度为 n，加上 cols/diag1/diag2 集合。

    证明要点:
        - 不遗漏：逐行枚举所有合法列位置，DFS 遍历全部可行解空间。
        - 不重复：每行只放一个皇后，且棋盘表示为字符串列表，不同放置顺序产生不同解。
        - 剪枝正确性：若 col 与已有皇后同列或同对角线，则后续无论如何放置都会冲突，剪去该分支安全。

    Args:
        n: 棋盘大小及皇后数量。

    Returns:
        所有合法棋盘布局的列表。
    """
    result: List[List[str]] = []
    board: List[int] = []  # board[row] = col，表示第 row 行皇后放在第 col 列

    def backtrack(row: int, cols: int, diag1: int, diag2: int) -> None:
        """使用位运算优化的回溯函数。

        cols, diag1, diag2 为位掩码，第 i 位为 1 表示第 i 列/对角线已被占用。
        """
        if row == n:
            # 构造棋盘
            solution = []
            for c in board:
                row_str = ["."] * n
                row_str[c] = "Q"
                solution.append("".join(row_str))
            result.append(solution)
            return

        # 可用位置掩码：1 表示可用
        available = ((1 << n) - 1) & ~(cols | diag1 | diag2)
        while available:
            # 取最低位的 1
            lsb = available & -available
            col = (lsb.bit_length() - 1)
            board.append(col)
            backtrack(
                row + 1,
                cols | lsb,
                (diag1 | lsb) << 1,
                (diag2 | lsb) >> 1,
            )
            board.pop()
            available &= available - 1  # 清除最低位的 1

    backtrack(0, 0, 0, 0)
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    n4 = solve_n_queens(4)
    expected_4 = [
        [".Q..", "...Q", "Q...", "..Q."],
        ["..Q.", "Q...", "...Q", ".Q.."],
    ]
    assert n4 == expected_4, f"Example n=4 failed: {n4}"

    n1 = solve_n_queens(1)
    assert n1 == [["Q"]], "Example n=1 failed"

    # 边界条件
    assert solve_n_queens(2) == [], "n=2 should have no solution"
    assert solve_n_queens(3) == [], "n=3 should have no solution"
    assert len(solve_n_queens(8)) == 92, "n=8 should have 92 solutions"

    print("All tests passed.")
