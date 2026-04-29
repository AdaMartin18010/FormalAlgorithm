"""LeetCode 37. 解数独 — Python 实现

编写一个程序，通过填充空格来解决数独问题。假设唯一解。

对标: LeetCode 37 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md
"""

from typing import List


def solve_sudoku(board: List[List[str]]) -> None:
    """原地修改 board，填充空格得到合法数独解。

    前置条件 (Pre):
        - board 为 9x9 的二维列表，元素为 '1'-'9' 或 '.'。
        - 输入保证有且仅有一个解。

    后置条件 (Post):
        - board 被原地修改为合法的完整数独。
        - 每行、每列、每个 3x3 宫格均包含 '1'-'9' 各一次。

    回溯不变式 (Backtrack Invariant):
        - 已填充的格子均满足数独约束（行、列、宫格唯一）。
        - 未填充的格子标记为 '.'。
        - 若找到解，则立即返回。

    剪枝条件 (Pruning):
        对于候选数字 d，若当前行、列或 3x3 宫格已包含 d，则剪枝。

    复杂度:
        时间复杂度: O(9^m) — m 为空格数，每个空格最多尝试 9 个数字。
        空间复杂度: O(m) — 递归栈深度最多为 m。

    证明要点:
        - 终止性：每次递归填充一个空格，空格数严格递减，必在有限步内终止。
        - 正确性：由于剪枝仅排除与已有约束冲突的数字，不会排除合法解；找到的第一个完整填充即为唯一解。

    Args:
        board: 9x9 数独棋盘，原地修改。
    """
    rows = [set() for _ in range(9)]
    cols = [set() for _ in range(9)]
    boxes = [set() for _ in range(9)]
    empty = []

    # 初始化已有数字
    for r in range(9):
        for c in range(9):
            val = board[r][c]
            if val == ".":
                empty.append((r, c))
            else:
                rows[r].add(val)
                cols[c].add(val)
                boxes[(r // 3) * 3 + (c // 3)].add(val)

    def backtrack(idx: int) -> bool:
        if idx == len(empty):
            return True
        r, c = empty[idx]
        box_idx = (r // 3) * 3 + (c // 3)
        for d in map(str, range(1, 10)):
            if d in rows[r] or d in cols[c] or d in boxes[box_idx]:
                continue
            # 做选择
            board[r][c] = d
            rows[r].add(d)
            cols[c].add(d)
            boxes[box_idx].add(d)
            # 递归
            if backtrack(idx + 1):
                return True
            # 撤销选择
            board[r][c] = "."
            rows[r].remove(d)
            cols[c].remove(d)
            boxes[box_idx].remove(d)
        return False

    backtrack(0)


if __name__ == "__main__":
    # LeetCode 官方示例
    board = [
        ["5", "3", ".", ".", "7", ".", ".", ".", "."],
        ["6", ".", ".", "1", "9", "5", ".", ".", "."],
        [".", "9", "8", ".", ".", ".", ".", "6", "."],
        ["8", ".", ".", ".", "6", ".", ".", ".", "3"],
        ["4", ".", ".", "8", ".", "3", ".", ".", "1"],
        ["7", ".", ".", ".", "2", ".", ".", ".", "6"],
        [".", "6", ".", ".", ".", ".", "2", "8", "."],
        [".", ".", ".", "4", "1", "9", ".", ".", "5"],
        [".", ".", ".", ".", "8", ".", ".", "7", "9"],
    ]
    solve_sudoku(board)
    expected = [
        ["5", "3", "4", "6", "7", "8", "9", "1", "2"],
        ["6", "7", "2", "1", "9", "5", "3", "4", "8"],
        ["1", "9", "8", "3", "4", "2", "5", "6", "7"],
        ["8", "5", "9", "7", "6", "1", "4", "2", "3"],
        ["4", "2", "6", "8", "5", "3", "7", "9", "1"],
        ["7", "1", "3", "9", "2", "4", "8", "5", "6"],
        ["9", "6", "1", "5", "3", "7", "2", "8", "4"],
        ["2", "8", "7", "4", "1", "9", "6", "3", "5"],
        ["3", "4", "5", "2", "8", "6", "1", "7", "9"],
    ]
    assert board == expected, f"Sudoku solve failed: {board}"

    print("All tests passed.")
