"""
LeetCode 51. N-Queens
链接: https://leetcode.com/problems/n-queens/
难度: Hard

算法: 回溯 + 约束剪枝
时间复杂度: O(n!)（最坏，实际远小于）
空间复杂度: O(n)
"""

from typing import List


class Solution:
    def solveNQueens(self, n: int) -> List[List[str]]:
        """
        求解 n 皇后问题，返回所有合法布局。
        
        形式化规约:
        - 前置条件: n ∈ [1, 9]
        - 后置条件: 返回所有满足约束的棋盘布局
        
        约束函数: 同列、同主对角线、同反对角线不能同时存在皇后
        优化: 用三个集合分别记录已占用的列、主对角线、反对角线，实现 O(1) 冲突检测。
        """
        res: List[List[str]] = []
        board = [['.' for _ in range(n)] for _ in range(n)]
        
        def backtrack(row: int, cols: set, diag1: set, diag2: set) -> None:
            if row == n:
                # 找到一个完整解
                res.append([''.join(r) for r in board])
                return
            
            for col in range(n):
                d1, d2 = row - col, row + col
                # 约束检查: 列、主对角线、反对角线
                if col in cols or d1 in diag1 or d2 in diag2:
                    continue
                
                # 做选择: 在 (row, col) 放置皇后
                board[row][col] = 'Q'
                cols.add(col)
                diag1.add(d1)
                diag2.add(d2)
                
                # 递归到下一行
                backtrack(row + 1, cols, diag1, diag2)
                
                # 撤销选择
                board[row][col] = '.'
                cols.remove(col)
                diag1.remove(d1)
                diag2.remove(d2)
        
        backtrack(0, set(), set(), set())
        return res


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1: n = 4
    res4 = sol.solveNQueens(4)
    print(f"n = 4, solutions: {len(res4)} (expected: 2)")
    for board in res4:
        for row in board:
            print(row)
        print()
    assert len(res4) == 2
    
    # 测试用例 2: n = 1
    res1 = sol.solveNQueens(1)
    print(f"n = 1, solutions: {len(res1)} (expected: 1)")
    assert len(res1) == 1
    
    # 测试用例 3: n = 8
    res8 = sol.solveNQueens(8)
    print(f"n = 8, solutions: {len(res8)} (expected: 92)")
    assert len(res8) == 92
    
    print("\nAll tests passed!")
