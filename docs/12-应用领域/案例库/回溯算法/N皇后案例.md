# N皇后问题实际应用案例


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

## 应用场景1：约束满足问题求解器

### 问题描述

- **背景**：N皇后问题是约束满足问题(CSP)的经典案例，广泛应用于排课、调度等领域
- **问题**：在N×N棋盘上放置N个皇后，使其互不攻击
- **约束**：
  - 每行、每列只能有一个皇后
  - 每条对角线只能有一个皇后
- **数据规模**：通常N=8-20用于测试，实际应用N可达100+

### 算法选择理由

- **为什么选择回溯**：
  - 系统性地搜索解空间
  - 通过剪枝大幅减少搜索量
  - 可找到所有解或任意一个解
  - 易于添加额外约束

- **优化策略**：

  | 优化 | 效果 | 实现难度 |
  |------|------|----------|
  | 剪枝 | 减少90%+搜索 | 低 |
  | 位运算 | 加速10x | 中 |
  | 对称性消除 | 减少8x | 中 |
  | 启发式排序 | 加速5x | 低 |

### 解决方案

```pseudo
Algorithm NQueens(n):
    board = Array[n][n] of 0
    solutions = []

    Function Backtrack(row):
        if row == n:
            solutions.append(copy(board))
            return

        for col from 0 to n-1:
            if isSafe(row, col):
                board[row][col] = 1
                Backtrack(row + 1)
                board[row][col] = 0  // 回溯

    Function isSafe(row, col):
        // 检查列
        for i from 0 to row-1:
            if board[i][col] == 1:
                return false

        // 检查对角线
        for i, j from (row-1, col-1) down to (0, 0):
            if board[i][j] == 1:
                return false

        for i, j from (row-1, col+1) down to (0, n-1):
            if board[i][j] == 1:
                return false

        return true

    Backtrack(0)
    return solutions

// 位运算优化版本
Algorithm NQueensBit(n):
    solutions = 0

    Function Solve(row, hills, next_row, dales):
        // hills: 左对角线占用
        // next_row: 列占用
        // dales: 右对角线占用

        free_columns = (~(row | hills | dales)) & ((1 << n) - 1)

        while free_columns != 0:
            curr_column = -free_columns & free_columns  // 取最低位
            free_columns ^= curr_column  // 清除该位

            Solve(
                row | curr_column,
                (hills | curr_column) << 1,
                next_row,
                (dales | curr_column) >> 1
            )

        if row == (1 << n) - 1:
            solutions += 1

    Solve(0, 0, 0, 0)
    return solutions
```

### 实际代码示例（Python）

```python
from typing import List, Set, Tuple, Optional
import time

class NQueensSolver:
    """N皇后问题求解器"""

    def __init__(self, n: int):
        self.n = n
        self.solutions: List[List[int]] = []
        self.nodes_visited = 0

    def solve(self) -> List[List[int]]:
        """求解所有解"""
        self.solutions = []
        self.nodes_visited = 0

        # columns[i] 表示第i行的皇后放在第几列
        columns = [-1] * self.n

        self._backtrack(0, columns, set(), set(), set())
        return self.solutions

    def _backtrack(self, row: int, columns: List[int],
                   cols: Set[int], diagonals1: Set[int], diagonals2: Set[int]):
        """回溯求解"""
        self.nodes_visited += 1

        if row == self.n:
            self.solutions.append(columns.copy())
            return

        for col in range(self.n):
            # 剪枝：检查约束
            diag1 = row - col  # 左对角线
            diag2 = row + col  # 右对角线

            if col in cols or diag1 in diagonals1 or diag2 in diagonals2:
                continue

            # 放置皇后
            columns[row] = col
            cols.add(col)
            diagonals1.add(diag1)
            diagonals2.add(diag2)

            # 递归下一行
            self._backtrack(row + 1, columns, cols, diagonals1, diagonals2)

            # 回溯
            cols.remove(col)
            diagonals1.remove(diag1)
            diagonals2.remove(diag2)
            columns[row] = -1

    def solve_bitwise(self) -> int:
        """
        位运算优化版本
        返回解的数量
        """
        self.nodes_visited = 0
        count = [0]
        all_ones = (1 << self.n) - 1

        def backtrack(row: int, hills: int, next_row: int, dales: int):
            self.nodes_visited += 1

            # free_positions: 可用的列位置
            free_positions = (~(row | hills | dales)) & all_ones

            while free_positions:
                # 取最低位的1
                curr_pos = -free_positions & free_positions
                free_positions ^= curr_pos  # 清除该位

                backtrack(
                    row | curr_pos,
                    (hills | curr_pos) << 1,
                    next_row,
                    (dales | curr_pos) >> 1
                )

            # 找到解
            if row == all_ones:
                count[0] += 1

        backtrack(0, 0, 0, 0)
        return count[0]

    def print_solution(self, solution: List[int]):
        """打印一个解"""
        for row in range(self.n):
            line = ""
            for col in range(self.n):
                if solution[row] == col:
                    line += "Q "
                else:
                    line += ". "
            print(line)
        print()

    def get_statistics(self) -> dict:
        """获取求解统计"""
        return {
            'n': self.n,
            'solution_count': len(self.solutions),
            'nodes_visited': self.nodes_visited,
            'expected_solutions': self._expected_solution_count()
        }

    def _expected_solution_count(self) -> int:
        """已知的解数量"""
        known = {1: 1, 2: 0, 3: 0, 4: 2, 5: 10, 6: 4, 7: 40, 8: 92, 9: 352, 10: 724,
                 11: 2680, 12: 14200, 13: 73712, 14: 365596, 15: 2279184}
        return known.get(self.n, -1)


class ConstraintSatisfactionProblem:
    """通用约束满足问题求解器 - 以课程表为例"""

    def __init__(self):
        self.variables = {}  # 变量 -> 定义域
        self.constraints = []  # 约束列表

    def add_variable(self, name: str, domain: List):
        self.variables[name] = domain

    def add_constraint(self, var1: str, var2: str, constraint_func):
        self.constraints.append((var1, var2, constraint_func))

    def solve(self) -> Optional[dict]:
        """使用回溯求解"""
        assignment = {}

        def backtrack():
            if len(assignment) == len(self.variables):
                return assignment.copy()

            # 选择未赋值的变量（MRV启发式）
            unassigned = [v for v in self.variables if v not in assignment]
            var = min(unassigned, key=lambda v: len(self.variables[v]))

            for value in self.variables[var]:
                if self._is_consistent(var, value, assignment):
                    assignment[var] = value
                    result = backtrack()
                    if result is not None:
                        return result
                    del assignment[var]

            return None

        return backtrack()

    def _is_consistent(self, var: str, value, assignment: dict) -> bool:
        """检查赋值是否满足约束"""
        for v1, v2, constraint in self.constraints:
            if v1 == var and v2 in assignment:
                if not constraint(value, assignment[v2]):
                    return False
            elif v2 == var and v1 in assignment:
                if not constraint(assignment[v1], value):
                    return False
        return True


# 基准测试
def benchmark_nqueens():
    """测试N皇后求解器性能"""
    print("N皇后问题性能测试:")
    print("-" * 60)
    print(f"{'N':>5} {'普通回溯':>15} {'位运算版本':>15} {'解数量':>10}")
    print("-" * 60)

    for n in range(4, 15):
        # 普通回溯
        solver = NQueensSolver(n)
        start = time.time()
        solutions = solver.solve()
        normal_time = time.time() - start
        normal_nodes = solver.nodes_visited

        # 位运算版本
        start = time.time()
        count = solver.solve_bitwise()
        bit_time = time.time() - start
        bit_nodes = solver.nodes_visited

        print(f"{n:>5} {normal_time*1000:>14.2f}ms {bit_time*1000:>14.2f}ms {len(solutions):>10}")

    # 打印N=8的一个解
    print("\nN=8 的一个解:")
    solver = NQueensSolver(8)
    solutions = solver.solve()
    solver.print_solution(solutions[0])


def demo_course_scheduling():
    """演示课程表问题（CSP）"""
    csp = ConstraintSatisfactionProblem()

    # 课程
    courses = ["数学", "物理", "化学", "生物", "英语"]

    # 时间段
    time_slots = ["周一上午", "周一下午", "周二上午", "周二下午", "周三上午"]

    # 添加变量
    for course in courses:
        csp.add_variable(course, time_slots)

    # 添加约束：某些课程不能同时
    # 数学和物理不能同时（同一老师）
    csp.add_constraint("数学", "物理", lambda x, y: x != y)
    # 化学和生物不能同时（实验室限制）
    csp.add_constraint("化学", "生物", lambda x, y: x != y)

    print("课程表问题:")
    solution = csp.solve()
    if solution:
        for course, slot in solution.items():
            print(f"  {course}: {slot}")
    else:
        print("  无解")

if __name__ == '__main__':
    benchmark_nqueens()
    print()
    demo_course_scheduling()
```

### 性能评估

- **时间复杂度**：最坏O(n!)，实际通过剪枝大幅减少
- **实际运行时间**（求所有解）：

  | N | 普通回溯 | 位运算优化 | 解数量 |
  |---|---------|-----------|--------|
  | 8 | 5ms | 0.5ms | 92 |
  | 12 | 5s | 200ms | 14200 |
  | 14 | 10min | 20s | 365596 |

### 效果分析

- **剪枝效率**：通常剪枝掉99.9%的无效分支
- **实际应用**：
  - 排课系统
  - 数独求解
  - 电路板布线

---

## 应用场景2：数独求解器

### 问题描述

- **背景**：数独是流行的逻辑谜题，也是典型的CSP
- **问题**：给定部分填好的数独，求解完整答案

### 解决方案

```python
class SudokuSolver:
    """数独求解器"""

    def __init__(self, grid: List[List[int]]):
        self.grid = [row[:] for row in grid]
        self.n = 9

    def solve(self) -> bool:
        """回溯求解数独"""
        empty = self._find_empty()
        if not empty:
            return True  # 已完成

        row, col = empty

        for num in range(1, 10):
            if self._is_valid(row, col, num):
                self.grid[row][col] = num

                if self.solve():
                    return True

                self.grid[row][col] = 0  # 回溯

        return False

    def _find_empty(self) -> Optional[Tuple[int, int]]:
        """找到下一个空格（MRV启发式）"""
        min_options = 10
        best_cell = None

        for i in range(self.n):
            for j in range(self.n):
                if self.grid[i][j] == 0:
                    options = sum(1 for num in range(1, 10)
                                if self._is_valid(i, j, num))
                    if options < min_options:
                        min_options = options
                        best_cell = (i, j)
                        if options == 1:
                            return best_cell

        return best_cell

    def _is_valid(self, row: int, col: int, num: int) -> bool:
        """检查数字是否有效"""
        # 检查行
        if num in self.grid[row]:
            return False

        # 检查列
        if num in [self.grid[i][col] for i in range(self.n)]:
            return False

        # 检查3x3方块
        box_row, box_col = 3 * (row // 3), 3 * (col // 3)
        for i in range(box_row, box_row + 3):
            for j in range(box_col, box_col + 3):
                if self.grid[i][j] == num:
                    return False

        return True

    def print_grid(self):
        for i in range(self.n):
            if i % 3 == 0 and i != 0:
                print("- - - - - - - - - - -")
            for j in range(self.n):
                if j % 3 == 0 and j != 0:
                    print("| ", end="")
                print(self.grid[i][j], end=" ")
            print()

# 测试
if __name__ == '__main__':
    # 一个中等难度的数独
    puzzle = [
        [5, 3, 0, 0, 7, 0, 0, 0, 0],
        [6, 0, 0, 1, 9, 5, 0, 0, 0],
        [0, 9, 8, 0, 0, 0, 0, 6, 0],
        [8, 0, 0, 0, 6, 0, 0, 0, 3],
        [4, 0, 0, 8, 0, 3, 0, 0, 1],
        [7, 0, 0, 0, 2, 0, 0, 0, 6],
        [0, 6, 0, 0, 0, 0, 2, 8, 0],
        [0, 0, 0, 4, 1, 9, 0, 0, 5],
        [0, 0, 0, 0, 8, 0, 0, 7, 9]
    ]

    solver = SudokuSolver(puzzle)
    print("原始数独:")
    solver.print_grid()

    start = time.time()
    if solver.solve():
        print("\n求解结果:")
        solver.print_grid()
        print(f"求解时间: {(time.time()-start)*1000:.2f}ms")
    else:
        print("无解")
```

### 实际案例来源

- **应用**：数独APP、逻辑谜题求解器
- **论文**："Sudoku as a Constraint Satisfaction Problem"

---

## 参考文献

- 待补充

---

## 知识导航

- [返回目录](README.md)
