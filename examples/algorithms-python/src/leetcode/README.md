# LeetCode 算法实现 — Python

## 目录定位

本目录存放 LeetCode 经典题目的工程级 Python 实现，作为 `docs/13-LeetCode算法面试专题/` 的可执行参考代码。所有实现遵循 LeetCode 官方函数签名与类型注解规范。

## 文件命名规范

```
lc{题号}_{题目简称}.py
```

示例：

- `lc0704_binary_search.py`
- `lc0033_search_in_rotated_sorted_array.py`
- `lc0153_find_minimum_in_rotated_sorted_array.py`

## 注释规范模板

每个公共函数必须包含以下 Google Style docstring：

```python
def search(nums: list[int], target: int) -> int:
    """在有序数组中查找目标值的索引。

    前置条件 (Pre):
        - nums 为升序排列的整数数组。
        - 元素取值范围为 [-10^4, 10^4]。

    后置条件 (Post):
        - 若 target 在 nums 中，返回其索引 i 满足 nums[i] == target。
        - 若 target 不在 nums 中，返回 -1。

    循环不变式:
        设当前搜索区间为 [left, right]（闭区间）。
        若 target 存在于 nums，则其索引必然位于 [left, right] 之内。

    复杂度:
        时间复杂度: O(log n) — 每次迭代搜索区间减半。
        空间复杂度: O(1) — 仅使用常数个额外变量。

    证明要点:
        - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
        - 终止性由区间长度严格递减保证。

    Args:
        nums: 升序排列的整数数组。
        target: 待查找的目标值。

    Returns:
        target 的索引，若不存在则返回 -1。
    """
```

## 测试规范

每个文件底部必须包含 `if __name__ == "__main__":` 测试块：

1. **LeetCode 官方示例用例**：覆盖题目给出的所有输入/输出对
2. **边界条件**：
   - 空数组 `[]`
   - 单元素数组 `[x]`
   - 全部相同元素 `[k, k, k, ...]`
   - 目标值为数组边界值（最小、最大）
3. **断言方式**：使用 `assert` 语句并附带描述性错误信息

```python
if __name__ == "__main__":
    # LeetCode 官方示例
    assert search([-1, 0, 3, 5, 9, 12], 9) == 4, "Example 1 failed"
    assert search([-1, 0, 3, 5, 9, 12], 2) == -1, "Example 2 failed"

    # 边界条件
    assert search([], 1) == -1, "Empty array should return -1"
    assert search([5], 5) == 0, "Single element found"
    assert search([5], 1) == -1, "Single element not found"

    print("All tests passed.")
```

## 与 docs/ 的交叉引用

- 算法范式：`docs/13-LeetCode算法面试专题/02-算法范式专题/`
- 数据结构：`docs/13-LeetCode算法面试专题/01-数据结构专题/`
- 复杂度分析：`docs/04-算法复杂度/`

在 docstring 的 "证明要点" 区块中使用相对路径引用，例如：

```
    - 正确性证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
```

## 代码风格

- 遵循 PEP 8 规范
- 使用类型注解（Python 3.9+ `list[int]` 语法）
- 函数名使用 `snake_case`
