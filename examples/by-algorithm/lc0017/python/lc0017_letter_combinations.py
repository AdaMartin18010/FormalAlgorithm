"""LeetCode 17. 电话号码的字母组合 — Python 实现

给定一个仅包含数字 2-9 的字符串，返回所有它能表示的字母组合。

对标: LeetCode 17 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md
"""

from typing import List


def letter_combinations(digits: str) -> List[str]:
    """返回 digits 能表示的所有字母组合。

    前置条件 (Pre):
        - digits 仅由 '2'-'9' 组成。
        - 0 <= len(digits) <= 4。

    后置条件 (Post):
        - 返回所有可能的字母组合列表。
        - 若 digits 为空，返回空列表。
        - 每个组合长度为 len(digits)。

    回溯不变式 (Backtrack Invariant):
        - path 为当前已选择的前缀字符串。
        - |path| 等于当前处理到的 digits 索引。
        - path 中第 i 个字符来自 digits[i] 对应的字母集合。

    复杂度:
        时间复杂度: O(3^m * 4^n) — m 为对应 3 个字母的数字个数，n 为对应 4 个字母的数字个数。
        空间复杂度: O(len(digits)) — 递归栈深度。

    证明要点:
        - 不遗漏：对每个数字，枚举其对应的所有字母，DFS 遍历笛卡尔积的全部元素。
        - 不重复：digits 固定，每个位置独立选择，不同选择序列产生不同组合。

    Args:
        digits: 由数字 2-9 组成的字符串。

    Returns:
        所有字母组合的列表。
    """
    if not digits:
        return []

    phone = {
        "2": "abc",
        "3": "def",
        "4": "ghi",
        "5": "jkl",
        "6": "mno",
        "7": "pqrs",
        "8": "tuv",
        "9": "wxyz",
    }

    result: List[str] = []
    n = len(digits)

    def backtrack(idx: int, path: List[str]) -> None:
        if idx == n:
            result.append("".join(path))
            return
        for ch in phone[digits[idx]]:
            path.append(ch)
            backtrack(idx + 1, path)
            path.pop()

    backtrack(0, [])
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert set(letter_combinations("23")) == {
        "ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"
    }, "Example 1 failed"

    assert letter_combinations("") == [], "Example 2 failed"
    assert letter_combinations("2") == ["a", "b", "c"], "Example 3 failed"

    # 边界条件
    assert len(letter_combinations("79")) == 16, "7 has 4 letters, 9 has 4 letters => 16"

    print("All tests passed.")
