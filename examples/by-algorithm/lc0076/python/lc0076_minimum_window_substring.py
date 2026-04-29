"""LeetCode 76. 最小覆盖子串 — Python 实现

给你一个字符串 s、一个字符串 t，返回 s 中涵盖 t 所有字符的最小子串。
如果不存在符合条件的子串，返回空字符串 ""。

对标: LeetCode 76 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
"""

from collections import Counter


def min_window(s: str, t: str) -> str:
    """找出 s 中涵盖 t 所有字符的最小子串。

    前置条件 (Pre):
        - s, t 由大写/小写英文字母组成。
        - len(s) ∈ [1, 10^5], len(t) ∈ [1, 10^5]。

    后置条件 (Post):
        - 返回 s 的最短子串 substr，使得 t 中每个字符在 substr 中出现次数
          均不少于在 t 中的出现次数。
        - 若不存在，返回空字符串。

    算法框架:
        滑动窗口 + 双哈希表：
        - need：记录 t 中各字符的需求量。
        - window：记录当前窗口中各字符的实际数量。
        - valid：记录窗口中满足需求（数量 ≥ need）的字符种类数。

    窗口不变式 WindowInvariant(left, right):
        window 准确记录 s[left..right] 中各字符的出现次数。
        valid 等于 window[ch] ≥ need[ch] 的字符种类数（只考虑 need 中的字符）。

        维护：
        - 初始 left = 0，窗口为空，valid = 0。
        - 扩展 right：将 s[right] 加入 window。
          * 若该字符在 need 中且 window[ch] == need[ch]，valid += 1。
        - 当 valid == len(need) 时（窗口已覆盖 t），尝试收缩 left：
          * 更新最小窗口记录。
          * 将 s[left] 移出 window。
          * 若移出的是 need 中字符且 window[ch] < need[ch]，valid -= 1。
          * left += 1，继续尝试收缩。

    复杂度:
        时间复杂度: O(|s| + |t|) — 摊还分析：right 遍历 s 一次，left 最多移动 |s| 次。
        空间复杂度: O(|Σ|) — Σ 为字符集大小，此处为 52（大小写字母），
                   故实际为 O(1)。

    证明要点:
        - 窗口收缩正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
        - 核心：当窗口已覆盖 t 时，收缩左边界不会丢失最优性，
          因为更短的窗口仍可能满足覆盖条件。

    Args:
        s: 源字符串。
        t: 目标字符集合字符串。

    Returns:
        最小覆盖子串，若不存在返回空字符串。
    """
    if not s or not t:
        return ""

    need = Counter(t)
    window: dict[str, int] = {}
    valid = 0

    left = 0
    start = 0
    min_len = float("inf")

    for right, ch in enumerate(s):
        # 扩展窗口
        window[ch] = window.get(ch, 0) + 1
        if ch in need and window[ch] == need[ch]:
            valid += 1

        # 尝试收缩窗口
        while valid == len(need):
            if right - left + 1 < min_len:
                min_len = right - left + 1
                start = left

            left_ch = s[left]
            window[left_ch] -= 1
            if left_ch in need and window[left_ch] < need[left_ch]:
                valid -= 1
            left += 1

    return "" if min_len == float("inf") else s[start : start + int(min_len)]


if __name__ == "__main__":
    # 示例 1
    assert min_window("ADOBECODEBANC", "ABC") == "BANC", "Example 1 failed"

    # 示例 2
    assert min_window("a", "a") == "a", "Example 2 failed"

    # 示例 3
    assert min_window("a", "aa") == "", "Example 3 failed"

    # 边界：s 和 t 相同
    assert min_window("abc", "abc") == "abc", "Same strings"

    # 边界：t 在 s 开头
    assert min_window("abcdef", "abc") == "abc", "At beginning"

    # 边界：t 在 s 末尾
    assert min_window("xyzabc", "abc") == "abc", "At end"

    # 边界：大小写敏感
    assert min_window("Aa", "a") == "a", "Case sensitive"

    # 边界：重复字符
    assert min_window("aaabbbccc", "abc") == "abbbc", "Repeated chars"

    print("All tests passed.")
