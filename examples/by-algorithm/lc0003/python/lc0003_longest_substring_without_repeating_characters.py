"""LeetCode 3. 无重复字符的最长子串 — Python 实现

给定一个字符串 s，找出其中不含有重复字符的最长子串的长度。

对标: LeetCode 3 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
"""


def length_of_longest_substring(s: str) -> int:
    """计算不含重复字符的最长子串长度。

    前置条件 (Pre):
        - s 为字符串，长度 ∈ [0, 5 * 10^4]。
        - s 由英文字母、数字、符号和空格组成。

    后置条件 (Post):
        - 返回 max_{0 ≤ l ≤ r < n} (r - l + 1)，其中 s[l..r] 不含重复字符。
        - 若 s 为空，返回 0。

    算法框架:
        滑动窗口：维护窗口 [left, right]，保证窗口内无重复字符。
        使用哈希表记录每个字符最后出现的位置。
        当发现重复字符时，将 left 收缩到重复字符上次出现位置的右侧。

    窗口不变式 WindowInvariant(left, right):
        s[left..right] 中所有字符均唯一。

        维护：
        - 初始 left = 0，窗口为空或仅含一个字符，不变式成立。
        - 扩展 right：考察 s[right]。
          * 若 s[right] 不在窗口中（或上次出现位置 < left），直接扩展。
          * 若 s[right] 在窗口中，将 left 移动到上次出现位置 + 1，
            保证新窗口内无重复。
        - 更新 s[right] 的最后出现位置。

        终止推出：right 遍历完所有字符，期间记录的最大窗口大小即为答案。

    复杂度:
        时间复杂度: O(n) — right 指针遍历字符串一次，left 指针最多移动 n 次。
        空间复杂度: O(min(m, n)) — m 为字符集大小，哈希表最多存储窗口内字符。

    证明要点:
        - 不遗漏最优解的证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
        - 核心：任何最优子串的右端点必被 right 指针访问到，此时 left 已收缩到
          保证窗口内无重复的最左位置，故该子串必被考察。

    Args:
        s: 输入字符串。

    Returns:
        不含重复字符的最长子串长度。
    """
    char_index: dict[str, int] = {}
    max_len = 0
    left = 0

    for right, ch in enumerate(s):
        if ch in char_index and char_index[ch] >= left:
            left = char_index[ch] + 1
        char_index[ch] = right
        max_len = max(max_len, right - left + 1)

    return max_len


if __name__ == "__main__":
    # 示例 1
    assert length_of_longest_substring("abcabcbb") == 3, "Example 1 failed"

    # 示例 2
    assert length_of_longest_substring("bbbbb") == 1, "Example 2 failed"

    # 示例 3
    assert length_of_longest_substring("pwwkew") == 3, "Example 3 failed"

    # 边界：空字符串
    assert length_of_longest_substring("") == 0, "Empty string"

    # 边界：单字符
    assert length_of_longest_substring("a") == 1, "Single char"

    # 边界：全不同
    assert length_of_longest_substring("abcdef") == 6, "All distinct"

    # 边界：重复字符分散
    assert length_of_longest_substring("abba") == 2, "Scattered repeats"

    # 边界：空格和符号
    assert length_of_longest_substring(" !@# !@#$") == 5, "Special chars"

    print("All tests passed.")
