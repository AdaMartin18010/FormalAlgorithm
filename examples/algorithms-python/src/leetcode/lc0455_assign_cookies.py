"""LeetCode 455. 分发饼干 — Python 实现

假设你是一位很棒的家长，想要给你的孩子们一些小饼干。但是，每个孩子最多只能给一块饼干。
对每个孩子 i，都有一个胃口值 g[i]，这是能让孩子们满足胃口的饼干的最小尺寸；
并且每块饼干 j，都有一个尺寸 s[j]。如果 s[j] >= g[i]，我们可以将这个饼干 j 分配给孩子 i，
这个孩子会得到满足。你的目标是尽可能满足越多数量的孩子，并输出这个最大数值。

对标: LeetCode 455 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
"""

from typing import List


def find_content_children(g: List[int], s: List[int]) -> int:
    """计算最多能满足的孩子数量。

    前置条件 (Pre):
        - g 为孩子胃口值数组，s 为饼干尺寸数组。
        - 1 <= len(g), len(s) <= 3·10^4。

    后置条件 (Post):
        - 返回能满足的孩子的最大数量。

    核心思路:
        贪心策略：用能满足某个孩子的最小饼干去满足他。
        1. 将孩子胃口数组 g 和饼干数组 s 分别排序。
        2. 双指针：对于每个孩子，找到能满足他的最小饼干。
        3. 若当前饼干太小，则放弃该饼干。

    复杂度:
        时间复杂度: O(m log m + n log n) — 排序主导。
        空间复杂度: O(1) — 忽略排序栈空间。

    证明要点:
        - 交换论证：设最优解中某孩子被更大的饼干满足，将其替换为最小满足饼干不降低解的质量。
        - 对每一步贪心选择应用交换论证，得到全局最优。

    Args:
        g: 孩子胃口值数组。
        s: 饼干尺寸数组。

    Returns:
        最多能满足的孩子数量。
    """
    g.sort()
    s.sort()

    child = cookie = 0
    while child < len(g) and cookie < len(s):
        if s[cookie] >= g[child]:
            child += 1
        cookie += 1

    return child


if __name__ == "__main__":
    # LeetCode 官方示例
    assert find_content_children([1, 2, 3], [1, 1]) == 1, "Example 1 failed"
    assert find_content_children([1, 2], [1, 2, 3]) == 2, "Example 2 failed"

    # 边界条件
    assert find_content_children([1], [1]) == 1, "Single match"
    assert find_content_children([2], [1]) == 0, "No match"
    assert find_content_children([1, 2, 3], [3, 3, 3]) == 3, "All satisfy"
    assert find_content_children([], [1, 2]) == 0, "No children"
    assert find_content_children([1, 2], []) == 0, "No cookies"

    print("All tests passed.")
