"""LeetCode 127. 单词接龙 — Python 实现

给定两个单词 beginWord 和 endWord，以及一个字典 wordList，返回从 beginWord 到 endWord 的最短转换序列的长度。

每次转换只能改变一个字母，且中间单词必须在字典中。

对标: LeetCode 127 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md
"""

from typing import List
from collections import deque, defaultdict


def ladder_length(begin_word: str, end_word: str, word_list: List[str]) -> int:
    """返回从 begin_word 到 end_word 的最短转换序列长度。

    前置条件 (Pre):
        - begin_word, end_word 长度相同，由小写英文字母组成。
        - word_list 中单词长度与 begin_word 相同。
        - 所有单词由小写英文字母组成。

    后置条件 (Post):
        - 若存在转换序列，返回序列长度（包含 begin_word 和 end_word）。
        - 若不存在，返回 0。

    BFS 层级不变式 (Layer Invariant):
        BFS 第 d 层恰好包含距 begin_word 最短转换距离为 d 的所有单词。

    复杂度:
        时间复杂度: O(N * L^2) — N 为 word_list 长度，L 为单词长度。
        空间复杂度: O(N * L) — 访问标记集合与队列。

    证明要点:
        - 正确性：BFS 按层扩展，第一次到达 end_word 时即为最短路径（无权图最短路径定理）。
        - 双向 BFS 优化：从两端同时 BFS，每次扩展较小的一侧，将搜索空间从 O(b^d) 降为 O(b^(d/2))。

    Args:
        begin_word: 起始单词。
        end_word: 目标单词。
        word_list: 合法中间单词列表。

    Returns:
        最短转换序列长度，不存在则返回 0。
    """
    word_set = set(word_list)
    if end_word not in word_set:
        return 0

    if begin_word == end_word:
        return 1

    # 双向 BFS
    begin_visited = {begin_word}
    end_visited = {end_word}
    begin_queue = deque([begin_word])
    end_queue = deque([end_word])
    length = 1

    def neighbors(word: str):
        """生成与 word 仅相差一个字母且在字典中的单词。"""
        chars = list(word)
        for i in range(len(chars)):
            original = chars[i]
            for c in "abcdefghijklmnopqrstuvwxyz":
                if c == original:
                    continue
                chars[i] = c
                new_word = "".join(chars)
                if new_word in word_set:
                    yield new_word
            chars[i] = original

    while begin_queue and end_queue:
        # 总是扩展较小的一侧
        if len(begin_queue) > len(end_queue):
            begin_queue, end_queue = end_queue, begin_queue
            begin_visited, end_visited = end_visited, begin_visited

        length += 1
        for _ in range(len(begin_queue)):
            word = begin_queue.popleft()
            for nb in neighbors(word):
                if nb in begin_visited:
                    continue
                if nb in end_visited:
                    return length
                begin_visited.add(nb)
                begin_queue.append(nb)

    return 0


if __name__ == "__main__":
    # LeetCode 官方示例
    assert ladder_length("hit", "cog", ["hot", "dot", "dog", "lot", "log", "cog"]) == 5, "Example 1 failed"
    assert ladder_length("hit", "cog", ["hot", "dot", "dog", "lot", "log"]) == 0, "Example 2 failed"

    # 边界条件
    assert ladder_length("a", "a", []) == 1, "Same word"
    assert ladder_length("a", "b", ["b"]) == 2, "Single step"
    assert ladder_length("abc", "def", []) == 0, "Empty word list"

    print("All tests passed.")
