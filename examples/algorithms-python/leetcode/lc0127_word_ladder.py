"""
LeetCode 127. Word Ladder
链接: https://leetcode.com/problems/word-ladder/
难度: Hard

算法: 双向 BFS
时间复杂度: O(N * L^2)，N=wordList 大小，L=单词长度
空间复杂度: O(N)
"""

from typing import List
from collections import deque


class Solution:
    def ladderLength(self, beginWord: str, endWord: str, wordList: List[str]) -> int:
        """
        返回从 beginWord 到 endWord 的最短转换序列长度。
        
        形式化规约:
        - 前置条件: endWord 在 wordList 中
        - 后置条件: 返回最短转换序列长度，若不存在则返回 0
        
        算法: 双向 BFS，从两端同时搜索，相遇时返回路径长度。
        复杂度优化: 单向 BFS 访问 O(b^d) 节点，双向 BFS 访问 O(b^{d/2})。
        """
        word_set = set(wordList)
        if endWord not in word_set:
            return 0
        
        if beginWord == endWord:
            return 1
        
        # 双向 BFS
        begin_visited = {beginWord: 1}
        end_visited = {endWord: 1}
        begin_queue = deque([beginWord])
        end_queue = deque([endWord])
        
        while begin_queue and end_queue:
            # 从较小的一侧扩展，保证效率
            if len(begin_queue) > len(end_queue):
                begin_queue, end_queue = end_queue, begin_queue
                begin_visited, end_visited = end_visited, begin_visited
            
            # 扩展当前层
            for _ in range(len(begin_queue)):
                word = begin_queue.popleft()
                current_len = begin_visited[word]
                
                # 生成所有可能的下一个单词（改变一个字符）
                for i in range(len(word)):
                    for c in 'abcdefghijklmnopqrstuvwxyz':
                        if c == word[i]:
                            continue
                        next_word = word[:i] + c + word[i+1:]
                        
                        if next_word not in word_set:
                            continue
                        
                        # 检查是否在另一侧已访问
                        if next_word in end_visited:
                            return current_len + end_visited[next_word]
                        
                        if next_word not in begin_visited:
                            begin_visited[next_word] = current_len + 1
                            begin_queue.append(next_word)
        
        return 0


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1
    begin1, end1 = "hit", "cog"
    word_list1 = ["hot", "dot", "dog", "lot", "log", "cog"]
    res1 = sol.ladderLength(begin1, end1, word_list1)
    print(f"Test 1: {begin1} -> {end1}")
    print(f"Result: {res1} (expected: 5)")  # hit -> hot -> dot -> dog -> cog
    assert res1 == 5
    
    # 测试用例 2: endWord 不在 wordList 中
    begin2, end2 = "hit", "cog"
    word_list2 = ["hot", "dot", "dog", "lot", "log"]
    res2 = sol.ladderLength(begin2, end2, word_list2)
    print(f"\nTest 2: {begin2} -> {end2}")
    print(f"Result: {res2} (expected: 0)")
    assert res2 == 0
    
    # 测试用例 3
    begin3, end3 = "a", "c"
    word_list3 = ["a", "b", "c"]
    res3 = sol.ladderLength(begin3, end3, word_list3)
    print(f"\nTest 3: {begin3} -> {end3}")
    print(f"Result: {res3} (expected: 2)")  # a -> c
    assert res3 == 2
    
    print("\nAll tests passed!")
