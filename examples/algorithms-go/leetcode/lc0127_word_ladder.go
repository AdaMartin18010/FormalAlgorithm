// LeetCode 127. Word Ladder
// 链接: https://leetcode.com/problems/word-ladder/
// 难度: Hard
//
// 算法: 双向 BFS
// 时间复杂度: O(N * L^2)，N=wordList 大小，L=单词长度
// 空间复杂度: O(N)

package leetcode

import (
	"container/list"
)

// LadderLength 返回从 beginWord 到 endWord 的最短转换序列长度。
func LadderLength(beginWord string, endWord string, wordList []string) int {
	wordSet := make(map[string]bool, len(wordList))
	for _, w := range wordList {
		wordSet[w] = true
	}
	if !wordSet[endWord] {
		return 0
	}
	if beginWord == endWord {
		return 1
	}

	// 双向 BFS
	beginVisited := map[string]int{beginWord: 1}
	endVisited := map[string]int{endWord: 1}
	beginQueue := list.New()
	endQueue := list.New()
	beginQueue.PushBack(beginWord)
	endQueue.PushBack(endWord)

	for beginQueue.Len() > 0 && endQueue.Len() > 0 {
		// 从较小的一侧扩展
		if beginQueue.Len() > endQueue.Len() {
			beginQueue, endQueue = endQueue, beginQueue
			beginVisited, endVisited = endVisited, beginVisited
		}

		levelSize := beginQueue.Len()
		for i := 0; i < levelSize; i++ {
			elem := beginQueue.Front()
			beginQueue.Remove(elem)
			word := elem.Value.(string)
			currentLen := beginVisited[word]

			// 生成所有可能的下一个单词
			wordBytes := []byte(word)
			for j := 0; j < len(wordBytes); j++ {
				original := wordBytes[j]
				for c := byte('a'); c <= 'z'; c++ {
					if c == original {
						continue
					}
					wordBytes[j] = c
					nextWord := string(wordBytes)

					if !wordSet[nextWord] {
						continue
					}

					// 检查是否在另一侧已访问
					if endLen, ok := endVisited[nextWord]; ok {
						return currentLen + endLen
					}

					if _, ok := beginVisited[nextWord]; !ok {
						beginVisited[nextWord] = currentLen + 1
						beginQueue.PushBack(nextWord)
					}
				}
				wordBytes[j] = original
			}
		}
	}

	return 0
}
