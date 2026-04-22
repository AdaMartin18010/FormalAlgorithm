// 剑指 Offer 09. 用两个栈实现队列
// https://leetcode.cn/problems/yong-liang-ge-zhan-shi-xian-dui-lie-lcof/
//
// Problem: Implement a queue using two stacks.
// Operations: appendTail (enqueue), deleteHead (dequeue).
//
// Formal specification:
// - Pre: none
// - Invariant: stackIn holds new elements; stackOut holds elements in FIFO order.
//   When stackOut is empty, pop all from stackIn and push to stackOut.
// - Post: deleteHead returns the oldest element or -1 if empty.
//
// Correctness proof:
//   - appendTail: pushes to stackIn. O(1) amortized.
//   - deleteHead: if stackOut not empty, pop (FIFO). If empty, transfer all from stackIn.
//     Each element is pushed once to stackIn and popped once to stackOut, then popped once.
//     Total operations per element: 3 pushes/pops → amortized O(1).
//
// Reference: docs/面试指南/06-面试专题/04-剑指Offer精选形式化证明.md

package leetcode

type CQueue struct {
	stackIn  []int // for appendTail
	stackOut []int // for deleteHead
}

func Constructor() CQueue {
	return CQueue{
		stackIn:  make([]int, 0),
		stackOut: make([]int, 0),
	}
}

func (this *CQueue) AppendTail(value int) {
	this.stackIn = append(this.stackIn, value)
}

func (this *CQueue) DeleteHead() int {
	if len(this.stackOut) == 0 {
		// Transfer all elements from stackIn to stackOut
		for len(this.stackIn) > 0 {
			// Pop from stackIn
			top := this.stackIn[len(this.stackIn)-1]
			this.stackIn = this.stackIn[:len(this.stackIn)-1]
			// Push to stackOut
			this.stackOut = append(this.stackOut, top)
		}
	}

	if len(this.stackOut) == 0 {
		return -1
	}

	// Pop from stackOut
	res := this.stackOut[len(this.stackOut)-1]
	this.stackOut = this.stackOut[:len(this.stackOut)-1]
	return res
}
