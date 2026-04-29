package leetcode

// LeetCode 232. Implement Queue using Stacks
// 用栈实现队列
//
// Implement a first in first out (FIFO) queue using only two stacks.

// MyQueue 双栈法实现队列 FIFO 语义
// Two-stack approach for FIFO semantics
type MyQueue struct {
	inStack  []int
	outStack []int
}

// ConstructorQueue initializes the queue object
func ConstructorQueue() MyQueue {
	return MyQueue{inStack: []int{}, outStack: []int{}}
}

// Push pushes element x to the back of queue
func (this *MyQueue) Push(x int) {
	this.inStack = append(this.inStack, x)
}

// Pop removes the element from in front of queue and returns that element
// Amortized O(1)
func (this *MyQueue) Pop() int {
	this.Peek()
	val := this.outStack[len(this.outStack)-1]
	this.outStack = this.outStack[:len(this.outStack)-1]
	return val
}

// Peek gets the front element
// Transfer only when outStack is empty
func (this *MyQueue) Peek() int {
	if len(this.outStack) == 0 {
		for len(this.inStack) > 0 {
			val := this.inStack[len(this.inStack)-1]
			this.inStack = this.inStack[:len(this.inStack)-1]
			this.outStack = append(this.outStack, val)
		}
	}
	return this.outStack[len(this.outStack)-1]
}

// Empty returns whether the queue is empty
func (this *MyQueue) Empty() bool {
	return len(this.inStack) == 0 && len(this.outStack) == 0
}
