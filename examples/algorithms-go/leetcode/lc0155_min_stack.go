package leetcode

// LeetCode 155. Min Stack
// 最小栈
//
// Design a stack that supports push, pop, top, and retrieving the minimum element in constant time.

// MinStack 主栈 + 辅助栈同步维护最小值
// Main stack + auxiliary stack maintaining minimum
type MinStack struct {
	stack    []int
	minStack []int
}

// ConstructorMinStack initializes the stack object
func ConstructorMinStack() MinStack {
	return MinStack{stack: []int{}, minStack: []int{}}
}

// Push pushes the element val onto the stack
func (this *MinStack) Push(val int) {
	this.stack = append(this.stack, val)
	if len(this.minStack) == 0 {
		this.minStack = append(this.minStack, val)
	} else {
		minVal := val
		if this.minStack[len(this.minStack)-1] < minVal {
			minVal = this.minStack[len(this.minStack)-1]
		}
		this.minStack = append(this.minStack, minVal)
	}
}

// Pop removes the element on the top of the stack
func (this *MinStack) Pop() {
	this.stack = this.stack[:len(this.stack)-1]
	this.minStack = this.minStack[:len(this.minStack)-1]
}

// Top gets the top element of the stack
func (this *MinStack) Top() int {
	return this.stack[len(this.stack)-1]
}

// GetMin retrieves the minimum element in the stack
func (this *MinStack) GetMin() int {
	return this.minStack[len(this.minStack)-1]
}
