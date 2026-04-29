package leetcode

import (
	"reflect"
	"testing"
)

// Helper: 从 slice 构建链表
func buildList(vals []int) *ListNode {
	dummy := &ListNode{Val: 0}
	curr := dummy
	for _, v := range vals {
		curr.Next = &ListNode{Val: v}
		curr = curr.Next
	}
	return dummy.Next
}

// Helper: 链表转 slice
func listToSlice(head *ListNode) []int {
	if head == nil {
		return nil
	}
	result := []int{}
	for head != nil {
		result = append(result, head.Val)
		head = head.Next
	}
	return result
}

func TestMergeTwoLists(t *testing.T) {
	tests := []struct {
		name     string
		l1       []int
		l2       []int
		expected []int
	}{
		{"normal", []int{1, 2, 4}, []int{1, 3, 4}, []int{1, 1, 2, 3, 4, 4}},
		{"empty both", nil, nil, nil},
		{"one empty", nil, []int{0}, []int{0}},
		{"with negatives", []int{-10, -5, 0, 5}, []int{-8, -3, 10}, []int{-10, -8, -5, -3, 0, 5, 10}},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := listToSlice(mergeTwoLists(buildList(tt.l1), buildList(tt.l2)))
			if !reflect.DeepEqual(got, tt.expected) {
				t.Errorf("mergeTwoLists() = %v, want %v", got, tt.expected)
			}
		})
	}
}
