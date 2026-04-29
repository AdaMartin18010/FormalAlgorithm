package leetcode

import "testing"

func TestComputeArea(t *testing.T) {
	// 示例 1
	if got := ComputeArea(-3, 0, 3, 4, 0, -1, 9, 2); got != 45 {
		t.Errorf("ComputeArea example 1 = %d, want 45", got)
	}

	// 示例 2：无重叠
	if got := ComputeArea(-2, -2, 2, 2, -4, -4, -3, -3); got != 17 {
		t.Errorf("ComputeArea example 2 = %d, want 17", got)
	}

	// 部分重叠
	if got := ComputeArea(0, 0, 2, 2, 1, 1, 3, 3); got != 7 {
		t.Errorf("ComputeArea partial overlap = %d, want 7", got)
	}

	// 一个包含另一个
	if got := ComputeArea(0, 0, 4, 4, 1, 1, 2, 2); got != 16 {
		t.Errorf("ComputeArea contain = %d, want 16", got)
	}

	// 边相接（无重叠）
	if got := ComputeArea(0, 0, 2, 2, 2, 0, 4, 2); got != 8 {
		t.Errorf("ComputeArea edge touch = %d, want 8", got)
	}

	// 角相接（无重叠）
	if got := ComputeArea(0, 0, 1, 1, 1, 1, 2, 2); got != 2 {
		t.Errorf("ComputeArea corner touch = %d, want 2", got)
	}

	// 大数值测试
	if got := ComputeArea(-10000, -10000, 10000, 10000, -10000, -10000, 10000, 10000); got != 400000000 {
		t.Errorf("ComputeArea large = %d, want 400000000", got)
	}
}
