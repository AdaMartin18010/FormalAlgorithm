package leetcode

import "testing"

func TestPickIndex(t *testing.T) {
	sol := ConstructorRandomPickIndex([]int{1, 2, 3, 3, 3})

	// 测试 target=3 时只返回有效索引
	for i := 0; i < 20; i++ {
		idx := sol.PickIndex(3)
		if idx != 2 && idx != 3 && idx != 4 {
			t.Errorf("PickIndex(3) returned invalid index %d", idx)
		}
	}

	if sol.PickIndex(1) != 0 {
		t.Error("PickIndex(1) should return 0")
	}
	if sol.PickIndex(2) != 1 {
		t.Error("PickIndex(2) should return 1")
	}
}

func TestPickIndexDistribution(t *testing.T) {
	sol := ConstructorRandomPickIndex([]int{1, 2, 3, 3, 3})
	freq := make(map[int]int)
	trials := 3000

	for i := 0; i < trials; i++ {
		idx := sol.PickIndex(3)
		freq[idx]++
	}

	for _, idx := range []int{2, 3, 4} {
		count := freq[idx]
		if count < 700 || count > 1300 {
			t.Errorf("Index %d frequency %d out of range", idx, count)
		}
	}
}
