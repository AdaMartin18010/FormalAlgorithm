package leetcode

import (
	"reflect"
	"testing"
)

func TestRotate3x3(t *testing.T) {
	m := [][]int{
		{1, 2, 3},
		{4, 5, 6},
		{7, 8, 9},
	}
	Rotate(m)
	expected := [][]int{
		{7, 4, 1},
		{8, 5, 2},
		{9, 6, 3},
	}
	if !reflect.DeepEqual(m, expected) {
		t.Errorf("Rotate 3x3 = %v, want %v", m, expected)
	}
}

func TestRotate4x4(t *testing.T) {
	m := [][]int{
		{5, 1, 9, 11},
		{2, 4, 8, 10},
		{13, 3, 6, 7},
		{15, 14, 12, 16},
	}
	Rotate(m)
	expected := [][]int{
		{15, 13, 2, 5},
		{14, 3, 4, 1},
		{12, 6, 8, 9},
		{16, 7, 10, 11},
	}
	if !reflect.DeepEqual(m, expected) {
		t.Errorf("Rotate 4x4 = %v, want %v", m, expected)
	}
}

func TestRotate1x1(t *testing.T) {
	m := [][]int{{42}}
	Rotate(m)
	expected := [][]int{{42}}
	if !reflect.DeepEqual(m, expected) {
		t.Errorf("Rotate 1x1 = %v, want %v", m, expected)
	}
}

func TestRotate2x2(t *testing.T) {
	m := [][]int{
		{1, 2},
		{3, 4},
	}
	Rotate(m)
	expected := [][]int{
		{3, 1},
		{4, 2},
	}
	if !reflect.DeepEqual(m, expected) {
		t.Errorf("Rotate 2x2 = %v, want %v", m, expected)
	}
}
