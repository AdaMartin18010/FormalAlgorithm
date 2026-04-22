package algorithms

import (
	"reflect"
	"testing"
)

func TestKMPSearch(t *testing.T) {
	got := KMPSearch("abababc", "ababc")
	want := []int{2}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("KMPSearch() = %v, want %v", got, want)
	}
}

func TestZFunction(t *testing.T) {
	got := ZFunction("aaaaa")
	want := []int{0, 4, 3, 2, 1}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("ZFunction() = %v, want %v", got, want)
	}
}

func TestManacher(t *testing.T) {
	p := Manacher("abba")
	maxR := 0
	for _, v := range p {
		if v > maxR { maxR = v }
	}
	if maxR < 4 {
		t.Errorf("Manacher max radius too small: %d", maxR)
	}
}
