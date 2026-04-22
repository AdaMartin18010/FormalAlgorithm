/-
Minimal stub for Mathlib.Data.List.Sort
-/

namespace List

universe u
variable {α : Type u}

/-- `Sorted r l` means that `l` is sorted with respect to the relation `r`. -/
def Sorted (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

end List
