/-
Minimal stub for Mathlib.Data.Multiset.Basic
-/

import Std

/-- A `Multiset` is a list up to permutation.
    For stub purposes, we just wrap a List. -/
def Multiset (α : Type) : Type := List α

instance : Coe (List α) (Multiset α) := ⟨id⟩
instance : Coe (Multiset α) (List α) := ⟨id⟩

namespace Multiset

/-- Multiset addition is list append (up to permutation).
    For the stub we just use list append. -/
def add (s t : Multiset α) : Multiset α := (s : List α) ++ (t : List α)

instance : HAppend (Multiset α) (Multiset α) (Multiset α) := ⟨add⟩
instance : Append (Multiset α) := ⟨add⟩
instance : Add (Multiset α) := ⟨add⟩

end Multiset
