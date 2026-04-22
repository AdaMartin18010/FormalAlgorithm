/-
Minimal stub for Mathlib.Data.List.Basic
-/

export List (Pairwise)

universe u
variable {α : Type u}

/-- `Sorted r l` means that `l` is sorted with respect to the relation `r`. -/
def Sorted (r : α → α → Prop) (l : List α) : Prop :=
  l.Pairwise r

/-- `Chain R l` means that all adjacent elements in `l` satisfy `R`. -/
inductive Chain (R : α → α → Prop) : List α → Prop
  | nil : Chain R []
  | singleton (a : α) : Chain R [a]
  | cons (a b : α) (l : List α) : R a b → Chain R (b :: l) → Chain R (a :: b :: l)

/-- Safe list lookup by index, returns `none` if out of bounds. -/
def get? (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', i+1 => get? xs' i
