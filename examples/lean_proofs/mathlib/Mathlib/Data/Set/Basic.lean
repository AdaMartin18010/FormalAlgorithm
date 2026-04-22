/-
Minimal stub for Mathlib.Data.Set.Basic
-/

def Set (α : Type) : Type := α → Prop

namespace Set

instance : Membership α (Set α) := ⟨fun x s => s x⟩

end Set
