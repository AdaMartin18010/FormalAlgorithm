def Multiset (α : Type) : Type := List α
instance : HAppend (Multiset α) (Multiset α) (Multiset α) := ⟨fun a b => a ++ b⟩
