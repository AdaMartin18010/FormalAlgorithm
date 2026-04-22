def Multiset (α : Type) : Type := List α
instance : Coe (List α) (Multiset α) := ⟨id⟩
instance : Coe (Multiset α) (List α) := ⟨id⟩

def add (s t : Multiset α) : Multiset α := (s : List α) ++ (t : List α)
instance : HAppend (Multiset α) (Multiset α) (Multiset α) := ⟨add⟩
