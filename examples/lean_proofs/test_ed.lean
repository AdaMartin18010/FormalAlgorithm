def editDistance {α : Type} [BEq α] (xs ys : List α) : Nat :=
  match xs, ys with
  | [], [] => 0
  | [], _ :: ys' => 1 + editDistance [] ys'
  | _ :: xs', [] => 1 + editDistance xs' []
  | x :: xs', y :: ys' =>
      if x == y then
        editDistance xs' ys'
      else
        1 + min (min (editDistance xs' ys) (editDistance xs ys')) (editDistance xs' ys')

example : editDistance ([] : List Nat) ([] : List Nat) = ([] : List Nat).length := rfl
