def f (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [], [] => 0
  | [], _ :: ys' => 1 + f [] ys'
  | _ :: xs', [] => 1 + f xs' []
  | x :: xs', y :: ys' =>
      if x == y then f xs' ys'
      else 1 + min (min (f xs' ys) (f xs ys')) (f xs' ys')
termination_by xs.length + ys.length
decreasing_by
  all_goals
    simp_wf
    <;> simp +arith
    <;> unfold List.length at *
    <;> omega
