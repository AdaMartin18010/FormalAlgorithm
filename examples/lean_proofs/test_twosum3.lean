def twoSumHash (nums : List Nat) (target : Nat) : Option (Nat × Nat) :=
  let rec aux (j : Nat) (seen : List (Nat × Nat)) : Option (Nat × Nat) :=
    if h : j < nums.length then
      let current := nums[j]'h
      let complement := target - current
      match seen with
      | [] => aux (j + 1) ((current, j) :: seen)
      | _ :: _ => none
    else
      none
    termination_by nums.length - j
    decreasing_by
      all_goals
        simp_wf
        <;> try omega
  aux 0 []
