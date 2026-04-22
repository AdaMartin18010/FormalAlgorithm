def twoSumHash (nums : List Nat) (target : Nat) : Option (Nat × Nat) :=
  let rec aux (j : Nat) (seen : List (Nat × Nat)) : Option (Nat × Nat) :=
    if h : j < nums.length then
      let current := nums[j]'h
      let complement := target - current
      if current = complement then
        some (0, j)
      else
        aux (j + 1) ((current, j) :: seen)
    else
      none
  aux 0 []
  termination_by nums.length - j
  decreasing_by
    all_goals
      simp_wf
      <;> try omega
