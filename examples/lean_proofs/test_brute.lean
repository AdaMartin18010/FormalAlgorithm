def twoSumBruteForce (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  match nums with
  | [] => none
  | _ :: tl =>
      let rec findPair (i : Nat) (xs : List Int) : Option (Nat × Nat) :=
        match xs with
        | [] => none
        | x :: xs' =>
            let rec findMatch (j : Nat) (ys : List Int) : Option (Nat × Nat) :=
              match ys with
              | [] => none
              | y :: ys' =>
                  if x + y = target then
                    some (i, j)
                  else
                    findMatch (j + 1) ys'
            match findMatch (i + 1) xs' with
            | some pair => some pair
            | none => findPair (i + 1) xs'
      findPair 0 nums
  termination_by nums.length - i
  decreasing_by
    all_goals
      simp_wf
      <;> try omega
