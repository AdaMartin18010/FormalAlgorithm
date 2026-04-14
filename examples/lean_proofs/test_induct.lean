def mergeSort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: zs =>
    let n := (x :: y :: zs).length / 2
    have _ : ((x :: y :: zs).take n).length < (x :: y :: zs).length := by simp_wf; omega
    have _ : ((x :: y :: zs).drop n).length < (x :: y :: zs).length := by simp_wf; omega
    mergeSort ((x :: y :: zs).take n) ++ mergeSort ((x :: y :: zs).drop n)
  termination_by xs.length
  decreasing_by simp_wf; omega

#check mergeSort.induct
