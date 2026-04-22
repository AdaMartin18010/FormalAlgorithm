/-
Minimal Mathlib.Tactic stub providing commonly used tactics.
-/

-- linarith is not available in core; provide a fallback macro
macro "linarith" : tactic => `(tactic| omega)
macro "linarith" "[" _ts:term,* "]" : tactic => `(tactic| omega)

-- aesop is sometimes used; stub it
macro "aesop" : tactic => `(tactic| simp_all)
macro "aesop" "(" _args* ")" : tactic => `(tactic| simp_all)
