/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.Match1

/-! # Match1 (Algorithm 1) -/

namespace RewbTests.Match1

open Rewb

/-- The automaton of `e₁ = ε`: one state, initial and accepting, with no transitions. -/
def epsilon : Simulator (Fin 1) Char := ⟨fun _ _ => ∅, {0}, {0}⟩

/-! `w = abab` and `α = ab`, with `e₀ = e₁ = e₂ = ε` and `e = ab`, so that `w = ε·ab·ε·ab·ε`.
`Pre` holds only for the empty prefix, `Suf` only for the empty suffix, and `Pre_α` only for `α`
itself. -/

example : match1 epsilon ['a', 'b', 'a', 'b'] ['a', 'b']
    (List.occurrences ['a', 'b'] ['a', 'b', 'a', 'b'])
    (fun i => decide (i = 0)) (fun j => decide (j = 4)) (fun k => decide (k = 2)) = true := by
  decide

/-! Remark 11 claims that Match1 is correct for every repeat `α`, not only for nonoverlapping
ones. It is not: take `w = aaaa`, `α = aa`, `e₀ = ε|a`, `e = aa` and `e₁ = e₂ = ε`. The three
occurrences of `α` overlap, and `Pre` holds before the first two. The injection due after the
first `α` is overwritten in `ique` by the one due after the second before it happens, so Match1
returns false. -/

example : match1 epsilon ['a', 'a', 'a', 'a'] ['a', 'a']
    (List.occurrences ['a', 'a'] ['a', 'a', 'a', 'a'])
    (fun i => decide (i ≤ 1)) (fun j => decide (j = 4)) (fun k => decide (k = 2)) = false := by
  decide

/-- Yet `e` matches `α`, and `r_α` matches `w` as `aaaa = ε·aa·ε·aa·ε`. -/
example : ['a', 'a'] ∈ ({x | x = ['a', 'a']} : Language Char) ∧
    ['a', 'a', 'a', 'a'] ∈
      rewbLangWith ({x | x = [] ∨ x = ['a']} : Language Char) 1 1 ['a', 'a'] :=
  ⟨rfl, mem_rewbLangWith.mpr ⟨[], [], [], Or.inl rfl, rfl, rfl, rfl⟩⟩

end RewbTests.Match1
