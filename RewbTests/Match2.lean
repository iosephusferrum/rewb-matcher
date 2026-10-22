/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.Match2

/-! # Match2 (Algorithm 2) -/

namespace RewbTests.Match2

open Rewb

/-! Example 16: `w = abbabbabbabba` over `{a, b}` and `α = bba`, with `e = Σ*` and `e₂ = (ΣΣ)*`,
where `e₀` matches the words with at most two `b`s and `e₁` those with an odd number of `b`s, at
least three. -/

/-- The automaton of `e₁`. Its state counts the `b`s read so far: `0`, `1` and `2` exactly, `3` an
odd number from three on and `4` an even number from four on. -/
def oddB : Simulator (Fin 5) Char where
  step q c := {if c = 'b' then (if q = 4 then 3 else q + 1) else q}
  start := {0}
  accept := {3}

/-- The input word. -/
def w : List Char := ['a', 'b', 'b', 'a', 'b', 'b', 'a', 'b', 'b', 'a', 'b', 'b', 'a']

/-- The right-maximal repeat that the example examines. -/
def α : List Char := ['b', 'b', 'a']

/-- `Pre`: `e₀` matches the prefix of length `i` when it has at most two `b`s. -/
def pre (i : ℕ) : Bool := decide ((w.take i).count 'b' ≤ 2)

/-- `Suf`: `e₂` matches the suffix from position `j` when its length is even. -/
def suf (j : ℕ) : Bool := decide ((w.drop j).length % 2 = 0)

/-- `Pre_α`: `e = Σ*` matches every prefix of `α`. -/
def preα (_ : ℕ) : Bool := true

/-- The occurrences of `α`: the paper's `Idx_α = [2, 5, 8, 11]`, in 0-based positions. -/
example : List.occurrences α w = [1, 4, 7, 10] := by decide

/-! Figure 1 shows `Pre` and `Suf` for the positions `0` to `13`. Its column `j` of `Suf` is our
`suf j`, the paper's `Suf[j + 1]`, so the columns `11` and `13` that the text calls `Suf[11]` and
`Suf[13]` are `Suf[12]` and `Suf[14]`. -/

example : (List.range 14).map pre =
    [true, true, true, true, true, false, false, false, false, false, false, false, false,
      false] := by
  decide

example : (List.range 14).map suf =
    [false, true, false, true, false, true, false, true, false, true, false, true, false,
      true] := by
  decide

/-- Line 8 at the occurrence `10` (the paper's `11`): Intmed injects before `ba` and at the end,
after the prefixes `b` and `bba` of `α` (the squares at the paper's positions `11` and `13`), so
`T` holds the states after `ba` and after nothing. -/
example : intmed oddB α 10 1 preα suf = {0, 1} := by decide

/-- Proposition 13 at the occurrence `10`: the occurrences `1` and `4` have `Pre`, so component `t`
holds what `t` reaches by reading `bbabba` and `bba`. From `1` both reach `3`, which accepts. -/
example : match2Set oddB w α (List.occurrences α w) pre 10 1 = {3} := by decide

example : match2Set oddB w α (List.occurrences α w) pre 10 0 = {2, 4} := by decide

/-- So Match2 returns true at the occurrence `10`, with `β = b`: `w` is `a · b · babbabba · b · ba`,
where `e₁` matches `babbabba`, the rest `ba` of `α` followed by `bbabba`. -/
example : match2 oddB w α (List.occurrences α w) pre suf preα = true := by decide

end RewbTests.Match2
