/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.ForCslib.Occurrence
public import Rewb.ForCslib.Repeat
public import Rewb.Timed.Main

/-!
# Theorem 5: the time of Main

Main (Section 3) builds the arrays `Pre` and `Suf`, checks `e₀ e₁ e₂` if `e` matches `ε`, then
runs `Match(α)` for every right-maximal repeat `α` of `w`, which EnumRM lists with its occurrence
array `Idx_α` (Appendix A), building the array `Pre_α` for each. The timed `main` takes these
constructions and the enumeration as given timed computations, with the costs the paper takes
from the literature or from simulation; everything else is timed in the cost model of
`Rewb.Timed.Simulation`.

Theorem 5 bounds the time of Main by `O(n² + n(m_e₀ + m_e₂) + µ_right · n(m_e + m²_e₁))`, with
`µ_right ≤ n - 1` right-maximal repeats. `time_main_le` is this bound in the cost model: the
constructions of `Pre` and `Suf`, the enumeration, `C.step` per position for the check of
`e₀ e₁ e₂`, and, for each of at most `n - 1` right-maximal repeats, `Pre_α` and `Match(α)`, at most
`n · (7 + 2 · C.sumStep + 4 · C.step)` since `α` occurs at most `n` times.

## Main definitions

* `Rewb.Timed.main`: Main, timed.

## Main statements

* `Rewb.Timed.ret_main`: the timed Main computes `Rewb.main`, so that it is correct
  (`Rewb.main_eq_true_iff`, the correctness part of Theorem 5).
* `Rewb.Timed.time_main_le`: the time bound of Theorem 5.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb.Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

/-- `List.anyM` in `TimeM` computes `List.any`. -/
@[simp]
theorem ret_anyM {β : Type*} (p : β → TimeM ℕ Bool) (l : List β) :
    ⟪l.anyM p⟫ = l.any fun b => ⟪p b⟫ := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.anyM, TimeM.ret_bind, List.any_cons]
    cases ⟪p b⟫ <;> simp [ih]

/-- `List.anyM` in `TimeM` takes at most the times of all its calls: it stops at the first
`true`. -/
theorem time_anyM_le {β : Type*} (p : β → TimeM ℕ Bool) (l : List β) :
    (l.anyM p).time ≤ (l.map fun b => (p b).time).sum := by
  induction l with
  | nil => simp [List.anyM]
  | cons b l ih =>
    simp only [List.anyM, TimeM.time_bind, List.map_cons, List.sum_cons]
    cases ⟪p b⟫
    · simp only; omega
    · simp only [TimeM.time_pure]; omega

/-- A sum of terms that are each at most `K` is at most `K` times their number. -/
private theorem sum_le_length_mul {l : List ℕ} {K : ℕ} (h : ∀ x ∈ l, x ≤ K) :
    l.sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Returning `true` early, or going on, is an `||`. -/
private theorem ret_ite_pure_true (b : Bool) (X : TimeM ℕ Bool) :
    ⟪if b = true then pure true else X⟫ = (b || ⟪X⟫) := by
  cases b <;> rfl

-- The states and symbols live in `Type`: `TimeM ℕ` is a monad on one universe, and Main binds
-- the list of right-maximal repeats on its way to a `Bool`.
variable {State Symbol : Type} [DecidableEq State] (M : Simulator State Symbol) (C : Cost)

/-- The check of `e₀ e₁ e₂`, run only when `b` says that `e` matches `ε`. -/
def matchEmptyIf (b : Bool) (w : List Symbol) (pre suf : ℕ → Bool) : TimeM ℕ Bool :=
  if b then matchEmpty M C w pre suf else pure false

@[simp]
theorem ret_matchEmptyIf (b : Bool) (w : List Symbol) (pre suf : ℕ → Bool) :
    ⟪matchEmptyIf M C b w pre suf⟫ = (b && Rewb.matchEmpty M w pre suf) := by
  cases b <;> simp [matchEmptyIf]

theorem time_matchEmptyIf_le (b : Bool) (w : List Symbol) (pre suf : ℕ → Bool) :
    (matchEmptyIf M C b w pre suf).time ≤ (2 * w.length + 1) * C.step := by
  cases b
  · simp [matchEmptyIf]
  · simpa [matchEmptyIf] using time_matchEmpty_le M C w pre suf

/-- Main (Section 3), timed. `buildPre` and `buildSuf` build the arrays `Pre` and `Suf`,
`buildPreα α` builds `Pre_α` (for `α = []`, whose entry at `0` tells whether `e` matches `ε`), and
`enum` lists the right-maximal repeats with their occurrence arrays. -/
def main (w : List Symbol) (buildPre buildSuf : TimeM ℕ (ℕ → Bool))
    (buildPreα : List Symbol → TimeM ℕ (ℕ → Bool))
    (enum : TimeM ℕ (List (List Symbol × List ℕ))) : TimeM ℕ Bool := do
  let pre ← buildPre
  let suf ← buildSuf
  let preε ← buildPreα []
  let empty ← matchEmptyIf M C (preε 0) w pre suf
  if empty then
    pure true
  else
    let reps ← enum
    reps.anyM fun r => do
      let preα ← buildPreα r.1
      matchRepeat M C w r.1 r.2 pre suf preα

variable [DecidableEq Symbol]

/-- The timed Main computes `Rewb.main` when `enum` lists the right-maximal repeats of `w`, each
with its occurrences, in any order. -/
theorem ret_main (w : List Symbol) (buildPre buildSuf : TimeM ℕ (ℕ → Bool))
    (buildPreα : List Symbol → TimeM ℕ (ℕ → Bool))
    (enum : TimeM ℕ (List (List Symbol × List ℕ)))
    (henum : ⟪enum⟫.Perm (w.rightMaximalRepeats.map fun α => (α, α.occurrences w))) :
    ⟪main M C w buildPre buildSuf buildPreα enum⟫ =
      Rewb.main M w ⟪buildPre⟫ ⟪buildSuf⟫ fun α => ⟪buildPreα α⟫ := by
  -- The repeats can come in any order, and each has its occurrences.
  have hrep : (⟪enum⟫.any fun r =>
      ⟪matchRepeat M C w r.1 r.2 ⟪buildPre⟫ ⟪buildSuf⟫ ⟪buildPreα r.1⟫⟫) =
      w.rightMaximalRepeats.any fun α =>
        Rewb.matchRepeat M w α (α.occurrences w) ⟪buildPre⟫ ⟪buildSuf⟫ ⟪buildPreα α⟫ := by
    rw [henum.any_eq, List.any_map, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    refine exists_congr fun α => and_congr_right fun hα => ?_
    have hne := (List.mem_rightMaximalRepeats.mp hα).1
    simp only [Function.comp_apply]
    rw [ret_matchRepeat M C (List.length_pos_iff.mpr hne) (List.pairwise_lt_occurrences α w)]
  simp only [main, Rewb.main, TimeM.ret_bind, ret_matchEmptyIf, ret_ite_pure_true, ret_anyM, hrep]

/-- Theorem 5, the time bound: when each `Pre_α` costs at most `(|α| + 1) · cₑ` (the paper's
`O(|α| · m_e)` by simulation) and `enum` lists the right-maximal repeats of `w` with their
occurrences, Main takes the time of building `Pre` and `Suf` and of the enumeration, plus
`cₑ + (2n + 1) · C.step`, plus, for each of at most `n - 1` right-maximal repeats,
`(n + 1) · cₑ + n · (7 + 2 · C.sumStep + 4 · C.step)`. With `C.step = O(m_e₁)`,
`C.sumStep = O(m²_e₁)` and `cₑ = O(m_e)` this is the paper's
`O(n² + n(m_e₀ + m_e₂) + µ_right · n(m_e + m²_e₁))`, and so `O(n²m²)`. -/
theorem time_main_le (w : List Symbol) (buildPre buildSuf : TimeM ℕ (ℕ → Bool))
    (buildPreα : List Symbol → TimeM ℕ (ℕ → Bool))
    (enum : TimeM ℕ (List (List Symbol × List ℕ))) {cₑ : ℕ}
    (henum : ⟪enum⟫.Perm (w.rightMaximalRepeats.map fun α => (α, α.occurrences w)))
    (hpreα : ∀ α, (buildPreα α).time ≤ (α.length + 1) * cₑ) :
    (main M C w buildPre buildSuf buildPreα enum).time ≤
      buildPre.time + buildSuf.time + enum.time + cₑ + (2 * w.length + 1) * C.step +
        (w.length - 1) *
          ((w.length + 1) * cₑ + w.length * (7 + 2 * C.sumStep + 4 * C.step)) := by
  -- Each right-maximal repeat costs at most `(n + 1) · cₑ + n · (7 + 2 · C.sumStep + 4 · C.step)`.
  have hrep : ∀ α ∈ w.rightMaximalRepeats, (buildPreα α).time +
      (matchRepeat M C w α (α.occurrences w) ⟪buildPre⟫ ⟪buildSuf⟫ ⟪buildPreα α⟫).time ≤
      (w.length + 1) * cₑ + w.length * (7 + 2 * C.sumStep + 4 * C.step) := by
    intro α hα
    obtain ⟨hne, i, -, hi, -, -⟩ := List.mem_rightMaximalRepeats.mp hα
    have hlen := hi.add_length_le hne
    have h₁ := (hpreα α).trans (Nat.mul_le_mul_right cₑ (by omega : α.length + 1 ≤ w.length + 1))
    have h₂ := time_matchRepeat_le M C (pre := ⟪buildPre⟫) (suf := ⟪buildSuf⟫)
      (preα := ⟪buildPreα α⟫) (rfl : α.occurrences w = α.occurrences w) hne
    have h₃ := Nat.mul_le_mul_right (7 + C.sumStep + 2 * C.step)
      (List.length_occurrences_le (w := w) hne)
    have e : w.length * (7 + 2 * C.sumStep + 4 * C.step) =
        w.length * (7 + C.sumStep + 2 * C.step) + w.length * (C.sumStep + 2 * C.step) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  -- There are at most `n - 1` of them.
  have hsum : (⟪enum⟫.map fun r => (buildPreα r.1).time +
      (matchRepeat M C w r.1 r.2 ⟪buildPre⟫ ⟪buildSuf⟫ ⟪buildPreα r.1⟫).time).sum ≤
      (w.length - 1) *
        ((w.length + 1) * cₑ + w.length * (7 + 2 * C.sumStep + 4 * C.step)) := by
    rw [(henum.map _).sum_nat, List.map_map]
    refine (sum_le_length_mul (K := (w.length + 1) * cₑ +
      w.length * (7 + 2 * C.sumStep + 4 * C.step)) fun x hx => ?_).trans ?_
    · obtain ⟨α, hα, rfl⟩ := List.mem_map.mp hx
      exact hrep α hα
    · rw [List.length_map]
      exact Nat.mul_le_mul_right _ (List.length_rightMaximalRepeats_le w)
  have hany := time_anyM_le (fun r => do
    let preα ← buildPreα r.1
    matchRepeat M C w r.1 r.2 ⟪buildPre⟫ ⟪buildSuf⟫ preα) ⟪enum⟫
  simp only [TimeM.time_bind] at hany
  have hempty := time_matchEmptyIf_le M C (⟪buildPreα []⟫ 0) w ⟪buildPre⟫ ⟪buildSuf⟫
  have hε := hpreα []
  simp only [List.length_nil, Nat.zero_add, Nat.one_mul] at hε
  simp only [main, TimeM.time_bind]
  -- The check of `e₀ e₁ e₂` either ends Main or lets it go on.
  split
  · simp only [TimeM.time_pure]; omega
  · simp only [TimeM.time_bind]; omega

end Rewb.Timed
