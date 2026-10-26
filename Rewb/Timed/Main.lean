/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Main
public import Rewb.Timed.Match3A
public import Rewb.Timed.Match3B

/-!
# The cost of Main

The parts of Main (Section 3), in the cost model of `Rewb.Timed.Simulation`.

When `e` matches `ε`, Main checks whether `e₀ e₁ e₂` matches `w` in `O(nm)` time "by ordinary NFA
simulation" (Section 3, before Lemma 6). `Rewb.matchEmpty` states this check as one simulation for
each end position; the timed `matchEmpty` makes the single pass: one simulation of `e₁` along `w`,
injecting `cl_ε(q₀)` after the positions with `Pre`, tested at every position with `Suf`.
`Match(α)` is Match3A, then Match3B if Match3A returns false.

## Main definitions

* `Rewb.Timed.matchEmpty`: the check of `e₀ e₁ e₂` in one pass.
* `Rewb.Timed.matchRepeat`: `Match(α)`.

## Main statements

* `Rewb.Timed.ret_matchEmpty` and `Rewb.Timed.time_matchEmpty_le`: the single pass computes
  `Rewb.matchEmpty`, at `C.step` per position and per test.
* `Rewb.Timed.ret_matchRepeat` and `Rewb.Timed.time_matchRepeat_le`: `Match(α)` computes
  `Rewb.matchRepeat`, in the time of Match3A and Match3B together.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb.Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

-- The states live in `Type`, as in `Rewb.Timed.Match3A`.
variable {State : Type} {Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)
  (C : Cost)

/-- The single pass of `matchEmpty` from position `j` on, with simulation set `S` there: test
`Suf` and acceptance at `j` (`C.step`), then read the next symbol and inject `cl_ε(q₀)` if `Pre`
holds after it (`C.step`). -/
def matchEmptyLoop (pre suf : ℕ → Bool) : Finset State → ℕ → List Symbol → TimeM ℕ Bool
  | S, j, [] => do
    ✓[C.step] pure (suf j && decide (∃ s ∈ S, s ∈ M.accept))
  | S, j, a :: u => do
    TimeM.tick C.step
    if suf j && decide (∃ s ∈ S, s ∈ M.accept) then
      pure true
    else
      TimeM.tick C.step
      matchEmptyLoop pre suf (if pre (j + 1) then M.stepSet S a ∪ M.start else M.stepSet S a)
        (j + 1) u

/-- The check of `e₀ e₁ e₂` (`Rewb.matchEmpty`) in one pass over `w`. -/
def matchEmpty (w : List Symbol) (pre suf : ℕ → Bool) : TimeM ℕ Bool :=
  matchEmptyLoop M C pre suf (if pre 0 then M.start else ∅) 0 w

/-- `Match(α)` (`Rewb.matchRepeat`): Match3A, then Match3B if Match3A returns false. -/
def matchRepeat (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) :
    TimeM ℕ Bool := do
  let found ← match3A M C w α idx pre suf preα
  if found then pure true else match3B M C α idx pre suf preα

/-- The single pass from `j` succeeds exactly when, for some `k`, `Suf` holds at `j + k` and the
simulation from `S` with injection accepts after reading `k` more symbols. -/
theorem ret_matchEmptyLoop_eq_true_iff (pre suf : ℕ → Bool) (S : Finset State) (j : ℕ)
    (u : List Symbol) :
    ⟪matchEmptyLoop M C pre suf S j u⟫ = true ↔
      ∃ k < u.length + 1, suf (j + k) = true ∧
        ∃ s ∈ M.evalInject M.start (fun p => pre (p + 1)) S j (u.take k), s ∈ M.accept := by
  induction u generalizing S j with
  | nil => simp [matchEmptyLoop, Nat.lt_one_iff]
  | cons a u ih =>
    -- Testing later than `j` is the pass from `j + 1`, after reading `a`.
    have hlater : (∃ m < u.length + 1, suf (j + (m + 1)) = true ∧
        ∃ s ∈ M.evalInject M.start (fun p => pre (p + 1)) S j ((a :: u).take (m + 1)),
          s ∈ M.accept) ↔
        ⟪matchEmptyLoop M C pre suf (if pre (j + 1) then M.stepSet S a ∪ M.start
          else M.stepSet S a) (j + 1) u⟫ = true := by
      rw [ih]
      refine exists_congr fun m => and_congr_right fun _ => ?_
      simp only [show j + (m + 1) = j + 1 + m by omega, List.take_succ_cons,
        Simulator.evalInject_cons]
    rw [List.length_cons, Nat.exists_lt_succ_left, hlater]
    simp only [Nat.add_zero, List.take_zero, Simulator.evalInject_nil, matchEmptyLoop,
      TimeM.ret_bind]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [TimeM.ret_pure, true_iff]
      exact .inl h
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h
      constructor
      · exact .inr
      · rintro (⟨h₁, h₂⟩ | h₃)
        · exact absurd h₂ (h h₁)
        · exact h₃

@[simp]
theorem ret_matchEmpty (w : List Symbol) (pre suf : ℕ → Bool) :
    ⟪matchEmpty M C w pre suf⟫ = Rewb.matchEmpty M w pre suf := by
  rw [Bool.eq_iff_iff, matchEmpty, ret_matchEmptyLoop_eq_true_iff, Rewb.matchEmpty,
    List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, Nat.zero_add]

theorem time_matchEmptyLoop_le (pre suf : ℕ → Bool) (S : Finset State) (j : ℕ)
    (u : List Symbol) : (matchEmptyLoop M C pre suf S j u).time ≤ (2 * u.length + 1) * C.step := by
  induction u generalizing S j with
  | nil => simp [matchEmptyLoop]
  | cons a u ih =>
    have := ih (if pre (j + 1) then M.stepSet S a ∪ M.start else M.stepSet S a) (j + 1)
    have e : (2 * (u.length + 1) + 1) * C.step = (2 * u.length + 1) * C.step + C.step + C.step := by
      rw [show 2 * (u.length + 1) + 1 = 2 * u.length + 1 + 1 + 1 by omega, Nat.add_mul,
        Nat.add_mul, Nat.one_mul]
    simp only [matchEmptyLoop, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    -- The test at `j` either ends the pass or lets it go on.
    split
    · simp only [TimeM.time_pure]; omega
    · simp only [TimeM.time_bind, TimeM.time_tick]; omega

/-- The check of `e₀ e₁ e₂` takes `O(n·m_e₁)` time: at most `(2|w| + 1) · C.step`. -/
theorem time_matchEmpty_le (w : List Symbol) (pre suf : ℕ → Bool) :
    (matchEmpty M C w pre suf).time ≤ (2 * w.length + 1) * C.step :=
  time_matchEmptyLoop_le M C pre suf _ 0 w

theorem ret_matchRepeat {w α : List Symbol} {idx : List ℕ} (hα : 0 < α.length)
    (hsorted : idx.Pairwise (· < ·)) (pre suf preα : ℕ → Bool) :
    ⟪matchRepeat M C w α idx pre suf preα⟫ = Rewb.matchRepeat M w α idx pre suf preα := by
  simp only [matchRepeat, Rewb.matchRepeat, TimeM.ret_bind, ret_match3A]
  split <;> simp_all [ret_match3B M C hα hsorted]

/-- `Match(α)` takes `O(n(m_e + m²_e₁))` time (Section 3), up to `Pre_α`: at most the times of
Match3A and Match3B together. -/
theorem time_matchRepeat_le [DecidableEq Symbol] {w α : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hidx : idx = α.occurrences w) (hα : α ≠ []) :
    (matchRepeat M C w α idx pre suf preα).time ≤
      idx.length * (7 + C.sumStep + 2 * C.step) + w.length * (C.sumStep + 2 * C.step) := by
  have h3A := time_match3A_le M C (pre := pre) (suf := suf) (preα := preα) hidx hα
  have h3B := time_match3B_le M C (pre := pre) (suf := suf) (preα := preα) hidx hα
  have e₁ : idx.length * (7 + C.sumStep + 2 * C.step) =
      idx.length * (2 + C.sumStep + C.step) + idx.length * (5 + C.step) := by
    rw [← Nat.mul_add]; congr 1; omega
  have e₂ : w.length * (C.sumStep + 2 * C.step) =
      w.length * (C.sumStep + C.step) + w.length * C.step := by
    rw [← Nat.mul_add]; congr 1; omega
  simp only [matchRepeat, TimeM.time_bind]
  -- Match3B runs only if Match3A returns false.
  split
  · simp only [TimeM.time_pure]; omega
  · omega

end Rewb.Timed
