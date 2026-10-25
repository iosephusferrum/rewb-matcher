/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Rewb.Match3A

/-!
# The cost of simulation

The time bounds of the paper count the steps of its simulations (Section 2, after Definition 3,
and the analyses of Match1, Match2, Match3A and Match3B in Section 3). This file fixes the cost
model and gives timed versions of the simulations in cslib's `TimeM ℕ`: each computes its untimed
counterpart (`ret_*`) at a stated cost (`time_*`).

## Cost model

`TimeM` annotations are trusted, so the model is stated here, and the timed algorithms charge
exactly this.

* `C.step` for reading one symbol in a simulation, including the injection after it and the
  lookups in `Pre`, `Suf` and `Pre_α` that decide it, and for one acceptance test `S ∩ F ≠ ∅`. For
  the automaton of `e₁` with a breadth-first ε-closure this is the paper's `O(m_e₁)`.
* `C.sumStep` for reading one symbol in a simulation with summarization, and for testing a summary
  against the set `T` of Intmed (Algorithm 2, line 9): the paper's `O(m²_e₁)` (Section 3.1.2).
* `1` for each occurrence of the repeat that a loop over `Idx_α` visits, for its bookkeeping.

Everything else (arithmetic, comparisons, pattern matching) is free.

## Main definitions

* `Rewb.Timed.Cost`: the costs `C.step` and `C.sumStep`.
* `Rewb.Timed.evalInject`, `Rewb.Timed.evalQue` and `Rewb.Timed.intmed`: simulation with
  injection, lines 6 to 10 of Algorithm 4, and Algorithm 3.

## Main statements

* `ret_evalInject`, `ret_evalQue` and `ret_intmed`: they compute `Simulator.evalInject`,
  `Rewb.evalQue` and `Rewb.intmed`.
* `time_evalInject`, `time_evalQue` and `time_intmed`: one step per symbol read, and one more for
  the injection that starts Intmed.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb.Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

/-- The costs of the operations that the time bounds count (see the cost model above). -/
structure Cost where
  /-- Reading one symbol in a simulation, with the injection after it, or one acceptance test. -/
  step : ℕ
  /-- Reading one symbol in a simulation with summarization, or testing a summary against a set
  of states. -/
  sumStep : ℕ

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol) (C : Cost)

/-- Simulation with injection (`Simulator.evalInject`), at `C.step` per symbol read. -/
def evalInject (I : Finset State) (mark : ℕ → Bool) :
    Finset State → ℕ → List Symbol → TimeM ℕ (Finset State)
  | S, _, [] => pure S
  | S, i, a :: u => do
    ✓[C.step] evalInject I mark (if mark i then M.stepSet S a ∪ I else M.stepSet S a) (i + 1) u

/-- Lines 6 to 10 of Algorithm 4 (`Rewb.evalQue`), at `C.sumStep` per symbol read. -/
def evalQue :
    (State → Finset State) → List ℕ → ℕ → List Symbol →
      TimeM ℕ ((State → Finset State) × List ℕ)
  | S, que, _, [] => pure (S, que)
  | S, que, p, a :: u => do
    TimeM.tick C.sumStep
    let S := fun t => M.stepSet (S t) a
    if que.head? = some (p + 1) then evalQue (fun t => S t ∪ {t}) que.tail (p + 1) u
    else evalQue S que (p + 1) u

/-- Algorithm 3 (`Rewb.intmed`): `C.step` for the injection before the first symbol, then `C.step`
per symbol read. -/
def intmed (α : List Symbol) (p kbeg : ℕ) (preα suf : ℕ → Bool) : TimeM ℕ (Finset State) := do
  ✓[C.step] evalInject M C M.start (fun k => preα (k + 1) && suf (p + (k + 1)))
    (if preα kbeg && suf (p + kbeg) then M.start else ∅) kbeg (α.drop kbeg)

@[simp]
theorem ret_evalInject (I : Finset State) (mark : ℕ → Bool) (S : Finset State) (i : ℕ)
    (u : List Symbol) : ⟪evalInject M C I mark S i u⟫ = M.evalInject I mark S i u := by
  induction u generalizing S i with
  | nil => rfl
  | cons a u ih => simp [evalInject, ih]

@[simp]
theorem time_evalInject (I : Finset State) (mark : ℕ → Bool) (S : Finset State) (i : ℕ)
    (u : List Symbol) : (evalInject M C I mark S i u).time = u.length * C.step := by
  induction u generalizing S i with
  | nil => simp [evalInject]
  | cons a u ih =>
    simp only [evalInject, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

@[simp]
theorem ret_evalQue (S : State → Finset State) (que : List ℕ) (i : ℕ) (u : List Symbol) :
    ⟪evalQue M C S que i u⟫ = Rewb.evalQue M S que i u := by
  induction u generalizing S que i with
  | nil => rfl
  | cons a u ih =>
    simp only [evalQue, Rewb.evalQue, TimeM.ret_bind]
    split_ifs <;> exact ih _ _ _

@[simp]
theorem time_evalQue (S : State → Finset State) (que : List ℕ) (i : ℕ) (u : List Symbol) :
    (evalQue M C S que i u).time = u.length * C.sumStep := by
  induction u generalizing S que i with
  | nil => simp [evalQue]
  | cons a u ih =>
    simp only [evalQue, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    split_ifs <;> rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

@[simp]
theorem ret_intmed (α : List Symbol) (p kbeg : ℕ) (preα suf : ℕ → Bool) :
    ⟪intmed M C α p kbeg preα suf⟫ = Rewb.intmed M α p kbeg preα suf := by
  simp [intmed, Rewb.intmed]

@[simp]
theorem time_intmed (α : List Symbol) (p kbeg : ℕ) (preα suf : ℕ → Bool) :
    (intmed M C α p kbeg preα suf).time = (α.length - kbeg + 1) * C.step := by
  simp only [intmed, TimeM.time_bind, TimeM.time_tick, time_evalInject, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end Rewb.Timed
