/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Timed.Simulation

/-!
# The cost of Match3A

Match3A (Algorithm 4) runs in `O(n(m_e + m²_e₁))` time (Section 3.2): the simulation with
summarization reads every position of `w` at most once, and so does Intmed, since it starts `d`
symbols into each occurrence of `α` and two consecutive occurrences overlap by at most `d`
(line 3). In the cost model of `Rewb.Timed.Simulation`, this file bounds the time of Match3A by
`|Idx_α| · (2 + C.sumStep + C.step) + |w| · (C.sumStep + C.step)`. Building `Pre_α` (line 2) is
left to the caller.

## Main definitions

* `Rewb.Timed.match3A`: Algorithm 4, timed.

## Main statements

* `Rewb.isChain_add_le_add_maxOverlap`: consecutive occurrences overlap by at most `d`.
* `Rewb.Timed.ret_match3A`: the timed Match3A computes `Rewb.match3A`.
* `Rewb.Timed.time_match3A_le`: its time bound.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- Two consecutive entries `p` and `p'` of `idx` overlap by at most every bound `d` on
`maxOverlap n idx`: `p + n ≤ p' + d` (Algorithm 4, line 3). -/
theorem isChain_add_le_add_maxOverlap {n d : ℕ} {idx : List ℕ} (h : maxOverlap n idx ≤ d) :
    idx.IsChain fun p p' => p + n ≤ p' + d := by
  induction idx with
  | nil => exact .nil
  | cons p idx ih =>
    cases idx with
    | nil => exact .singleton p
    | cons p' idx =>
      rw [maxOverlap, Nat.max_le] at h
      exact .cons_cons (by omega) (ih h.2)

namespace Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

-- The states live in `Type`, as those of the automata of regular expressions do: `TimeM ℕ` is a
-- monad on one universe, and the loop binds sets of states on its way to a `Bool`.
variable {State : Type} {Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)
  (C : Cost)

/-- The loop of Algorithm 4 (`Rewb.match3ALoop`), timed: `1` for each occurrence it visits and,
once an injection is pending, lines 6 to 10, Intmed (line 11) and the test of line 12. -/
def match3ALoop (w α : List Symbol) (pre suf preα : ℕ → Bool) (d : ℕ) :
    ℕ → (State → Finset State) → Option (List ℕ) → List ℕ → TimeM ℕ Bool
  | _, _, _, [] => pure false
  | _, S, none, inext :: idx => do
    TimeM.tick 1
    match3ALoop w α pre suf preα d inext S
      (if pre inext then some [inext + α.length] else none) idx
  | iprev, S, some que, inext :: idx => do
    TimeM.tick (1 + C.sumStep)
    let (S, que) ← evalQue M C S que iprev ((w.drop iprev).take (inext - iprev))
    let T ← intmed M C α inext (d + 1) preα suf
    if ∃ t ∈ T, ∃ s ∈ S t, s ∈ M.accept then
      pure true
    else
      match3ALoop w α pre suf preα d inext S
        (some (if pre inext then que ++ [inext + α.length] else que)) idx

/-- Algorithm 4 (`Rewb.match3A`), timed: line 3 costs `1` per occurrence, then the loop runs. -/
def match3A (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : TimeM ℕ Bool := do
  TimeM.tick idx.length
  match3ALoop M C w α pre suf preα (maxOverlap α.length idx) 0 (fun _ => ∅) none idx

@[simp]
theorem ret_match3ALoop (w α : List Symbol) (pre suf preα : ℕ → Bool) (d : ℕ) (iprev : ℕ)
    (S : State → Finset State) (que : Option (List ℕ)) (idx : List ℕ) :
    ⟪match3ALoop M C w α pre suf preα d iprev S que idx⟫ =
      Rewb.match3ALoop M w α pre suf preα d iprev S que idx := by
  induction idx generalizing iprev S que with
  | nil => rfl
  | cons inext idx ih =>
    cases que with
    | none => simp [match3ALoop, Rewb.match3ALoop, ih]
    | some que =>
      rcases hq : Rewb.evalQue M S que iprev ((w.drop iprev).take (inext - iprev)) with
        ⟨S', que'⟩
      simp only [match3ALoop, Rewb.match3ALoop, TimeM.ret_bind, ret_evalQue, ret_intmed, hq]
      split_ifs with h <;> simp [h, ih]

@[simp]
theorem ret_match3A (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) :
    ⟪match3A M C w α idx pre suf preα⟫ = Rewb.match3A M w α idx pre suf preα := by
  simp [match3A, Rewb.match3A]

/-- The time of the loop of Algorithm 4. Each visited occurrence costs `1 + C.sumStep + C.step`;
the simulation with summarization costs `C.sumStep` per position, and the segments it reads,
from one occurrence to the next, add up to at most `|w| - iprev`; Intmed costs `C.step` per
position after its first, and its segments, from `d + 1` symbols into each occurrence to its
end, are disjoint because consecutive occurrences overlap by at most `d`. -/
theorem time_match3ALoop_le (w α : List Symbol) (pre suf preα : ℕ → Bool) (d : ℕ) :
    ∀ {idx : List ℕ} {iprev : ℕ} {S : State → Finset State} {que : Option (List ℕ)},
      idx.Pairwise (· < ·) → (∀ p ∈ idx, iprev ≤ p) → (∀ p ∈ idx, p + α.length ≤ w.length) →
      (idx.IsChain fun p p' => p + α.length ≤ p' + d) →
      (match3ALoop M C w α pre suf preα d iprev S que idx).time ≤
        idx.length * (1 + C.sumStep + C.step) + (w.length - iprev) * C.sumStep +
          (w.length - idx.headD w.length) * C.step := by
  intro idx
  induction idx with
  | nil => intros; simp [match3ALoop]
  | cons inext idx ih =>
    intro iprev S que hsorted hge hlen hchain
    have hgt : ∀ p ∈ idx, inext < p := fun p hp => List.rel_of_pairwise_cons hsorted hp
    have hlen' : ∀ p ∈ idx, p + α.length ≤ w.length := fun p hp =>
      hlen p (List.mem_cons_of_mem _ hp)
    have hinext := hlen inext List.mem_cons_self
    have hiprev := hge inext List.mem_cons_self
    have hrest := fun {S : State → Finset State} {que : Option (List ℕ)} =>
      ih (iprev := inext) (S := S) (que := que) hsorted.of_cons (fun p hp => (hgt p hp).le)
        hlen' hchain.tail
    -- The rest of the list starts after `inext`, at a distance that pays for Intmed at `inext`.
    have hhead : inext ≤ idx.headD w.length := by
      cases idx with
      | nil => simp only [List.headD_nil]; omega
      | cons p' _ => exact (hgt p' List.mem_cons_self).le
    have hgap : α.length - (d + 1) + (w.length - idx.headD w.length) ≤ w.length - inext := by
      cases idx with
      | nil => simp only [List.headD_nil]; omega
      | cons p' _ =>
        have := (List.isChain_cons_cons.mp hchain).1
        have := hlen' p' List.mem_cons_self
        have := hgt p' List.mem_cons_self
        simp only [List.headD_cons]; omega
    have hK : (idx.length + 1) * (1 + C.sumStep + C.step) =
        idx.length * (1 + C.sumStep + C.step) + (1 + C.sumStep + C.step) := by
      rw [Nat.add_mul, Nat.one_mul]
    have hsum : (w.length - inext) * C.sumStep ≤ (w.length - iprev) * C.sumStep :=
      Nat.mul_le_mul_right _ (by omega)
    cases que with
    | none =>
      have hstep : (w.length - idx.headD w.length) * C.step ≤ (w.length - inext) * C.step :=
        Nat.mul_le_mul_right _ (by omega)
      have := hrest (S := S) (que := if pre inext then some [inext + α.length] else none)
      simp only [match3ALoop, TimeM.time_bind, TimeM.time_tick, List.length_cons,
        List.headD_cons]
      omega
    | some que =>
      rcases hq : (evalQue M C S que iprev ((w.drop iprev).take (inext - iprev))).ret with
        ⟨S', que'⟩
      have := hrest (S := S') (que := some (if pre inext then que' ++ [inext + α.length] else que'))
      have hseg : ((w.drop iprev).take (inext - iprev)).length * C.sumStep +
          (w.length - inext) * C.sumStep ≤ (w.length - iprev) * C.sumStep := by
        rw [← Nat.add_mul]
        exact Nat.mul_le_mul_right _ (by simp only [List.length_take, List.length_drop]; omega)
      have hint : (α.length - (d + 1) + 1) * C.step + (w.length - idx.headD w.length) * C.step ≤
          C.step + (w.length - inext) * C.step := by
        have := Nat.mul_le_mul_right C.step hgap
        rw [Nat.add_mul] at this
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simp only [match3ALoop, TimeM.time_bind, TimeM.time_tick, hq, time_evalQue, time_intmed,
        List.length_cons, List.headD_cons]
      -- The test of line 12 either ends the loop or lets it go on.
      split
      · simp only [TimeM.time_pure]; omega
      · omega

/-- Match3A takes `O(n(m_e + m²_e₁))` time (Section 3.2), up to `Pre_α`: at most
`|Idx_α| · (2 + C.sumStep + C.step) + |w| · (C.sumStep + C.step)`. -/
theorem time_match3A_le [DecidableEq Symbol] {w α : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hidx : idx = α.occurrences w) (hα : α ≠ []) :
    (match3A M C w α idx pre suf preα).time ≤
      idx.length * (2 + C.sumStep + C.step) + w.length * (C.sumStep + C.step) := by
  have hloop := time_match3ALoop_le M C w α pre suf preα (maxOverlap α.length idx)
    (idx := idx) (iprev := 0) (S := fun _ => ∅) (que := none)
    (by rw [hidx]; exact List.pairwise_lt_occurrences α w) (fun _ _ => Nat.zero_le _)
    (fun p hp =>
      ((List.mem_occurrences_of_ne_nil hα).mp (by rw [← hidx]; exact hp)).add_length_le hα)
    (isChain_add_le_add_maxOverlap le_rfl)
  rw [Nat.sub_zero] at hloop
  have hstep : (w.length - idx.headD w.length) * C.step ≤ w.length * C.step :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hK : idx.length * (2 + C.sumStep + C.step) =
      idx.length + idx.length * (1 + C.sumStep + C.step) := by
    rw [show 2 + C.sumStep + C.step = (1 + C.sumStep + C.step) + 1 by omega, Nat.mul_add,
      Nat.mul_one]
    omega
  have hn : w.length * (C.sumStep + C.step) = w.length * C.sumStep + w.length * C.step :=
    Nat.mul_add _ _ _
  simp only [match3A, TimeM.time_bind, TimeM.time_tick]
  omega

end Rewb.Timed
