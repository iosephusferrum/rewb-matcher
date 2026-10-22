/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Match2

/-!
# Match3A: right-maximal repeats whose occurrences may overlap

Algorithm 4 (`Match3A(α)`, Section 3.2) adapts Match2 to repeats whose occurrences may overlap.
This file defines its two new ingredients: the longest overlap `d` of two consecutive occurrences
(line 3), from which Intmed starts, and the simulation with summarization whose injections come
from a FIFO queue `Que` (lines 6 to 10), which may hold several pending injections at once.

## Main definitions

* `Rewb.maxOverlap`: `d` (Algorithm 4, line 3).
* `Rewb.evalQue`: Algorithm 4, lines 6 to 10.

## Main statements

* `Rewb.maxOverlap_lt`: `d` is below every bound on the overlaps.
* `Rewb.evalQue_fst` and `Rewb.evalQue_snd`: as long as `Que` is sorted and ahead of the
  position being read, the injections it drives are those at the positions it holds, and it keeps
  the positions not yet reached.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- Line 3 of Algorithm 4: `d`, the longest overlap `p + n - p'` of two consecutive occurrences
`p` and `p'` in `idx`, where `n = |α|`, and `0` if none overlap. -/
def maxOverlap (n : ℕ) : List ℕ → ℕ
  | p :: p' :: idx => max (p + n - p') (maxOverlap n (p' :: idx))
  | _ => 0

/-- `d` is below every bound `m > 0` on the overlaps of two occurrences in `idx`. -/
theorem maxOverlap_lt {n m : ℕ} {idx : List ℕ} (hm : 0 < m) (hsorted : idx.Pairwise (· < ·))
    (h : ∀ p ∈ idx, ∀ p' ∈ idx, p < p' → p + n - p' < m) : maxOverlap n idx < m := by
  induction idx with
  | nil => exact hm
  | cons p idx ih =>
    cases idx with
    | nil => exact hm
    | cons p' idx =>
      rw [maxOverlap, max_lt_iff]
      have hpp' : p < p' := List.rel_of_pairwise_cons hsorted (by simp)
      exact ⟨h p (by simp) p' (by simp) hpp',
        ih hsorted.of_cons fun q hq q' hq' hlt => h q (by simp [hq]) q' (by simp [hq']) hlt⟩

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Lines 6 to 10 of Algorithm 4: the simulation with summarization reads `u`, whose first symbol
is at position `i`, and right after reading a position `p` it injects (the paper's
`S[l] ← S[l] ∪ {q_l}`) and dequeues if the head of the queue `Que` is `p + 1`, the paper's number
for position `p`. It returns the simulation sets and what is left of `Que`. -/
def evalQue :
    (State → Finset State) → List ℕ → ℕ → List Symbol → (State → Finset State) × List ℕ
  | S, que, _, [] => (S, que)
  | S, que, p, a :: u =>
    let S := fun t => M.stepSet (S t) a
    if que.head? = some (p + 1) then evalQue (fun t => S t ∪ {t}) que.tail (p + 1) u
    else evalQue S que (p + 1) u

variable {M}

/-- In a sorted queue whose entries are past `i`, the entry `i + 1` can only be at the head. -/
private theorem head?_eq_some_iff_mem {que : List ℕ} {i : ℕ} (hsorted : que.Pairwise (· < ·))
    (hgt : ∀ q ∈ que, i < q) : que.head? = some (i + 1) ↔ i + 1 ∈ que := by
  cases que with
  | nil => simp
  | cons q que =>
    simp only [List.head?_cons, Option.some.injEq, List.mem_cons]
    constructor
    · intro h; exact .inl h.symm
    · rintro (h | h)
      · exact h.symm
      · have := List.rel_of_pairwise_cons hsorted h
        have := hgt q (by simp)
        omega

/-- The simulation sets after lines 6 to 10 of Algorithm 4: as long as `Que` is sorted and its
entries are past `i`, it injects exactly after the positions `p` with `p + 1` in `Que`. -/
theorem evalQue_fst {S : State → Finset State} {que : List ℕ} {i : ℕ} {u : List Symbol}
    (hsorted : que.Pairwise (· < ·)) (hgt : ∀ q ∈ que, i < q) :
    (evalQue M S que i u).1 = M.evalInjectSum (fun p => decide (p + 1 ∈ que)) S i u := by
  induction u generalizing S que i with
  | nil => rfl
  | cons a u ih =>
    rw [evalQue]
    split
    · rename_i hhead
      obtain ⟨que', rfl⟩ := List.head?_eq_some_iff.mp hhead
      rw [List.tail_cons, ih hsorted.of_cons fun q hq => List.rel_of_pairwise_cons hsorted hq]
      funext t
      simp only [Simulator.evalInjectSum, Simulator.evalInject_cons, List.mem_cons, true_or,
        decide_true, ite_true]
      refine Simulator.evalInject_congr fun k _ => ?_
      have hne : i + 1 + k + 1 ≠ i + 1 := by omega
      simp only [hne, false_or]
    · rename_i hhead
      have hnot : i + 1 ∉ que := fun h => hhead ((head?_eq_some_iff_mem hsorted hgt).mpr h)
      rw [ih hsorted fun q hq => by
        have := hgt q hq
        have : q ≠ i + 1 := fun h => hnot (h ▸ hq)
        omega]
      funext t
      simp only [Simulator.evalInjectSum, Simulator.evalInject_cons, hnot, decide_false,
        Bool.false_eq_true, ite_false]

/-- What is left of `Que` after lines 6 to 10 of Algorithm 4: as long as `Que` is sorted and its
entries are past `i`, the entries past the end `i + |u|` of `u`. -/
theorem evalQue_snd {S : State → Finset State} {que : List ℕ} {i : ℕ} {u : List Symbol}
    (hsorted : que.Pairwise (· < ·)) (hgt : ∀ q ∈ que, i < q) :
    (evalQue M S que i u).2 = que.filter (fun q => i + u.length < q) := by
  induction u generalizing S que i with
  | nil =>
    refine (List.filter_eq_self.mpr fun q hq => ?_).symm
    simpa using hgt q hq
  | cons a u ih =>
    rw [evalQue]
    split
    · rename_i hhead
      obtain ⟨que', rfl⟩ := List.head?_eq_some_iff.mp hhead
      rw [List.tail_cons, ih hsorted.of_cons fun q hq => List.rel_of_pairwise_cons hsorted hq,
        List.length_cons, show i + (u.length + 1) = i + 1 + u.length by omega, List.filter_cons,
        ite_eq_right (by simp)]
    · rename_i hhead
      have hnot : i + 1 ∉ que := fun h => hhead ((head?_eq_some_iff_mem hsorted hgt).mpr h)
      rw [ih hsorted fun q hq => by
          have := hgt q hq
          have : q ≠ i + 1 := fun h => hnot (h ▸ hq)
          omega,
        List.length_cons, show i + (u.length + 1) = i + 1 + u.length by omega]

end Rewb
