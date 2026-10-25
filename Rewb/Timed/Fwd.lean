/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Rewb.Match3B

/-!
# The array `Fwd`

Algorithm 5 computes `f(i)` (Definition 20) for every occurrence `i` of `α` in `O(n)` time with
two pointers (lines 1 to 6): `j₁` runs through the occurrences from the right, and `j₂` steps left
past the occurrences that start too far to the right, then gives `f(i)`. Neither pointer ever
moves back. Here the occurrences are a list in decreasing order and `j₂` is the list of the
candidates still ahead of it. This file proves that the scan computes `fwd` (`Rewb.Match3B`) at
cost `O(|Idx_α|)`, `1` per step of either pointer, in the cost model of `Rewb.Timed.Simulation`.

## Main definitions

* `Rewb.Timed.fwdScan`: lines 1 to 6 of Algorithm 5, on the occurrences in decreasing order.
* `Rewb.Timed.fwdList`: the array `Fwd`.

## Main statements

* `Rewb.Timed.ret_fwdList`: `Fwd` lists `f(i)` for every occurrence `i`.
* `Rewb.Timed.time_fwdList_le`: at a cost of at most `4 · |Idx_α|`.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb.Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

/-- Lines 1 to 6 of Algorithm 5, on the occurrences `is` in decreasing order, with the candidates
`cand` for `j₂` in decreasing order: for each `i`, step `j₂` past the candidates that start at
`i + n` or later (line 6), then take the first one left (lines 4 and 5). `1` per step of either
pointer. -/
def fwdScan (n : ℕ) : List ℕ → List ℕ → TimeM ℕ (List ℕ)
  | [], _ => pure []
  | i :: is, cand => do
    let cand' := cand.dropWhile fun j => decide (i + n ≤ j)
    TimeM.tick (cand.length - cand'.length + 1)
    let fwds ← fwdScan n is cand'
    pure (cand'.headD i :: fwds)

/-- The array `Fwd` of Algorithm 5 (lines 1 to 6): `f(i)` for each occurrence `i` in `idx`, in
order. Reading `Idx_α` from the right and filling `Fwd` from the right cost `1` per entry each. -/
def fwdList (n : ℕ) (idx : List ℕ) : TimeM ℕ (List ℕ) := do
  TimeM.tick (2 * idx.length)
  let fwds ← fwdScan n idx.reverse idx.reverse
  pure fwds.reverse

theorem time_fwdScan_le (n : ℕ) (is cand : List ℕ) :
    (fwdScan n is cand).time ≤ is.length + cand.length := by
  induction is generalizing cand with
  | nil => simp [fwdScan]
  | cons i is ih =>
    have := ih (cand.dropWhile fun j => decide (i + n ≤ j))
    have := (List.dropWhile_suffix (fun j => decide (i + n ≤ j)) (l := cand)).length_le
    simp only [fwdScan, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    omega

theorem time_fwdList_le (n : ℕ) (idx : List ℕ) : (fwdList n idx).time ≤ 4 * idx.length := by
  have := time_fwdScan_le n idx.reverse idx.reverse
  simp only [List.length_reverse] at this
  simp only [fwdList, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
  omega

/-- In a decreasing list, stepping past the entries at or above `k` leaves those below `k`. -/
theorem mem_dropWhile_le_iff {k x : ℕ} {l : List ℕ} (hl : l.Pairwise (· > ·)) :
    x ∈ l.dropWhile (fun j => decide (k ≤ j)) ↔ x ∈ l ∧ x < k := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj : ∀ y ∈ l, y < j := fun y hy => List.rel_of_pairwise_cons hl hy
    rw [List.dropWhile_cons]
    by_cases hk : k ≤ j
    · simp only [hk, decide_true, ite_true, ih hl.of_cons, List.mem_cons]
      constructor
      · rintro ⟨hx, hxk⟩; exact ⟨.inr hx, hxk⟩
      · rintro ⟨rfl | hx, hxk⟩
        · omega
        · exact ⟨hx, hxk⟩
    · simp only [hk, decide_false, Bool.false_eq_true, ite_false, List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact ⟨.inl rfl, by omega⟩
        · exact ⟨.inr hx, by have := hj x hx; omega⟩
      · exact fun h => h.1

/-- The scan computes `f(i)` for each `i`, as long as the candidates are the occurrences in
decreasing order that `f` may still need: all those below `i + n` for every `i` still to come. -/
theorem ret_fwdScan {n : ℕ} (hn : 0 < n) {idx : List ℕ} :
    ∀ {is cand : List ℕ}, is.Pairwise (· > ·) → cand.Pairwise (· > ·) → (∀ i ∈ is, i ∈ idx) →
      (∀ j ∈ cand, j ∈ idx) → (∀ i ∈ is, ∀ j ∈ idx, j < i + n → j ∈ cand) →
      ⟪fwdScan n is cand⟫ = is.map (fwd n idx) := by
  intro is
  induction is with
  | nil => intros; rfl
  | cons i is ih =>
    intro cand his hcand hisidx hcandidx hneed
    have hi : i ∈ idx := hisidx i List.mem_cons_self
    have hmem : ∀ {x}, x ∈ cand.dropWhile (fun j => decide (i + n ≤ j)) ↔ x ∈ cand ∧ x < i + n :=
      mem_dropWhile_le_iff hcand
    have hcand' : (cand.dropWhile fun j => decide (i + n ≤ j)).Pairwise (· > ·) :=
      hcand.sublist (List.dropWhile_suffix _).sublist
    -- The first candidate left is `f(i)`: it is the largest occurrence below `i + n`.
    have hhead : (cand.dropWhile fun j => decide (i + n ≤ j)).headD i = fwd n idx i := by
      have hfwd : fwd n idx i ∈ cand.dropWhile (fun j => decide (i + n ≤ j)) :=
        hmem.mpr ⟨hneed i List.mem_cons_self _ (fwd_mem hi) (fwd_lt hn), fwd_lt hn⟩
      cases h : cand.dropWhile (fun j => decide (i + n ≤ j)) with
      | nil => rw [h] at hfwd; simp at hfwd
      | cons y l =>
        rw [h] at hfwd hcand'
        have hy := (hmem (x := y)).mp (by rw [h]; exact List.mem_cons_self)
        have h₁ : y ≤ fwd n idx i := le_fwd_of_mem (hcandidx y hy.1) hy.2
        have h₂ : fwd n idx i ≤ y := by
          rcases List.mem_cons.mp hfwd with h' | h'
          · exact h'.le
          · exact (List.rel_of_pairwise_cons hcand' h').le
        simp only [List.headD_cons]
        omega
    simp only [fwdScan, TimeM.ret_bind, TimeM.ret_pure, List.map_cons, hhead]
    congr 1
    refine ih his.of_cons hcand' (fun i' hi' => hisidx i' (List.mem_cons_of_mem _ hi'))
      (fun j hj => hcandidx j (hmem.mp hj).1) (fun i' hi' j hj hji => hmem.mpr ⟨?_, ?_⟩)
    · exact hneed i' (List.mem_cons_of_mem _ hi') j hj hji
    · have := List.rel_of_pairwise_cons his hi'
      omega

/-- `Fwd` lists `f(i)` for every occurrence `i` (Definition 20), in the order of `Idx_α`. -/
theorem ret_fwdList {n : ℕ} (hn : 0 < n) {idx : List ℕ} (hsorted : idx.Pairwise (· < ·)) :
    ⟪fwdList n idx⟫ = idx.map (fwd n idx) := by
  have hrev : idx.reverse.Pairwise (· > ·) := List.pairwise_reverse.mpr hsorted
  simp only [fwdList, TimeM.ret_bind, TimeM.ret_pure]
  rw [ret_fwdScan hn hrev hrev (fun i hi => List.mem_reverse.mp hi)
    (fun j hj => List.mem_reverse.mp hj) (fun _ _ j hj _ => List.mem_reverse.mpr hj),
    List.map_reverse, List.reverse_reverse]

end Rewb.Timed
