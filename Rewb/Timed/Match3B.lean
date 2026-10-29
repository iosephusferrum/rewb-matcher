/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Timed.Fwd
public import Rewb.Timed.Simulation

/-!
# The cost of Match3B

Match3B (Algorithm 5) checks its matches in `O(n·m_e₁)` time (Section 3.2): `Fwd` takes `O(n)`
(lines 1 to 6), and for each pair `(inext, fnext)` that passes the guard of line 9, Intmed's loop
reads the positions from `max{inext, fprev} + 1` up to `fnext` (lines 10 to 14). Since `f` is
monotone and `fprev` becomes `fnext` after every pair (line 16), these stretches do not overlap,
and Intmed reads every position of `w` at most once. In the cost model of
`Rewb.Timed.Simulation`, this file bounds the time of Match3B by
`|Idx_α| · (5 + C.step) + |w| · C.step`.

## Main definitions

* `Rewb.Timed.match3BCheck`: lines 9 to 15 of Algorithm 5 for one pair.
* `Rewb.Timed.match3B`: Algorithm 5, timed.

## Main statements

* `Rewb.fwd_le_fwd`: `f` is monotone.
* `Rewb.Timed.ret_match3B`: the timed Match3B computes `Rewb.match3B`.
* `Rewb.Timed.time_match3B_le`: its time bound, `|Idx_α| · (5 + C.step) + |w| · C.step`.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- `f` is monotone (Definition 20): an occurrence that starts inside the occurrence at `i` starts
before `j + n` for every `j ≥ i`. -/
theorem fwd_le_fwd {n : ℕ} {idx : List ℕ} {i j : ℕ} (hn : 0 < n) (hi : i ∈ idx) (hij : i ≤ j) :
    fwd n idx i ≤ fwd n idx j :=
  le_fwd_of_mem (fwd_mem hi) (by have := fwd_lt (idx := idx) (i := i) hn; omega)

namespace Timed

open Cslib.Algorithms.Lean
open scoped Cslib.Algorithms.Lean.TimeM

/-- Zipping a list with its image under `f` pairs each entry with its image. -/
private theorem zip_map_right_self (l : List ℕ) (f : ℕ → ℕ) :
    l.zip (l.map f) = l.map fun i => (i, f i) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

-- The states live in `Type`, as in `Rewb.Timed.Match3A`.
variable {State : Type} {Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)
  (C : Cost)

/-- Lines 9 to 15 of Algorithm 5 for the pair `(inext, fnext)`: if the guard of line 9 holds,
Intmed's loop (lines 10 to 14, as `Rewb.intmed` on `α.take (fnext - inext)`) and the test of
line 15. -/
def match3BCheck (α : List Symbol) (pre preα suf : ℕ → Bool) (fprev inext fnext : ℕ) :
    TimeM ℕ Bool :=
  if inext < fnext ∧ pre inext = true ∧ fprev < fnext then do
    let S ← intmed M C (α.take (fnext - inext)) fnext (max 1 (fprev + 1 - inext)) preα suf
    ✓[C.step] pure (decide (∃ s ∈ S, s ∈ M.accept))
  else pure false

/-- The loop of Algorithm 5 (lines 8 to 16), timed: `1` per pair, and the check of the pair. -/
def match3BLoop (α : List Symbol) (pre suf preα : ℕ → Bool) : ℕ → List (ℕ × ℕ) → TimeM ℕ Bool
  | _, [] => pure false
  | fprev, (inext, fnext) :: occ => do
    TimeM.tick 1
    let found ← match3BCheck M C α pre preα suf fprev inext fnext
    if found then
      pure true
    else
      match3BLoop α pre suf preα fnext occ

/-- Algorithm 5 (`Rewb.match3B`), timed: `Fwd` (lines 1 to 6), then the loop over
`zip(Idx_α, Fwd)` (line 8). -/
def match3B (α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : TimeM ℕ Bool := do
  let fwds ← fwdList α.length idx
  match3BLoop M C α pre suf preα 0 (idx.zip fwds)

@[simp]
theorem ret_match3BCheck (α : List Symbol) (pre preα suf : ℕ → Bool) (fprev inext fnext : ℕ) :
    ⟪match3BCheck M C α pre preα suf fprev inext fnext⟫ =
      (decide (inext < fnext) && pre inext && decide (fprev < fnext) &&
        (let S := Rewb.intmed M (α.take (fnext - inext)) fnext (max 1 (fprev + 1 - inext)) preα suf
         decide (∃ s ∈ S, s ∈ M.accept))) := by
  unfold match3BCheck
  by_cases h₁ : inext < fnext <;> by_cases h₂ : pre inext = true <;>
    by_cases h₃ : fprev < fnext <;> simp [h₁, h₂, h₃]

@[simp]
theorem ret_match3BLoop (α : List Symbol) (pre suf preα : ℕ → Bool) (fprev : ℕ)
    (occ : List (ℕ × ℕ)) :
    ⟪match3BLoop M C α pre suf preα fprev occ⟫ = Rewb.match3BLoop M α pre suf preα fprev occ := by
  induction occ generalizing fprev with
  | nil => rfl
  | cons x occ ih =>
    obtain ⟨inext, fnext⟩ := x
    simp only [match3BLoop, Rewb.match3BLoop, TimeM.ret_bind, ret_match3BCheck]
    split <;> simp_all

theorem ret_match3B {α : List Symbol} {idx : List ℕ} (hα : 0 < α.length)
    (hsorted : idx.Pairwise (· < ·)) (pre suf preα : ℕ → Bool) :
    ⟪match3B M C α idx pre suf preα⟫ = Rewb.match3B M α idx pre suf preα := by
  simp only [match3B, Rewb.match3B, TimeM.ret_bind, ret_fwdList hα hsorted, zip_map_right_self,
    ret_match3BLoop]

/-- The check of one pair costs at most `C.step` for the test and `C.step` per position of Intmed,
which reads from `max{inext, fprev} + 1` up to `fnext` after one step for its first injection. -/
theorem time_match3BCheck_le (α : List Symbol) (pre preα suf : ℕ → Bool)
    (fprev inext fnext : ℕ) :
    (match3BCheck M C α pre preα suf fprev inext fnext).time ≤
      C.step + (fnext - fprev) * C.step := by
  unfold match3BCheck
  split_ifs with h
  · simp only [TimeM.time_bind, time_intmed, TimeM.time_tick, TimeM.time_pure, List.length_take]
    have h₁ : min (fnext - inext) α.length - max 1 (fprev + 1 - inext) + 1 ≤ fnext - fprev := by
      omega
    have := Nat.mul_le_mul_right C.step h₁
    omega
  · simp

/-- The time of the loop of Algorithm 5: `1 + C.step` per pair, and `C.step` per position that
Intmed reads, which add up to at most `N - fprev` when the second entries of the pairs increase
from `fprev` and stay below `N`. -/
theorem time_match3BLoop_le (α : List Symbol) (pre suf preα : ℕ → Bool) (N : ℕ) :
    ∀ {fprev : ℕ} {occ : List (ℕ × ℕ)}, (occ.map Prod.snd).Pairwise (· ≤ ·) →
      (∀ p ∈ occ, fprev ≤ p.2) → (∀ p ∈ occ, p.2 ≤ N) →
      (match3BLoop M C α pre suf preα fprev occ).time ≤
        occ.length * (1 + C.step) + (N - fprev) * C.step := by
  intro fprev occ
  induction occ generalizing fprev with
  | nil => intros; simp [match3BLoop]
  | cons x occ ih =>
    obtain ⟨inext, fnext⟩ := x
    intro hsorted hge hle
    simp only [List.map_cons, List.pairwise_cons] at hsorted
    have hf : fprev ≤ fnext := hge (inext, fnext) List.mem_cons_self
    have hN : fnext ≤ N := hle (inext, fnext) List.mem_cons_self
    have hcheck := time_match3BCheck_le M C α pre preα suf fprev inext fnext
    have hrest := ih (fprev := fnext) hsorted.2 (fun p hp => hsorted.1 p.2 (List.mem_map_of_mem hp))
      (fun p hp => hle p (List.mem_cons_of_mem _ hp))
    -- The stretches of consecutive pairs telescope.
    have e₁ : (fnext - fprev) * C.step + (N - fnext) * C.step = (N - fprev) * C.step := by
      rw [← Nat.add_mul]; congr 1; omega
    have e₂ : (occ.length + 1) * (1 + C.step) = occ.length * (1 + C.step) + (1 + C.step) := by
      rw [Nat.add_mul, Nat.one_mul]
    simp only [match3BLoop, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    -- The test of line 15 either ends the loop or lets it go on.
    split
    · simp only [TimeM.time_pure]; omega
    · omega

/-- Match3B takes `O(n·m_e₁)` time (Section 3.2), up to `Pre_α`: at most
`|Idx_α| · (5 + C.step) + |w| · C.step`. -/
theorem time_match3B_le [DecidableEq Symbol] {w α : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hidx : idx = α.occurrences w) (hα : α ≠ []) :
    (match3B M C α idx pre suf preα).time ≤ idx.length * (5 + C.step) + w.length * C.step := by
  have hα' := List.length_pos_iff.mpr hα
  have hsorted : idx.Pairwise (· < ·) := by rw [hidx]; exact List.pairwise_lt_occurrences α w
  have hocc : ∀ p ∈ idx, α.OccursAt w p := fun p hp =>
    (List.mem_occurrences_of_ne_nil hα).mp (by rw [← hidx]; exact hp)
  -- `f` is monotone along `Idx_α` and stays within `w`.
  have h₁ : ((idx.map fun i => (i, fwd α.length idx i)).map Prod.snd).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr (List.pairwise_map.mpr
      (hsorted.imp_of_mem fun hi _ hlt => fwd_le_fwd hα' hi hlt.le))
  have h₃ : ∀ p ∈ idx.map (fun i => (i, fwd α.length idx i)), p.2 ≤ w.length := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have := (hocc _ (fwd_mem (n := α.length) hi)).add_length_le hα
    simp only
    omega
  have hloop := time_match3BLoop_le M C α pre suf preα w.length (fprev := 0) h₁
    (fun _ _ => Nat.zero_le _) h₃
  rw [Nat.sub_zero, List.length_map] at hloop
  have hfwd := time_fwdList_le α.length idx
  have e : idx.length * (5 + C.step) = 4 * idx.length + idx.length * (1 + C.step) := by
    rw [show 5 + C.step = 4 + (1 + C.step) by omega, Nat.mul_add]
    omega
  simp only [match3B, TimeM.time_bind, ret_fwdList hα' hsorted, zip_map_right_self]
  omega

end Rewb.Timed
