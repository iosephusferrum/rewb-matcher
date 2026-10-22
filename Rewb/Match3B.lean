/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Match2

/-!
# Match3B: matches inside overlapping occurrences of the repeat

Algorithm 5 (`Match3B(α)`, Section 3.2) finds the matches whose two occurrences of the
backreferenced word extend to occurrences of `α` that overlap. By Lemma 21 it only needs to pair
each occurrence `i` of `α` with the last occurrence `f(i)` that starts inside it (Definition 20).
This file defines `f` and proves Lemma 21.

## Main definitions

* `Rewb.fwd`: `f(i)` (Definition 20), the entries of the array `Fwd` of Algorithm 5.

## Main statements

* `Rewb.sub_lt_length_of_lt_fwd` and `Rewb.fwd_sub_lt_length`: Lemma 21.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- Definition 20: `f(i)`, the last occurrence in `idx` that starts inside the occurrence of `α` at
`i`, where `n = |α|`: the largest `j ∈ idx` with `j < i + n` (the paper's `j ≤ i + |α| − 1`). The
paper computes the array `Fwd` of these values with two pointers (Algorithm 5, lines 1 to 6); here
it is computed from the definition. -/
def fwd (n : ℕ) (idx : List ℕ) (i : ℕ) : ℕ :=
  (idx.filter fun j => j < i + n).foldr max i

/-- `l.foldr max a` is the largest of `a` and the entries of `l`. -/
private theorem foldr_max_spec (l : List ℕ) (a : ℕ) :
    a ≤ l.foldr max a ∧ (∀ j ∈ l, j ≤ l.foldr max a) ∧ (l.foldr max a = a ∨ l.foldr max a ∈ l) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨le_max_of_le_right h₁, ⟨le_max_left _ _, fun j hj => le_max_of_le_right (h₂ j hj)⟩, ?_⟩
    rcases le_total x (l.foldr max a) with h | h
    · rw [max_eq_right h]
      rcases h₃ with h₃ | h₃
      · exact .inl h₃
      · exact .inr (.inr h₃)
    · rw [max_eq_left h]
      exact .inr (.inl rfl)

/-- `f(i) ≥ i`. -/
theorem le_fwd (n : ℕ) (idx : List ℕ) (i : ℕ) : i ≤ fwd n idx i :=
  (foldr_max_spec _ i).1

/-- `f(i)` is an occurrence. -/
theorem fwd_mem {n : ℕ} {idx : List ℕ} {i : ℕ} (hi : i ∈ idx) : fwd n idx i ∈ idx := by
  rcases (foldr_max_spec (idx.filter fun j => j < i + n) i).2.2 with h | h
  · rw [fwd, h]; exact hi
  · exact (List.mem_filter.mp h).1

/-- `f(i)` starts inside the occurrence at `i`. -/
theorem fwd_lt {n : ℕ} {idx : List ℕ} {i : ℕ} (hn : 0 < n) : fwd n idx i < i + n := by
  rw [fwd]
  rcases (foldr_max_spec (idx.filter fun j => j < i + n) i).2.2 with h | h
  · rw [h]; omega
  · simpa using (List.mem_filter.mp h).2

/-- Every occurrence that starts inside the occurrence at `i` is at most `f(i)`. -/
theorem le_fwd_of_mem {n : ℕ} {idx : List ℕ} {i j : ℕ} (hj : j ∈ idx) (hjn : j < i + n) :
    j ≤ fwd n idx i :=
  (foldr_max_spec _ i).2.1 j (List.mem_filter.mpr ⟨hj, by simpa using hjn⟩)

variable {Symbol : Type*} [DecidableEq Symbol]

/-- Lemma 21, first part: for occurrences `i` and `j < f(i)` of `α`, every extendable prefix of `α`
is longer than `j - i`, so that no prefix of `w[i..j−1]` is extendable. Indeed, the occurrences at
`j` and `f(i)` overlap in more than `j - i` symbols (Lemma 17). -/
theorem sub_lt_length_of_lt_fwd {w α β : List Symbol} {i j : ℕ} (hβ : β.IsExtendablePrefix α w)
    (hα : α ≠ []) (hi : α.OccursAt w i) (hj : α.OccursAt w j)
    (hjf : j < fwd α.length (α.occurrences w) i) : j - i < β.length := by
  have hf := (List.mem_occurrences_of_ne_nil hα).mp
    (fwd_mem (n := α.length) ((List.mem_occurrences_of_ne_nil hα).mpr hi))
  have := hβ.add_length_sub_lt_length hj hf hjf
  have := fwd_lt (idx := α.occurrences w) (i := i) (List.length_pos_iff.mpr hα)
  omega

/-- Lemma 21, second part: for occurrences `i < j` of `α`, every extendable prefix of `α` is longer
than `f(i) - j`, so that no prefix of `w[j..f(i)−1]` is extendable. Indeed, the occurrences at `i`
and `j` overlap in more than `f(i) - j` symbols (Lemma 17). -/
theorem fwd_sub_lt_length {w α β : List Symbol} {i j : ℕ} (hβ : β.IsExtendablePrefix α w)
    (hα : α ≠ []) (hi : α.OccursAt w i) (hj : α.OccursAt w j) (hij : i < j) :
    fwd α.length (α.occurrences w) i - j < β.length := by
  have := hβ.add_length_sub_lt_length hi hj hij
  have := fwd_lt (idx := α.occurrences w) (i := i) (List.length_pos_iff.mpr hα)
  omega

end Rewb
