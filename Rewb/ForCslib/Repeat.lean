/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Data.List.Repeat
public import Mathlib.Data.Finset.Card

/-!
# The number of right-maximal repeats

A word of length `n` has at most `n - 1` right-maximal repeats [Gusfield1997], although it can
have `Θ(n²)` repeats. Nogami and Terauchi's algorithm runs Match once per right-maximal repeat, so
this bounds its running time (Section 2 and Theorem 5, where the number is `µ_right`).

The proof adds one letter at a time. Prepending a letter `c` to `w` keeps every right-maximal
repeat of `w`, since its occurrences move one position to the right together with the letters
that follow them (`IsRightMaximalRepeat.cons`). And it makes at most one new right-maximal repeat
(`eq_of_isRightMaximalRepeat_cons`): a new one must occur at the start of `c :: w`, and also in
`w`, while its extension by the next letter of `c :: w` does not occur in `w`; so it is the
longest prefix of `c :: w` that occurs in `w`.

## Main statements

* `List.length_rightMaximalRepeats_cons_le`: prepending a letter adds at most one right-maximal
  repeat.
* `List.length_rightMaximalRepeats_le`: a word `w` has at most `w.length - 1` right-maximal
  repeats.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace List

variable {α : Type*} {u w : List α} {c : α}

/-- The occurrences in `c :: w` after its first position are the occurrences in `w`. -/
theorem occursAt_cons_succ {i : ℕ} : u.OccursAt (c :: w) (i + 1) ↔ u.OccursAt w i :=
  Iff.rfl

/-- The letters of `c :: w` after its first position are those of `w`. -/
private theorem getElem?_cons_succ_add (c : α) (w : List α) (i k : ℕ) :
    (c :: w)[i + 1 + k]? = w[i + k]? := by
  rw [show i + 1 + k = i + k + 1 by omega, getElem?_cons_succ]

/-- Prepending a letter keeps every right-maximal repeat. -/
theorem IsRightMaximalRepeat.cons (h : u.IsRightMaximalRepeat w) (c : α) :
    u.IsRightMaximalRepeat (c :: w) := by
  obtain ⟨hu, i, j, hi, hj, hne⟩ := h
  refine ⟨hu, i + 1, j + 1, occursAt_cons_succ.mpr hi, occursAt_cons_succ.mpr hj, ?_⟩
  rwa [getElem?_cons_succ_add, getElem?_cons_succ_add]

/-- A right-maximal repeat of `c :: w` that is not one of `w` is a prefix of `c :: w` that occurs
in `w`, while its extension by one more letter of `c :: w` does not occur in `w`. -/
theorem IsRightMaximalRepeat.of_cons (h : u.IsRightMaximalRepeat (c :: w))
    (hw : ¬u.IsRightMaximalRepeat w) :
    u <+: c :: w ∧ (∃ j, u.OccursAt w j) ∧ ∀ m, ¬((c :: w).take (u.length + 1)).OccursAt w m := by
  obtain ⟨hu, i, j, hi, hj, hne⟩ := h
  -- With one occurrence at the start and the other later, the later one is in `w`, and an
  -- occurrence of the extension in `w` would make `u` right-maximal in `w`.
  have key : ∀ {j : ℕ}, u.OccursAt (c :: w) 0 → u.OccursAt (c :: w) (j + 1) →
      (c :: w)[0 + u.length]? ≠ (c :: w)[j + 1 + u.length]? →
      u <+: c :: w ∧ (∃ j, u.OccursAt w j) ∧
        ∀ m, ¬((c :: w).take (u.length + 1)).OccursAt w m := by
    intro j h₀ hj hne
    have hp := occursAt_zero.mp h₀
    have hj' : u.OccursAt w j := occursAt_cons_succ.mp hj
    have hlen := hj'.add_length_le hu
    refine ⟨hp, ⟨j, hj'⟩, fun m hm => hw ⟨hu, m, j, ?_, hj', ?_⟩⟩
    · refine hm.of_prefix (prefix_of_prefix_length_le hp (take_prefix _ _) ?_)
      simp only [length_take, length_cons]
      omega
    · have hk : u.length < ((c :: w).take (u.length + 1)).length := by
        simp only [length_take, length_cons]
        omega
      rw [occursAt_iff_getElem?] at hm
      rw [hm u.length hk, getElem_take, ← getElem?_eq_getElem, ← getElem?_cons_succ_add c w j]
      rwa [Nat.zero_add] at hne
  rcases i with _ | i <;> rcases j with _ | j
  · exact absurd rfl hne
  · exact key hi hj hne
  · exact key hj hi (Ne.symm hne)
  · exact absurd ⟨hu, i, j, occursAt_cons_succ.mp hi, occursAt_cons_succ.mp hj,
      by rwa [getElem?_cons_succ_add, getElem?_cons_succ_add] at hne⟩ hw

/-- Prepending a letter makes at most one new right-maximal repeat: of two new ones, the longer
would contain the extension of the shorter by one letter, which does not occur in `w`. -/
theorem eq_of_isRightMaximalRepeat_cons {u' : List α} (h : u.IsRightMaximalRepeat (c :: w))
    (hw : ¬u.IsRightMaximalRepeat w) (h' : u'.IsRightMaximalRepeat (c :: w))
    (hw' : ¬u'.IsRightMaximalRepeat w) : u = u' := by
  obtain ⟨hp, ⟨j, hj⟩, hext⟩ := h.of_cons hw
  obtain ⟨hp', ⟨j', hj'⟩, hext'⟩ := h'.of_cons hw'
  have hlen : u.length = u'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · refine hext j' (hj'.of_prefix (prefix_of_prefix_length_le (take_prefix _ _) hp' ?_))
      simp only [length_take]
      omega
    · refine hext' j (hj.of_prefix (prefix_of_prefix_length_le (take_prefix _ _) hp ?_))
      simp only [length_take]
      omega
  rw [prefix_iff_eq_take.mp hp, prefix_iff_eq_take.mp hp', hlen]

/-- A word of length at most `1` has no right-maximal repeat: a nonempty word occurs in it only
at the start. -/
theorem rightMaximalRepeats_eq_nil_of_length_le_one [DecidableEq α] (hw : w.length ≤ 1) :
    w.rightMaximalRepeats = [] := by
  refine eq_nil_iff_forall_not_mem.mpr fun u hu => ?_
  obtain ⟨hu, i, j, hi, hj, hne⟩ := mem_rightMaximalRepeats.mp hu
  have := hi.add_length_le hu
  have := hj.add_length_le hu
  have := length_pos_iff.mpr hu
  obtain rfl : i = j := by omega
  exact hne rfl

/-- Prepending a letter adds at most one right-maximal repeat. -/
theorem length_rightMaximalRepeats_cons_le [DecidableEq α] (c : α) (w : List α) :
    (c :: w).rightMaximalRepeats.length ≤ w.rightMaximalRepeats.length + 1 := by
  rw [← toFinset_card_of_nodup (nodup_rightMaximalRepeats _),
    ← toFinset_card_of_nodup (nodup_rightMaximalRepeats w)]
  have hsub : w.rightMaximalRepeats.toFinset ⊆ (c :: w).rightMaximalRepeats.toFinset := by
    intro u hu
    simp only [mem_toFinset, mem_rightMaximalRepeats] at hu ⊢
    exact hu.cons c
  have hnew :
      ((c :: w).rightMaximalRepeats.toFinset \ w.rightMaximalRepeats.toFinset).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun u hu u' hu' => ?_
    simp only [Finset.mem_sdiff, mem_toFinset, mem_rightMaximalRepeats] at hu hu'
    exact eq_of_isRightMaximalRepeat_cons hu.1 hu.2 hu'.1 hu'.2
  have := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- A word of length `n` has at most `n - 1` right-maximal repeats [Gusfield1997], the paper's
`µ_right ≤ n - 1` (Theorem 5). -/
theorem length_rightMaximalRepeats_le [DecidableEq α] (w : List α) :
    w.rightMaximalRepeats.length ≤ w.length - 1 := by
  induction w with
  | nil => rw [rightMaximalRepeats_eq_nil_of_length_le_one (by simp)]; simp
  | cons c w ih =>
    cases w with
    | nil => rw [rightMaximalRepeats_eq_nil_of_length_le_one (by simp)]; simp
    | cons c' w =>
      have := length_rightMaximalRepeats_cons_le c (c' :: w)
      simp only [length_cons] at ih ⊢
      omega

end List
