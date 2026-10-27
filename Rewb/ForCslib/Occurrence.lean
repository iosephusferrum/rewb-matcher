/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Data.List.Occurrence

/-!
# The number of occurrences

A nonempty word occurs in `w` at most `w.length` times, since it cannot start at the end of `w`.
Nogami and Terauchi's Match3A and Match3B visit each occurrence once, so this bounds their
bookkeeping, the length of the occurrence array `Idx_α` (Section 2).

## Main statements

* `List.length_occurrences_le`: a nonempty word occurs at most `w.length` times in `w`.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace List

variable {α : Type*} [DecidableEq α] {u w : List α}

/-- A nonempty word occurs at most `w.length` times in `w`: it cannot start at the end of `w`. -/
theorem length_occurrences_le (hu : u ≠ []) : (u.occurrences w).length ≤ w.length := by
  have hend : ¬u.OccursAt w w.length := fun h => by
    have := h.add_length_le hu
    have := length_pos_iff.mpr hu
    omega
  have h₁ : ((range w.length).filter fun i => decide (u.OccursAt w i)).length ≤ w.length :=
    (length_filter_le _ _).trans (by simp)
  have h₂ : ([w.length].filter fun i => decide (u.OccursAt w i)).length = 0 := by simp [hend]
  rw [occurrences, range_succ, filter_append, length_append]
  omega

end List
