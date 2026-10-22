/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Injection

/-!
# Intmed: the simulation along one occurrence of the repeat

Algorithm 3 (`Intmed(ibeg, iend)`, Section 3.1.2) runs the automaton of `e₁` along one occurrence
of `α` in the input word. Before reading each symbol of `α`, and at the end, it injects the initial
simulation set when `e` matches the part of `α` read so far and `e₂` matches the rest of the word.
Algorithm 2 (line 8) and Algorithm 4 (line 11) compose the result with their simulation with
summarization.

## Main definitions

* `Rewb.intmed`: Algorithm 3.

## Main statements

* `Rewb.mem_intmed`: Lemma 14, the correctness of Intmed.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Algorithm 3, `Intmed(ibeg, iend)`, on the occurrence of `α` at position `p` of the input word.
It goes through the prefix lengths `k` from `kbeg` to `|α|`. When `e` matches `α.take k` (`Pre_α`)
and `e₂` matches the input word after that prefix (`suf (p + k)`), it injects `cl_ε(q₀)` (line 3);
then it reads `α[k]` (line 4).

The paper counts positions of the input word instead: in its 1-based numbering the occurrence ends
at `iend = p + |α|`, the loop starts at `ibeg = p + kbeg` and its `i` is `p + k`. It reads
`w[i + 1]`, which is `α[k]` since `α` occurs at `p`. Algorithm 2 starts at `kbeg = 1` and
Algorithm 4 at `kbeg = d + 1`. -/
def intmed (α : List Symbol) (p kbeg : ℕ) (preα suf : ℕ → Bool) : Finset State :=
  M.evalInject M.start (fun k => preα (k + 1) && suf (p + (k + 1)))
    (if preα kbeg && suf (p + kbeg) then M.start else ∅) kbeg (α.drop kbeg)

variable {M}

/-- Lemma 14, the correctness of Intmed: its simulation set consists of the states that
`cl_ε(q₀)` reaches by reading the rest `α.drop k` of `α`, for the prefix lengths `k` from `kbeg`
to `|α|` such that `e` matches `α.take k` and `e₂` matches the input word after it. -/
theorem mem_intmed {α : List Symbol} {p kbeg : ℕ} {preα suf : ℕ → Bool} {s : State}
    (hk : kbeg ≤ α.length) :
    s ∈ intmed M α p kbeg preα suf ↔
      ∃ k, kbeg ≤ k ∧ k ≤ α.length ∧ preα k = true ∧ suf (p + k) = true ∧
        s ∈ M.evalFrom M.start (α.drop k) := by
  rw [intmed, Simulator.mem_evalInject]
  simp only [List.length_drop, List.drop_drop, Bool.and_eq_true]
  constructor
  · rintro (hs | ⟨j, hj, ⟨hpre, hsuf⟩, hs⟩)
    · by_cases hc : preα kbeg = true ∧ suf (p + kbeg) = true
      · rw [ite_eq_left hc] at hs
        exact ⟨kbeg, le_rfl, hk, hc.1, hc.2, hs⟩
      · rw [ite_eq_right hc, Simulator.evalFrom_empty] at hs
        exact absurd hs (Finset.notMem_empty s)
    · refine ⟨kbeg + j + 1, by omega, by omega, hpre, hsuf, ?_⟩
      rwa [Nat.add_assoc]
  · rintro ⟨k, hk₁, hk₂, hpre, hsuf, hs⟩
    rcases Nat.eq_or_lt_of_le hk₁ with rfl | hlt
    · exact .inl (by rwa [ite_eq_left ⟨hpre, hsuf⟩])
    · refine .inr ⟨k - kbeg - 1, by omega, ?_⟩
      rw [show kbeg + (k - kbeg - 1) + 1 = k by omega,
        show kbeg + (k - kbeg - 1 + 1) = k by omega]
      exact ⟨⟨hpre, hsuf⟩, hs⟩

end Rewb
