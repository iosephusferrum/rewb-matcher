/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Basic

/-!
# NFA simulation with injection

Injection (Section 3.1.1) adds a set of states to the simulation set at chosen positions, so that
one simulation follows runs that start at several positions of the input word. Summarization
(Section 3.1.2) simulates from every state at once; here it is injecting the singleton `{q}`, once
for each state `q`.

## Main definitions

* `Rewb.Simulator.evalInject`: the simulation of a word with injection after marked positions.

## Main statements

* `Rewb.Simulator.mem_evalInject`: the injection lemma. A simulation with injection ends in the
  states that the simulation from the initial set reaches, together with those that simulations
  started right after a marked position reach. It generalizes the equation after Lemma 8, and
  Propositions 9, 13 and 22 and Lemma 14 are instances of it.
* `Rewb.Simulator.evalInject_append`: simulating `u ++ v` is simulating `u`, then `v`.
* `Rewb.Simulator.biUnion_evalInject_singleton`: summarization composes. Injecting each state `q`
  of `T` as `{q}` into its own simulation and merging the results is injecting `T`; this is how
  Algorithm 2 combines `T` and `S` in line 9.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb.Simulator

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Simulation with injection (Section 3.1.1): read `u`, whose first symbol sits at position `i`
of the input word, starting from the simulation set `S`, and right after reading a position `p`
with `mark p`, add `I` to the simulation set.

With `I = M.start` this is the inner loop of Algorithm 1 (lines 5 to 7), where `mark p` says that
`p` is `ique`. With `I = {q}` it is the `q`-th component of the simulation with summarization in
Algorithms 2 and 4 (Section 3.1.2). The paper's guards `S ≠ ∅` only save work, since
`Δ(∅, a) = ∅` (`stepSet_empty`). -/
def evalInject (I : Finset State) (mark : ℕ → Bool) :
    Finset State → ℕ → List Symbol → Finset State
  | S, _, [] => S
  | S, i, a :: u =>
    evalInject I mark (if mark i then M.stepSet S a ∪ I else M.stepSet S a) (i + 1) u

@[simp]
theorem evalInject_nil (I : Finset State) (mark : ℕ → Bool) (S : Finset State) (i : ℕ) :
    M.evalInject I mark S i [] = S :=
  rfl

@[simp]
theorem evalInject_cons (I : Finset State) (mark : ℕ → Bool) (S : Finset State) (i : ℕ)
    (a : Symbol) (u : List Symbol) :
    M.evalInject I mark S i (a :: u) =
      M.evalInject I mark (if mark i then M.stepSet S a ∪ I else M.stepSet S a) (i + 1) u :=
  rfl

/-- Simulating `u ++ v` with injection is simulating `u`, then `v` from where `u` ends. -/
theorem evalInject_append (I : Finset State) (mark : ℕ → Bool) (S : Finset State) (i : ℕ)
    (u v : List Symbol) :
    M.evalInject I mark S i (u ++ v) =
      M.evalInject I mark (M.evalInject I mark S i u) (i + u.length) v := by
  induction u generalizing S i with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append, evalInject_cons, ih, List.length_cons]
    congr 1
    omega

variable {M} in
/-- A simulation with injection only looks at the marks of the positions it reads. -/
theorem evalInject_congr {I : Finset State} {mark mark' : ℕ → Bool} {u : List Symbol} :
    ∀ {S : Finset State} {i : ℕ}, (∀ k < u.length, mark (i + k) = mark' (i + k)) →
      M.evalInject I mark S i u = M.evalInject I mark' S i u := by
  induction u with
  | nil => intro S i _; rfl
  | cons a u ih =>
    intro S i h
    have h0 : mark i = mark' i := h 0 (by simp)
    rw [evalInject_cons, evalInject_cons, h0]
    exact ih fun k hk => by
      have := h (k + 1) (by simp [hk])
      rwa [show i + (k + 1) = i + 1 + k by omega] at this

variable {M} in
/-- The injection lemma (Section 3.1.1): a simulation with injection reaches `q` exactly when the
simulation from `S` reaches it, or a simulation started from `I` right after a marked position
`i + k` does. For a single injection this is the equation after Lemma 8; Propositions 9, 13 and 22
and Lemma 14 are instances. -/
theorem mem_evalInject {I : Finset State} {mark : ℕ → Bool} {S : Finset State} {i : ℕ}
    {u : List Symbol} {q : State} :
    q ∈ M.evalInject I mark S i u ↔
      q ∈ M.evalFrom S u ∨
        ∃ k < u.length, mark (i + k) = true ∧ q ∈ M.evalFrom I (u.drop (k + 1)) := by
  induction u generalizing S i with
  | nil => simp
  | cons a u ih =>
    have e : ∀ m, i + 1 + m = i + (m + 1) := fun m => by omega
    rw [evalInject_cons, ih, List.length_cons, Nat.exists_lt_succ_left]
    simp only [e, Nat.add_zero, List.drop_succ_cons, List.drop_zero, evalFrom_cons]
    cases mark i
    · simp
    · simp [or_assoc]

/-- The simulation from a set is the union of the simulations from its states. -/
theorem evalFrom_eq_biUnion_singleton (S : Finset State) (u : List Symbol) :
    M.evalFrom S u = S.biUnion fun q => M.evalFrom {q} u := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S _ ih =>
    rw [Finset.insert_eq, evalFrom_union, ih, Finset.union_biUnion, Finset.singleton_biUnion]

/-- Summarization composes (Section 3.1.2; Algorithm 2, line 9): injecting each state `q` of `T`
as `{q}` into its own simulation from the empty set, and merging the results, is injecting `T`. -/
theorem biUnion_evalInject_singleton (T : Finset State) (mark : ℕ → Bool) (i : ℕ)
    (u : List Symbol) :
    (T.biUnion fun q => M.evalInject {q} mark ∅ i u) = M.evalInject T mark ∅ i u := by
  ext p
  simp only [Finset.mem_biUnion, mem_evalInject, evalFrom_empty, Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨q, hq, k, hk, hm, hp⟩
    refine ⟨k, hk, hm, ?_⟩
    rw [evalFrom_eq_biUnion_singleton, Finset.mem_biUnion]
    exact ⟨q, hq, hp⟩
  · rintro ⟨k, hk, hm, hp⟩
    rw [evalFrom_eq_biUnion_singleton, Finset.mem_biUnion] at hp
    obtain ⟨q, hq, hp⟩ := hp
    exact ⟨q, hq, k, hk, hm, hp⟩

end Rewb.Simulator
