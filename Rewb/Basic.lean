/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Mathlib.Computability.Language
public import Mathlib.Data.Finset.Union

/-!
# The language of a rewb, the simulated automaton and the oracles

This file sets up what the matching algorithms work with.

* `Rewb.rewbLang L₀ L L₁ L₂`: the language of the rewb `e₀(e)₁e₁\1e₂` (Definition 1), stated for
  the languages `L₀`, `L`, `L₁` and `L₂` of `e₀`, `e`, `e₁` and `e₂`.
* `Rewb.Simulator`: the automaton for `e₁` as the algorithms simulate it, given by the paper's
  `Δ(q, a)`, the initial simulation set `cl_ε(q₀)` and the accepting states `F` (Section 2, after
  Definition 3; Algorithm 1, line 1). Its `stepSet` and `evalFrom` compute `Δ(S, a)` and
  `Δ(S, u)`; `evalFrom_append` and `evalFrom_union` are Lemma 8.
* `Rewb.IsPrefixOracle` and `Rewb.IsSuffixOracle`: what the arrays `Pre` and `Suf` (Section 3,
  before the proof of Theorem 5) and `Pre_α` (Algorithm 2, line 2) tell the algorithms.

Positions are 0-based, while the paper's are 1-based (Section 2). Prefixes are described by their
length.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {Symbol : Type*}

/-- The language of the rewb `e₀(e)₁e₁\1e₂` (Definition 1), for the languages `L₀`, `L`, `L₁` and
`L₂` of `e₀`, `e`, `e₁` and `e₂`: the words `w₀ ++ α ++ w₁ ++ α ++ w₂` with `w₀ ∈ L₀`, `α ∈ L`,
`w₁ ∈ L₁` and `w₂ ∈ L₂`. The word `α` is the one that `(e)₁` captures and `\1` repeats. -/
def rewbLang (L₀ L L₁ L₂ : Language Symbol) : Language Symbol :=
  {w | ∃ w₀ α w₁ w₂, w₀ ∈ L₀ ∧ α ∈ L ∧ w₁ ∈ L₁ ∧ w₂ ∈ L₂ ∧ w = w₀ ++ α ++ w₁ ++ α ++ w₂}

theorem mem_rewbLang {L₀ L L₁ L₂ : Language Symbol} {w : List Symbol} :
    w ∈ rewbLang L₀ L L₁ L₂ ↔
      ∃ w₀ α w₁ w₂, w₀ ∈ L₀ ∧ α ∈ L ∧ w₁ ∈ L₁ ∧ w₂ ∈ L₂ ∧ w = w₀ ++ α ++ w₁ ++ α ++ w₂ :=
  Iff.rfl

/-- An automaton presented for NFA simulation. For an NFA `(Q, δ, q₀, F)` with ε-moves
(Definition 3), `step q a` is the paper's `Δ(q, a) = cl_ε(δ(q, a))`, `start` is the initial
simulation set `cl_ε(q₀)` and `accept` is `F`: the triple `(Δ, cl_ε(q₀), F)` that Algorithm 1 takes
from `N_e1` in line 1. -/
structure Simulator (State Symbol : Type*) where
  /-- The states reached from a state by reading a symbol. -/
  step : State → Symbol → Finset State
  /-- The simulation set before anything is read. -/
  start : Finset State
  /-- The accepting states. -/
  accept : Finset State

namespace Simulator

variable {State : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- `Δ(S, a)`, the states reached from a state of `S` by reading `a` (Section 2, after
Definition 3). -/
def stepSet (S : Finset State) (a : Symbol) : Finset State :=
  S.biUnion (M.step · a)

/-- `Δ(S, u)`, the states reached from a state of `S` by reading `u` (Section 2, after
Definition 3). -/
def evalFrom (S : Finset State) (u : List Symbol) : Finset State :=
  u.foldl M.stepSet S

/-- The words that lead from `start` to an accepting state: the paper's
`L(N) = {w ∣ Δ(cl_ε(q₀), w) ∩ F ≠ ∅}` (Section 2, after Definition 3). -/
def accepts : Language Symbol :=
  {u | ∃ q ∈ M.evalFrom M.start u, q ∈ M.accept}

instance : DecidablePred (· ∈ M.accepts) := fun u =>
  inferInstanceAs (Decidable (∃ q ∈ M.evalFrom M.start u, q ∈ M.accept))

variable {M}

theorem mem_stepSet {S : Finset State} {a : Symbol} {q : State} :
    q ∈ M.stepSet S a ↔ ∃ p ∈ S, q ∈ M.step p a :=
  Finset.mem_biUnion

theorem mem_accepts {u : List Symbol} :
    u ∈ M.accepts ↔ ∃ q ∈ M.evalFrom M.start u, q ∈ M.accept :=
  Iff.rfl

variable (M)

@[simp]
theorem stepSet_empty (a : Symbol) : M.stepSet ∅ a = ∅ :=
  Finset.biUnion_empty

@[simp]
theorem stepSet_singleton (q : State) (a : Symbol) : M.stepSet {q} a = M.step q a :=
  Finset.singleton_biUnion

@[simp]
theorem stepSet_union (S T : Finset State) (a : Symbol) :
    M.stepSet (S ∪ T) a = M.stepSet S a ∪ M.stepSet T a :=
  Finset.union_biUnion

@[simp]
theorem evalFrom_nil (S : Finset State) : M.evalFrom S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (S : Finset State) (a : Symbol) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

@[simp]
theorem evalFrom_cons (S : Finset State) (a : Symbol) (u : List Symbol) :
    M.evalFrom S (a :: u) = M.evalFrom (M.stepSet S a) u :=
  rfl

/-- The first half of Lemma 8: `Δ(S, uv) = Δ(Δ(S, u), v)`. -/
@[simp]
theorem evalFrom_append (S : Finset State) (u v : List Symbol) :
    M.evalFrom S (u ++ v) = M.evalFrom (M.evalFrom S u) v :=
  List.foldl_append

@[simp]
theorem evalFrom_empty (u : List Symbol) : M.evalFrom ∅ u = ∅ := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [evalFrom_cons, stepSet_empty, ih]

/-- The second half of Lemma 8: `Δ(S, u) ∪ Δ(T, u) = Δ(S ∪ T, u)`. -/
@[simp]
theorem evalFrom_union (S T : Finset State) (u : List Symbol) :
    M.evalFrom (S ∪ T) u = M.evalFrom S u ∪ M.evalFrom T u := by
  induction u generalizing S T with
  | nil => rfl
  | cons a u ih => rw [evalFrom_cons, evalFrom_cons, evalFrom_cons, stepSet_union, ih]

end Simulator

/-- `f` tells which prefixes of `w` are in `L`: for `i ≤ w.length`, `f i = true` exactly when
`w.take i ∈ L`. The paper's arrays `Pre` (for `e₀` and the input word; Section 3, before the proof
of Theorem 5) and `Pre_α` (for `e` and `α`; Algorithm 2, line 2) are such oracles, with the same
indices. -/
def IsPrefixOracle (L : Language Symbol) (w : List Symbol) (f : ℕ → Bool) : Prop :=
  ∀ i ≤ w.length, f i = true ↔ w.take i ∈ L

/-- `f` tells which suffixes of `w` are in `L`: for `j ≤ w.length`, `f j = true` exactly when
`w.drop j ∈ L`. The paper's array `Suf` (for `e₂` and the input word; Section 3, before the proof
of Theorem 5) is such an oracle, shifted by one: `f j` is its entry `Suf[j + 1]`. -/
def IsSuffixOracle (L : Language Symbol) (w : List Symbol) (f : ℕ → Bool) : Prop :=
  ∀ j ≤ w.length, f j = true ↔ w.drop j ∈ L

variable (L : Language Symbol) [DecidablePred (· ∈ L)] (w : List Symbol)

/-- The prefix oracle that decides each membership directly. -/
def prefixOracle (i : ℕ) : Bool :=
  decide (w.take i ∈ L)

/-- The suffix oracle that decides each membership directly. -/
def suffixOracle (j : ℕ) : Bool :=
  decide (w.drop j ∈ L)

theorem isPrefixOracle_prefixOracle : IsPrefixOracle L w (prefixOracle L w) :=
  fun _ _ => decide_eq_true_iff

theorem isSuffixOracle_suffixOracle : IsSuffixOracle L w (suffixOracle L w) :=
  fun _ _ => decide_eq_true_iff

end Rewb
