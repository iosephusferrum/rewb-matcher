/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.ToNA
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.SetTheory.Cardinal.Finite
public import Rewb.Basic

/-!
# The simulator of a finite ε-NFA

For an ε-NFA with finitely many states and decidable transitions (Definition 3), this file
computes the triple `(Δ, cl_ε(q₀), F)` that the algorithms simulate (Section 2, after
Definition 3).

* `Rewb.εClosureFinset a S`: the ε-closure `cl_ε(S)`, computed by following ε-transitions once per
  state; `coe_εClosureFinset` identifies it with `εNA.εClosure`.
* `Rewb.Simulator.ofEpsilonNA a`: the simulator with `Δ(q, x) = cl_ε(δ(q, x))`, the initial
  simulation set `cl_ε(q₀)` and the accepting states `F`; `accepts_ofEpsilonNA` says that it
  accepts exactly the language of `a`.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

open Cslib Cslib.Automata Acceptor Relation

/-- Being related within `n + 1` steps is being related within `n` steps, or within `n` steps to
an element related to the target. -/
private theorem relatesWithinSteps_succ_iff {α : Type*} {r : α → α → Prop} {s t : α} {n : ℕ} :
    RelatesWithinSteps r s t (n + 1) ↔
      RelatesWithinSteps r s t n ∨ ∃ u, RelatesWithinSteps r s u n ∧ r u t := by
  constructor
  · rintro ⟨m, hm, h⟩
    rcases Nat.lt_or_eq_of_le hm with hm | rfl
    · exact .inl ⟨m, Nat.lt_succ_iff.mp hm, h⟩
    · obtain ⟨u, hu, hr⟩ := h.succ
      exact .inr ⟨u, ⟨n, le_rfl, hu⟩, hr⟩
  · rintro (h | ⟨u, ⟨m, hm, h⟩, hr⟩)
    · exact RelatesWithinSteps.mono (Nat.le_succ n) h
    · exact ⟨m + 1, Nat.succ_le_succ hm, .tail _ _ _ _ h hr⟩

variable {State Symbol : Type*}

/-- A step of `toNAFinAcc` on `x` is an `x`-transition between two ε-closures. -/
theorem setImage_toNAFinAcc {a : εNA.FinAcc State Symbol} (S : Set State) (x : Symbol) :
    a.toNAFinAcc.setImage S x = a.εClosure (a.setImage (a.εClosure S) (some x)) := by
  rw [εNA.εClosure, εNA.εClosure, ← LTS.saturate_setImage_of_ne_τ _ (Option.some_ne_none x)]
  ext t
  simp [εNA.FinAcc.toNAFinAcc, LTS.mem_setImage]

variable [Fintype State] [DecidableEq State] (a : εNA.FinAcc State Symbol)
  [∀ s μ t, Decidable (a.Tr s μ t)]

/-- `S` together with the states that an ε-transition leads to from a state of `S`. -/
def εStep (S : Finset State) : Finset State :=
  S ∪ Finset.univ.filter fun t => ∃ s ∈ S, a.Tr s none t

/-- The ε-closure `cl_ε(S)` (Section 2, after Definition 3): `εStep` applied once per state, which
is enough for every path of ε-transitions that visits no state twice. -/
def εClosureFinset (S : Finset State) : Finset State :=
  (εStep a)^[Fintype.card State] S

variable {a}

theorem mem_εStep {S : Finset State} {t : State} :
    t ∈ εStep a S ↔ t ∈ S ∨ ∃ s ∈ S, a.Tr s none t := by
  simp [εStep]

/-- After `n` rounds of `εStep`, the states are those that at most `n` ε-transitions lead to. -/
theorem mem_iterate_εStep {n : ℕ} {S : Finset State} {t : State} :
    t ∈ (εStep a)^[n] S ↔ ∃ s ∈ S, RelatesWithinSteps (a.Tr · none ·) s t n := by
  induction n generalizing t with
  | zero => simp [RelatesWithinSteps.zero_iff]
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_εStep]
    simp only [ih, relatesWithinSteps_succ_iff]
    constructor
    · rintro (⟨s, hs, h⟩ | ⟨u, ⟨s, hs, h⟩, hr⟩)
      · exact ⟨s, hs, .inl h⟩
      · exact ⟨s, hs, .inr ⟨u, h, hr⟩⟩
    · rintro ⟨s, hs, h | ⟨u, h, hr⟩⟩
      · exact .inl ⟨s, hs, h⟩
      · exact .inr ⟨u, ⟨s, hs, h⟩, hr⟩

theorem mem_εClosureFinset {S : Finset State} {t : State} :
    t ∈ εClosureFinset a S ↔ ∃ s ∈ S, a.τSTr s t := by
  rw [εClosureFinset, mem_iterate_εStep]
  refine exists_congr fun s => and_congr_right fun _ =>
    ⟨fun ⟨_, _, h⟩ => h.reflTransGen, fun h => ?_⟩
  obtain ⟨n, h, hlt⟩ := ReflTransGen.relatesInSteps_lt_encard (r := (a.Tr · none ·)) h
  have hn := hlt.trans_le Set.encard_le_card
  rw [ENat.card_eq_coe_fintype_card, ENat.natCast_lt_natCast] at hn
  exact ⟨n, hn.le, h⟩

theorem coe_εClosureFinset (S : Finset State) :
    (εClosureFinset a S : Set State) = a.εClosure S := by
  ext t
  rw [Finset.mem_coe, mem_εClosureFinset, εNA.εClosure, LTS.mem_τClosure_iff]
  rfl

variable (a) [DecidablePred (· ∈ a.start)] [DecidablePred (· ∈ a.accept)]

/-- The simulator of `a`: `Δ(q, x) = cl_ε(δ(q, x))`, the initial simulation set `cl_ε(q₀)` and the
accepting states `F` (Section 2, after Definition 3). The initial states of `a` take the place of
`q₀`. -/
def Simulator.ofEpsilonNA : Simulator State Symbol where
  step q x := εClosureFinset a (Finset.univ.filter fun t => a.Tr q (some x) t)
  start := εClosureFinset a (Finset.univ.filter (· ∈ a.start))
  accept := Finset.univ.filter (· ∈ a.accept)

variable {a}

theorem coe_start_ofEpsilonNA :
    ((Simulator.ofEpsilonNA a).start : Set State) = a.εClosure a.start := by
  change (εClosureFinset a _ : Set State) = _
  rw [coe_εClosureFinset, Finset.coe_filter_univ, Set.ofPred_mem_eq]

/-- From an ε-closed set, a step of the simulator is a step of `toNAFinAcc`. -/
theorem coe_stepSet_ofEpsilonNA {S : Finset State} (hS : a.εClosure S = S) (x : Symbol) :
    ((Simulator.ofEpsilonNA a).stepSet S x : Set State) = a.toNAFinAcc.setImage S x := by
  rw [setImage_toNAFinAcc, hS]
  ext t
  simp only [Finset.mem_coe, Simulator.mem_stepSet, Simulator.ofEpsilonNA, mem_εClosureFinset,
    Finset.mem_filter, Finset.mem_univ, true_and, εNA.εClosure, LTS.mem_τClosure_iff,
    LTS.mem_setImage]
  constructor
  · rintro ⟨q, hq, u, hu, h⟩
    exact ⟨u, ⟨q, hq, hu⟩, h⟩
  · rintro ⟨u, ⟨q, hq, hu⟩, h⟩
    exact ⟨q, hq, u, hu, h⟩

/-- From an ε-closed set, the simulator follows `toNAFinAcc`. -/
theorem coe_evalFrom_ofEpsilonNA {S : Finset State} (hS : a.εClosure S = S) (u : List Symbol) :
    ((Simulator.ofEpsilonNA a).evalFrom S u : Set State) = u.foldl a.toNAFinAcc.setImage S := by
  induction u generalizing S with
  | nil => rfl
  | cons x u ih =>
    have h := coe_stepSet_ofEpsilonNA hS x
    have hclosed : a.εClosure ((Simulator.ofEpsilonNA a).stepSet S x) =
        (Simulator.ofEpsilonNA a).stepSet S x := by
      rw [h, setImage_toNAFinAcc]
      exact LTS.τClosure_τClosure _ _
    rw [Simulator.evalFrom_cons, ih hclosed, h, List.foldl_cons]

/-- The simulator of `a` accepts exactly the language of `a`. -/
@[simp]
theorem accepts_ofEpsilonNA : (Simulator.ofEpsilonNA a).accepts = language a := by
  rw [← εNA.FinAcc.toNAFinAcc_language_eq]
  ext u
  -- The initial set is ε-closed, so from it the simulator follows `toNAFinAcc`.
  have hstart : a.εClosure ((Simulator.ofEpsilonNA a).start : Set State) =
      (Simulator.ofEpsilonNA a).start := by
    rw [coe_start_ofEpsilonNA]
    exact LTS.τClosure_τClosure _ _
  have h := coe_evalFrom_ofEpsilonNA hstart u
  rw [coe_start_ofEpsilonNA] at h
  rw [Simulator.mem_accepts, mem_language]
  constructor
  · rintro ⟨q, hq, hacc⟩
    rw [← Finset.mem_coe, h, LTS.mem_foldl_setImage] at hq
    obtain ⟨s, hs, hrun⟩ := hq
    exact ⟨s, hs, q, (Finset.mem_filter.mp hacc).2, hrun⟩
  · rintro ⟨s, hs, q, hq, hrun⟩
    refine ⟨q, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩
    rw [← Finset.mem_coe, h, LTS.mem_foldl_setImage]
    exact ⟨s, hs, hrun⟩

end Rewb
