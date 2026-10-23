/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Computability.Automata.EpsilonNA.OfRegularExpression
public import Mathlib.Data.Fintype.Sum
public import Rewb.EpsilonNA

/-!
# The simulator of a regular expression

Main simulates `N_e₁`, an NFA for the middle subexpression `e₁` (Section 3, after Lemma 6), which
the paper obtains by the standard construction (Section 2, after Definition 3). Here it is the
automaton `RegularExpression.toEpsilonNA` of Thompson's construction, from cslib.

* Instances that make Thompson's automata computable: finitely many states with decidable
  equality, and decidable transitions, initial states and accepting states.
* `Rewb.Simulator.ofRegularExpression r`: the simulator of the automaton of `r`;
  `accepts_ofRegularExpression` says that it accepts exactly `r.matches'`.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
* K. Thompson, *Regular expression search algorithm*, Communications of the ACM 11(6), 1968.
-/

@[expose] public section

namespace Cslib.Automata.εNA.FinAcc

variable {Symbol State S₁ S₂ : Type*}

/-! ### The automata of `0`, `1` and of a single symbol -/

instance (s : Unit) (μ : Option Symbol) (t : Unit) :
    Decidable ((zero : FinAcc Unit Symbol).Tr s μ t) :=
  inferInstanceAs (Decidable False)

instance : DecidablePred (· ∈ (zero : FinAcc Unit Symbol).start) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({()} : Set Unit)))

instance : DecidablePred (· ∈ (zero : FinAcc Unit Symbol).accept) :=
  fun s => inferInstanceAs (Decidable (s ∈ (∅ : Set Unit)))

instance (s : Unit) (μ : Option Symbol) (t : Unit) :
    Decidable ((epsilon : FinAcc Unit Symbol).Tr s μ t) :=
  inferInstanceAs (Decidable False)

instance : DecidablePred (· ∈ (epsilon : FinAcc Unit Symbol).start) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({()} : Set Unit)))

instance : DecidablePred (· ∈ (epsilon : FinAcc Unit Symbol).accept) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({()} : Set Unit)))

instance [DecidableEq Symbol] (x : Symbol) (s : Bool) (μ : Option Symbol) (t : Bool) :
    Decidable ((char x).Tr s μ t) :=
  inferInstanceAs (Decidable (s = false ∧ μ = some x ∧ t = true))

instance (x : Symbol) : DecidablePred (· ∈ (char x).start) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({false} : Set Bool)))

instance (x : Symbol) : DecidablePred (· ∈ (char x).accept) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({true} : Set Bool)))

/-! ### A single initial and a single accepting state -/

section toSingleStartAccept

variable {a : FinAcc State Symbol}

instance [DecidableEq State] : DecidablePred (· ∈ a.toSingleStartAccept.start) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({.inl false} : Set (Bool ⊕ State))))

instance [DecidableEq State] : DecidablePred (· ∈ a.toSingleStartAccept.accept) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({.inl true} : Set (Bool ⊕ State))))

instance [∀ s μ t, Decidable (a.Tr s μ t)] [DecidablePred (· ∈ a.start)]
    [DecidablePred (· ∈ a.accept)] : ∀ s μ t, Decidable (a.toSingleStartAccept.Tr s μ t)
  | .inr _, _, .inr _ => decidable_of_iff' _ toSingleStartAccept_tr_inr_inr
  | .inl false, none, .inr t => inferInstanceAs (Decidable (t ∈ a.start))
  | .inr s, none, .inl true => inferInstanceAs (Decidable (s ∈ a.accept))
  | .inl true, _, _ => isFalse toSingleStartAccept_not_tr_inl_true
  | _, _, .inl false => isFalse toSingleStartAccept_not_tr_inl_false
  | .inl false, some _, .inr _ => isFalse nofun
  | .inl false, none, .inl true => isFalse nofun
  | .inl false, some _, .inl true => isFalse nofun
  | .inr _, some _, .inl true => isFalse nofun

end toSingleStartAccept

/-! ### Sum and union -/

variable {a : FinAcc S₁ Symbol} {b : FinAcc S₂ Symbol}

instance [∀ s μ t, Decidable (a.Tr s μ t)] [∀ s μ t, Decidable (b.Tr s μ t)] :
    ∀ s μ t, Decidable ((sum a b).Tr s μ t)
  | .inl _, _, .inl _ => decidable_of_iff' _ LTS.unionSum_tr_inl_inl
  | .inr _, _, .inr _ => decidable_of_iff' _ LTS.unionSum_tr_inr_inr
  | .inl _, _, .inr _ => isFalse LTS.unionSum_not_tr_inl_inr
  | .inr _, _, .inl _ => isFalse LTS.unionSum_not_tr_inr_inl

instance [DecidablePred (· ∈ a.start)] [DecidablePred (· ∈ b.start)] :
    DecidablePred (· ∈ (sum a b).start)
  | .inl s => decidable_of_iff (s ∈ a.start) (by simp [sum])
  | .inr s => decidable_of_iff (s ∈ b.start) (by simp [sum])

instance [DecidablePred (· ∈ a.accept)] [DecidablePred (· ∈ b.accept)] :
    DecidablePred (· ∈ (sum a b).accept)
  | .inl s => decidable_of_iff (s ∈ a.accept) (by simp [sum])
  | .inr s => decidable_of_iff (s ∈ b.accept) (by simp [sum])

instance [DecidableEq S₁] [DecidableEq S₂] : DecidablePred (· ∈ (union a b).start) :=
  inferInstanceAs (DecidablePred (· ∈ (sum a b).toSingleStartAccept.start))

instance [DecidableEq S₁] [DecidableEq S₂] : DecidablePred (· ∈ (union a b).accept) :=
  inferInstanceAs (DecidablePred (· ∈ (sum a b).toSingleStartAccept.accept))

instance [∀ s μ t, Decidable (a.Tr s μ t)] [∀ s μ t, Decidable (b.Tr s μ t)]
    [DecidablePred (· ∈ a.start)] [DecidablePred (· ∈ b.start)]
    [DecidablePred (· ∈ a.accept)] [DecidablePred (· ∈ b.accept)] :
    ∀ s μ t, Decidable ((union a b).Tr s μ t) :=
  inferInstanceAs (∀ s μ t, Decidable ((sum a b).toSingleStartAccept.Tr s μ t))

/-! ### Concatenation and star -/

instance [∀ s μ t, Decidable (a.Tr s μ t)] [∀ s μ t, Decidable (b.Tr s μ t)]
    [DecidablePred (· ∈ a.accept)] [DecidablePred (· ∈ b.start)] :
    ∀ s μ t, Decidable ((concat a b).Tr s μ t)
  | .inl s, μ, .inl t =>
    decidable_of_iff (a.Tr s μ t) ⟨ConcatTr.left, fun h => by cases h; assumption⟩
  | .inr s, μ, .inr t =>
    decidable_of_iff (b.Tr s μ t) ⟨ConcatTr.right, fun h => by cases h; assumption⟩
  | .inl s, none, .inr t =>
    decidable_of_iff (s ∈ a.accept ∧ t ∈ b.start)
      ⟨fun h => ConcatTr.bridge h.1 h.2, fun h => by cases h; constructor <;> assumption⟩
  | .inl _, some _, .inr _ => isFalse nofun
  | .inr _, _, .inl _ => isFalse nofun

instance [DecidablePred (· ∈ a.start)] : DecidablePred (· ∈ (concat a b).start)
  | .inl s => decidable_of_iff (s ∈ a.start) (by simp [concat])
  | .inr _ => isFalse (by simp [concat])

instance [DecidablePred (· ∈ b.accept)] : DecidablePred (· ∈ (concat a b).accept)
  | .inl _ => isFalse (by simp [concat])
  | .inr s => decidable_of_iff (s ∈ b.accept) (by simp [concat])

instance [∀ s μ t, Decidable (a.Tr s μ t)] [DecidablePred (· ∈ a.start)]
    [DecidablePred (· ∈ a.accept)] : ∀ s μ t, Decidable ((star a).Tr s μ t)
  | .inr s, μ, .inr t =>
    decidable_of_iff (a.Tr s μ t) ⟨StarTr.inner, fun h => by cases h; assumption⟩
  | .inl (), none, .inr t =>
    decidable_of_iff (t ∈ a.start) ⟨StarTr.enter, fun h => by cases h; assumption⟩
  | .inr s, none, .inl () =>
    decidable_of_iff (s ∈ a.accept) ⟨StarTr.exit, fun h => by cases h; assumption⟩
  | .inl (), some _, .inr _ => isFalse nofun
  | .inr _, some _, .inl () => isFalse nofun
  | .inl (), _, .inl () => isFalse nofun

instance [DecidableEq S₁] : DecidablePred (· ∈ (star a).start) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({.inl ()} : Set (Unit ⊕ S₁))))

instance [DecidableEq S₁] : DecidablePred (· ∈ (star a).accept) :=
  fun s => inferInstanceAs (Decidable (s ∈ ({.inl ()} : Set (Unit ⊕ S₁))))

end Cslib.Automata.εNA.FinAcc

namespace RegularExpression

open Cslib.Automata εNA

variable {α : Type*}

/-- The states of the automaton of a regular expression, listed. -/
instance instFintypeState : (r : RegularExpression α) → Fintype r.State
  | zero => inferInstanceAs (Fintype Unit)
  | epsilon => inferInstanceAs (Fintype Unit)
  | char _ => inferInstanceAs (Fintype Bool)
  | plus P Q =>
    letI := instFintypeState P
    letI := instFintypeState Q
    inferInstanceAs (Fintype (Bool ⊕ (P.State ⊕ Q.State)))
  | comp P Q =>
    letI := instFintypeState P
    letI := instFintypeState Q
    inferInstanceAs (Fintype (P.State ⊕ Q.State))
  | star P =>
    letI := instFintypeState P
    inferInstanceAs (Fintype (Unit ⊕ P.State))

instance instDecidableEqState : (r : RegularExpression α) → DecidableEq r.State
  | zero => inferInstanceAs (DecidableEq Unit)
  | epsilon => inferInstanceAs (DecidableEq Unit)
  | char _ => inferInstanceAs (DecidableEq Bool)
  | plus P Q =>
    letI := instDecidableEqState P
    letI := instDecidableEqState Q
    inferInstanceAs (DecidableEq (Bool ⊕ (P.State ⊕ Q.State)))
  | comp P Q =>
    letI := instDecidableEqState P
    letI := instDecidableEqState Q
    inferInstanceAs (DecidableEq (P.State ⊕ Q.State))
  | star P =>
    letI := instDecidableEqState P
    inferInstanceAs (DecidableEq (Unit ⊕ P.State))

instance instDecidablePredMemStart :
    (r : RegularExpression α) → DecidablePred (· ∈ r.toEpsilonNA.start)
  | zero => inferInstanceAs (DecidablePred (· ∈ (FinAcc.zero : FinAcc Unit α).start))
  | epsilon => inferInstanceAs (DecidablePred (· ∈ (FinAcc.epsilon : FinAcc Unit α).start))
  | char a => inferInstanceAs (DecidablePred (· ∈ (FinAcc.char a).start))
  | plus P Q => inferInstanceAs (DecidablePred (· ∈ (P.toEpsilonNA.union Q.toEpsilonNA).start))
  | comp P Q =>
    letI := instDecidablePredMemStart P
    inferInstanceAs (DecidablePred (· ∈ (P.toEpsilonNA.concat Q.toEpsilonNA).start))
  | star P => inferInstanceAs (DecidablePred (· ∈ P.toEpsilonNA.star.start))

instance instDecidablePredMemAccept :
    (r : RegularExpression α) → DecidablePred (· ∈ r.toEpsilonNA.accept)
  | zero => inferInstanceAs (DecidablePred (· ∈ (FinAcc.zero : FinAcc Unit α).accept))
  | epsilon => inferInstanceAs (DecidablePred (· ∈ (FinAcc.epsilon : FinAcc Unit α).accept))
  | char a => inferInstanceAs (DecidablePred (· ∈ (FinAcc.char a).accept))
  | plus P Q => inferInstanceAs (DecidablePred (· ∈ (P.toEpsilonNA.union Q.toEpsilonNA).accept))
  | comp P Q =>
    letI := instDecidablePredMemAccept Q
    inferInstanceAs (DecidablePred (· ∈ (P.toEpsilonNA.concat Q.toEpsilonNA).accept))
  | star P => inferInstanceAs (DecidablePred (· ∈ P.toEpsilonNA.star.accept))

instance instDecidableTr [DecidableEq α] :
    (r : RegularExpression α) → ∀ s μ t, Decidable (r.toEpsilonNA.Tr s μ t)
  | zero => inferInstanceAs (∀ s μ t, Decidable ((FinAcc.zero : FinAcc Unit α).Tr s μ t))
  | epsilon => inferInstanceAs (∀ s μ t, Decidable ((FinAcc.epsilon : FinAcc Unit α).Tr s μ t))
  | char a => inferInstanceAs (∀ s μ t, Decidable ((FinAcc.char a).Tr s μ t))
  | plus P Q =>
    letI := instDecidableTr P
    letI := instDecidableTr Q
    inferInstanceAs (∀ s μ t, Decidable ((P.toEpsilonNA.union Q.toEpsilonNA).Tr s μ t))
  | comp P Q =>
    letI := instDecidableTr P
    letI := instDecidableTr Q
    inferInstanceAs (∀ s μ t, Decidable ((P.toEpsilonNA.concat Q.toEpsilonNA).Tr s μ t))
  | star P =>
    letI := instDecidableTr P
    inferInstanceAs (∀ s μ t, Decidable (P.toEpsilonNA.star.Tr s μ t))

end RegularExpression

namespace Rewb

variable {α : Type*} [DecidableEq α]

/-- The simulator of `N_e` for a regular expression `e` (Section 2, after Definition 3): that of
the automaton of `e` by Thompson's construction. -/
def Simulator.ofRegularExpression (r : RegularExpression α) : Simulator r.State α :=
  Simulator.ofEpsilonNA r.toEpsilonNA

/-- The simulator of a regular expression accepts exactly its language. -/
@[simp]
theorem accepts_ofRegularExpression (r : RegularExpression α) :
    (Simulator.ofRegularExpression r).accepts = r.matches' := by
  rw [Simulator.ofRegularExpression, accepts_ofEpsilonNA, RegularExpression.language_toEpsilonNA]

end Rewb
