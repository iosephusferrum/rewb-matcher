/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Main
public import Rewb.RegularExpression

/-!
# Matching a rewb of regular expressions

Main (Section 3) for a rewb `e₀(e)₁e₁\1e₂` whose subexpressions are regular expressions. It
simulates the automaton of `e₁` by Thompson's construction, and its arrays `Pre`, `Suf` and `Pre_α`
decide each membership with Mathlib's `rmatch` instead of by the simulations of Remark 4.

## Main definitions

* `Rewb.rmatch e₀ e e₁ e₂ w`: whether the rewb `e₀(e)₁e₁\1e₂` matches `w`.

## Main statements

* `Rewb.rmatch_eq_true_iff`: the correctness part of Theorem 5 for regular expressions, so that
  membership in the language of a rewb is decidable.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {Symbol : Type*} [DecidableEq Symbol] (e₀ e e₁ e₂ : RegularExpression Symbol)
  (w : List Symbol)

/-- Main (Section 3) for the rewb `e₀(e)₁e₁\1e₂`: whether it matches `w`. It simulates the
automaton of `e₁`, and the arrays `Pre`, `Suf` and `Pre_α` decide membership in the languages of
`e₀`, `e₂` and `e` with Mathlib's `rmatch`. -/
def rmatch : Bool :=
  main (Simulator.ofRegularExpression e₁) w (prefixOracle e₀.matches' w)
    (suffixOracle e₂.matches' w) (prefixOracle e.matches')

/-- The correctness part of Theorem 5 for regular expressions: `rmatch` returns true exactly when
`w` is in the language of the rewb `e₀(e)₁e₁\1e₂` (Definition 1). -/
theorem rmatch_eq_true_iff :
    rmatch e₀ e e₁ e₂ w = true ↔ w ∈ rewbLang e₀.matches' e.matches' e₁.matches' e₂.matches' :=
  main_eq_true_iff (accepts_ofRegularExpression e₁) (isPrefixOracle_prefixOracle _ _)
    (isSuffixOracle_suffixOracle _ _) fun _ => isPrefixOracle_prefixOracle _ _

/-- Membership in the language of a rewb is decided by `rmatch`. -/
instance : DecidablePred (· ∈ rewbLang e₀.matches' e.matches' e₁.matches' e₂.matches') :=
  fun w => decidable_of_iff _ (rmatch_eq_true_iff e₀ e e₁ e₂ w)

end Rewb
