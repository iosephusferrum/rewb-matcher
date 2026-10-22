/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Match3A
public import Rewb.Match3B

/-!
# Main: the matching algorithm

The algorithm Main of Section 3 decides whether the rewb `e₀(e)₁e₁\1e₂` matches the input word
`w`. If `e` matches `ε`, it checks whether `e₀ e₁ e₂` matches `w`. Then it runs `Match(α)` on every
right-maximal repeat `α` of `w`, which is Match3A or Match3B (Section 3.2). Lemma 6 states what
Match finds, and Theorem 5 that Main is correct: a match with a nonempty backreferenced word `β`
is found by `Match(→β)`, where `→β` is the right-maximal repeat that `β` extends to.

## Main definitions

* `Rewb.matchEmpty`: whether `e₀ e₁ e₂` matches `w`.
* `Rewb.matchRepeat`: `Match(α)`, written `Match(α, Idx_α)` in the paper.
* `Rewb.main`: Main.

## Main statements

* `Rewb.matchEmpty_eq_true_iff`: the case of the empty backreferenced word.
* `Rewb.exists_mem_rewbLangWith_of_matchRepeat_eq_true` and
  `Rewb.matchRepeat_eq_true_of_isExtendablePrefix`: Lemma 6, the correctness of Match.
* `Rewb.main_eq_true_iff`: Theorem 5, the correctness of Main.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Whether `e₀ e₁ e₂` matches `w`, which Main checks when `e` matches `ε` (Section 3, before
Lemma 6): for some position `j`, `Suf` holds after `j` and the simulation of `e₁` that injects
`cl_ε(q₀)` at every position `i` with `Pre[i]` accepts at `j`. The paper runs the automaton of
`e₀ e₁ e₂` instead. -/
def matchEmpty (w : List Symbol) (pre suf : ℕ → Bool) : Bool :=
  (List.range (w.length + 1)).any fun j =>
    let S := M.evalInject M.start (fun p => pre (p + 1)) (if pre 0 then M.start else ∅) 0
      (w.take j)
    suf j && decide (∃ s ∈ S, s ∈ M.accept)

/-- `Match(α)` (Section 3.2): Match3A or Match3B. `idx` lists the occurrences of `α` in `w` (the
paper's `Idx_α`) and `preα` is its array `Pre_α`. -/
def matchRepeat (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : Bool :=
  match3A M w α idx pre suf preα || match3B M α idx pre suf preα

/-- Main (Section 3): `e` matches `ε` and `e₀ e₁ e₂` matches `w`, or `Match(α)` returns true for
some right-maximal repeat `α` of `w`. `M` simulates `e₁`, `pre` and `suf` are the arrays `Pre` and
`Suf`, and `preα α` is the array `Pre_α` of each `α`; in particular `preα [] 0` tells whether `e`
matches `ε`. The right-maximal repeats and their occurrences are enumerated directly
(`List.rightMaximalRepeats`, `List.occurrences`) instead of by EnumRM (Appendix A). -/
def main [DecidableEq Symbol] (w : List Symbol) (pre suf : ℕ → Bool)
    (preα : List Symbol → ℕ → Bool) : Bool :=
  (preα [] 0 && matchEmpty M w pre suf) ||
    w.rightMaximalRepeats.any fun α => matchRepeat M w α (α.occurrences w) pre suf (preα α)

variable {M}

/-- The case of the empty backreferenced word: `matchEmpty` returns true exactly when
`r_ε = e₀ e₁ e₂` matches `w`. -/
theorem matchEmpty_eq_true_iff {L₀ L₁ L₂ : Language Symbol} {w : List Symbol}
    {pre suf : ℕ → Bool} (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre)
    (hsuf : IsSuffixOracle L₂ w suf) :
    matchEmpty M w pre suf = true ↔ w ∈ rewbLangWith L₀ L₁ L₂ [] := by
  -- The simulation set at `j` holds what `cl_ε(q₀)` reaches between some `i ≤ j` with `Pre[i]`
  -- and `j`.
  have hS : ∀ j ≤ w.length, ∀ s, s ∈ M.evalInject M.start (fun p => pre (p + 1))
      (if pre 0 then M.start else ∅) 0 (w.take j) ↔
        ∃ i ≤ j, pre i = true ∧ s ∈ M.evalFrom M.start ((w.drop i).take (j - i)) := by
    intro j hj s
    rw [Simulator.mem_evalInject]
    constructor
    · rintro (hs | ⟨k, hk, hpk, hs⟩)
      · by_cases h0 : pre 0 = true
        · rw [ite_eq_left h0] at hs
          exact ⟨0, Nat.zero_le _, h0, by simpa using hs⟩
        · rw [ite_eq_right h0, Simulator.evalFrom_empty] at hs
          exact absurd hs (Finset.notMem_empty s)
      · rw [List.length_take] at hk
        refine ⟨k + 1, by omega, by simpa using hpk, ?_⟩
        rwa [List.drop_take] at hs
    · rintro ⟨i, hi, hpi, hs⟩
      rcases i with _ | k
      · exact .inl (by rw [ite_eq_left hpi]; simpa using hs)
      · refine .inr ⟨k, by rw [List.length_take]; omega, by simpa using hpi, ?_⟩
        rwa [List.drop_take]
  rw [matchEmpty, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hsufj, s, hs, hacc⟩ := h
    obtain ⟨i, hi, hpi, hs⟩ := (hS j (by omega) s).mp hs
    refine mem_rewbLangWith.mpr ⟨w.take i, (w.drop i).take (j - i), w.drop j,
      (hpre i (by omega)).mp hpi, ?_, (hsuf j (by omega)).mp hsufj, ?_⟩
    · rw [← hM]
      exact Simulator.mem_accepts.mpr ⟨s, hs, hacc⟩
    · conv_lhs => rw [← List.take_append_drop i w, ← List.take_append_drop (j - i) (w.drop i),
        List.drop_drop, Nat.add_sub_of_le hi]
      simp
  · intro hw
    obtain ⟨w₀, w₁, w₂, h₀, h₁, h₂, rfl⟩ := mem_rewbLangWith.mp hw
    rw [← hM] at h₁
    obtain ⟨s, hs, hacc⟩ := Simulator.mem_accepts.mp h₁
    refine ⟨w₀.length + w₁.length, List.mem_range.mpr (by simp; omega), ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨(hsuf _ (by simp)).mpr (by simpa using h₂), s,
      (hS _ (by simp) s).mpr ⟨w₀.length, by omega, (hpre _ (by simp)).mpr
        (by simpa using h₀), ?_⟩, hacc⟩
    simpa using hs

/-- Lemma 6, first part, the soundness of Match: if `Match(α)` returns true, then `e` matches a
nonempty prefix `β` of `α` and `r_β = e₀ β e₁ β e₂` matches `w`. -/
theorem exists_mem_rewbLangWith_of_matchRepeat_eq_true [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α : List Symbol} {idx : List ℕ} {pre suf preα : ℕ → Bool}
    (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : IsPrefixOracle L α preα) (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (h : matchRepeat M w α idx pre suf preα = true) :
    ∃ β, β <+: α ∧ β ≠ [] ∧ β ∈ L ∧ w ∈ rewbLangWith L₀ L₁ L₂ β := by
  rw [matchRepeat, Bool.or_eq_true] at h
  rcases h with h | h
  · exact exists_mem_rewbLangWith_of_match3A_eq_true hM hpre hsuf hpreα hidx hα h
  · exact exists_mem_rewbLangWith_of_match3B_eq_true hM hpre hsuf hpreα hidx hα h

/-- Lemma 6, second part, the completeness of Match for extendable prefixes: `Match(α)` returns
true for every extendable prefix `β` of `α` that `e` matches and for which `r_β = e₀ β e₁ β e₂`
matches `w`. Match3A finds the matches whose two occurrences of `β` are `α`-separable, Match3B the
others. -/
theorem matchRepeat_eq_true_of_isExtendablePrefix [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α β : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre)
    (hsuf : IsSuffixOracle L₂ w suf) (hpreα : IsPrefixOracle L α preα)
    (hidx : idx = α.occurrences w) (hβ : β.IsExtendablePrefix α w) (hβL : β ∈ L)
    (hw : w ∈ rewbLangWith L₀ L₁ L₂ β) :
    matchRepeat M w α idx pre suf preα = true := by
  have hα : α ≠ [] := hβ.isRightMaximalRepeat.1
  obtain ⟨p₁, p₂, hp₁, hp₂, hle, h₀, h₁, h₂⟩ := mem_rewbLangWith_iff_occursAt.mp hw
  rw [matchRepeat, Bool.or_eq_true]
  by_cases hsep : p₁ + α.length ≤ p₂
  · exact .inl (match3A_eq_true_of_isExtendablePrefix hM hpre hsuf hpreα hidx hα hβ hβL hp₁ hp₂
      hsep h₀ h₁ h₂)
  · exact .inr (match3B_eq_true_of_isExtendablePrefix hM hpre hsuf hpreα hidx hα hβ hβL hp₁ hp₂
      hle (by omega) h₀ h₁ h₂)

/-- Theorem 5, the correctness of Main: Main returns true exactly when the rewb `e₀(e)₁e₁\1e₂`
matches `w`. A match with an empty backreferenced word is found by `matchEmpty`; one with a
nonempty backreferenced word `β`, which is then a repeat of `w`, is found by `Match(→β)` (Lemma 6),
where `→β` is the right-maximal repeat that `β` extends to. -/
theorem main_eq_true_iff [DecidableEq Symbol] {L₀ L L₁ L₂ : Language Symbol} {w : List Symbol}
    {pre suf : ℕ → Bool} {preα : List Symbol → ℕ → Bool} (hM : M.accepts = L₁)
    (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : ∀ α, IsPrefixOracle L α (preα α)) :
    main M w pre suf preα = true ↔ w ∈ rewbLang L₀ L L₁ L₂ := by
  have hε : preα [] 0 = true ↔ [] ∈ L := hpreα [] 0 le_rfl
  rw [main, Bool.or_eq_true, Bool.and_eq_true, hε, matchEmpty_eq_true_iff hM hpre hsuf,
    List.any_eq_true, mem_rewbLang_iff_exists_mem_rewbLangWith]
  constructor
  · rintro (⟨hL, hw⟩ | ⟨α, hα, h⟩)
    · exact ⟨[], hL, hw⟩
    · obtain ⟨β, -, -, hβL, hw⟩ := exists_mem_rewbLangWith_of_matchRepeat_eq_true hM hpre hsuf
        (hpreα α) rfl (List.mem_rightMaximalRepeats.mp hα).1 h
      exact ⟨β, hβL, hw⟩
  · rintro ⟨β, hβL, hw⟩
    by_cases hβ : β = []
    · subst hβ
      exact .inl ⟨hβL, hw⟩
    · -- `β` occurs twice in `w`, so it is a repeat, which extends to a right-maximal repeat.
      obtain ⟨p₁, p₂, hp₁, hp₂, hle, -⟩ := mem_rewbLangWith_iff_occursAt.mp hw
      have hrep : β.IsRepeat w :=
        ⟨hβ, p₁, p₂, by have := List.length_pos_iff.mpr hβ; omega, hp₁, hp₂⟩
      obtain ⟨α, hβα⟩ := hrep.exists_isExtendablePrefix
      exact .inr ⟨α, List.mem_rightMaximalRepeats.mpr hβα.isRightMaximalRepeat,
        matchRepeat_eq_true_of_isExtendablePrefix hM hpre hsuf (hpreα α) rfl hβα hβL hw⟩

end Rewb
