/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Injection

/-!
# Match1: the right-maximal repeat itself

Algorithm 1 (`Match1(α)`, Section 3.1.1) decides whether `r_α = e₀ α e₁ α e₂` matches the input
word `w`, for a word `α` that `e` matches. It simulates the automaton of `e₁` along `w`, injects
the initial simulation set right after each occurrence of `α` that `e₀` can precede, and tests
acceptance right before each occurrence of `α` that `e₂` can follow.

## Main definitions

* `Rewb.match1`: Algorithm 1.

## Main statements

* `Rewb.mem_match1Set`: Proposition 9, the simulation set when line 8 is reached.
* `Rewb.match1_eq_true_iff`: Lemma 10, the correctness of Match1, for every nonempty `α` whose
  occurrences do not overlap.

The paper states Lemma 10 for nonoverlapping right-maximal repeats; right-maximality is not
needed. Remark 11 claims that Match1 is correct for every repeat; `RewbTests/Match1.lean` gives
an overlapping repeat for which it is not.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- The loop of Algorithm 1, lines 3 to 10, over the occurrences of `α` still to visit, with the
variables `iprev`, `S` and `ique`.

Positions are 0-based, so an occurrence at `p` is the paper's position `p + 1`, and the paper's
inner loop over `i ∈ [iprev, inext − 1]` reads our positions `iprev` to `inext - 1`. `ique` holds
the same number as in the paper: how many symbols have been read when the injection is due.
`iprev` starts at `0` instead of `⊥`; it is only read once `ique` is set. -/
def match1Loop (w α : List Symbol) (pre suf : ℕ → Bool) :
    ℕ → Finset State → Option ℕ → List ℕ → Bool
  | _, _, _, [] => false
  | _, S, none, inext :: idx =>
    match1Loop w α pre suf inext S (if pre inext then some (inext + α.length) else none) idx
  | iprev, S, some q, inext :: idx =>
    let S := M.evalInject M.start (fun p => decide (p + 1 = q)) S iprev
      ((w.drop iprev).take (inext - iprev))
    (decide (∃ s ∈ S, s ∈ M.accept) && suf (inext + α.length)) ||
      match1Loop w α pre suf inext S (if pre inext then some (inext + α.length) else some q) idx

/-- Algorithm 1, `Match1(α)`. `M` simulates `e₁`, `idx` lists the occurrences of `α` in `w` in
increasing order (the paper's `Idx_α`), and `pre` and `suf` are the arrays `Pre` and `Suf`.
Line 2 asks whether `e` matches `α`: that is the last entry of `Pre_α`, `preα α.length`. -/
def match1 (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : Bool :=
  preα α.length && match1Loop M w α pre suf 0 ∅ none idx

/-! ### Correctness -/

/-- The positions after which Algorithm 1 injects when no injection is lost: the last symbol of
each occurrence `p` of `α` with `Pre[p]` (Algorithm 1, line 10). -/
def match1Mark (α : List Symbol) (idx : List ℕ) (pre : ℕ → Bool) (k : ℕ) : Bool :=
  decide (∃ p ∈ idx, pre p = true ∧ k + 1 = p + α.length)

/-- The simulation set at line 8 of Algorithm 1 when `inext = p`, if no injection is lost
(Proposition 9). -/
def match1Set (w α : List Symbol) (idx : List ℕ) (pre : ℕ → Bool) (p : ℕ) : Finset State :=
  M.evalInject M.start (match1Mark α idx pre) ∅ 0 (w.take p)

variable {M}

/-- Proposition 9: the states of `match1Set` at `p` are those that `cl_ε(q₀)` reaches by reading
`w` from the end of an occurrence `p'` of `α` with `Pre[p']` up to position `p`. -/
theorem mem_match1Set {w α : List Symbol} {idx : List ℕ} {pre : ℕ → Bool} {p : ℕ} {s : State}
    (hα : α ≠ []) (hp : p ≤ w.length) :
    s ∈ match1Set M w α idx pre p ↔
      ∃ p' ∈ idx, pre p' = true ∧ p' + α.length ≤ p ∧
        s ∈ M.evalFrom M.start ((w.drop (p' + α.length)).take (p - (p' + α.length))) := by
  have hα' := List.length_pos_iff.mpr hα
  simp only [match1Set, Simulator.mem_evalInject, Simulator.evalFrom_empty, Finset.notMem_empty,
    false_or, match1Mark, decide_eq_true_eq, Nat.zero_add, List.length_take, List.drop_take]
  constructor
  · rintro ⟨k, hk, ⟨p', hp', hpre, hkp⟩, hs⟩
    refine ⟨p', hp', hpre, by omega, ?_⟩
    rwa [← hkp]
  · rintro ⟨p', hp', hpre, hle, hs⟩
    refine ⟨p' + α.length - 1, by omega, ⟨p', hp', hpre, by omega⟩, ?_⟩
    rwa [show p' + α.length - 1 + 1 = p' + α.length by omega]

/-- The loop of Algorithm 1 finds a match exactly at the occurrences `p` where `match1Set` at `p`
passes the acceptance test and `Suf` holds, as long as the occurrences of `α` don't overlap. The
hypotheses describe the variables once the occurrences in `done` have been visited. -/
theorem match1Loop_eq_true_iff {w α : List Symbol} {pre suf : ℕ → Bool} {idx : List ℕ}
    (hα : α ≠ []) (hsorted : idx.Pairwise (· < ·)) (hlen : ∀ p ∈ idx, p + α.length ≤ w.length)
    (hno : ∀ p ∈ idx, ∀ p' ∈ idx, p < p' → p + α.length ≤ p') :
    ∀ {rest done : List ℕ} {iprev : ℕ} {S : Finset State} {ique : Option ℕ}, done ++ rest = idx →
      (ique = none → S = ∅ ∧ ∀ p ∈ done, pre p = false) →
      (∀ q, ique = some q → iprev ∈ done ∧ (∀ p ∈ done, p ≤ iprev) ∧
        S = match1Set M w α idx pre iprev ∧
        (pre iprev = true ∧ q = iprev + α.length ∨ pre iprev = false ∧ q ≤ iprev)) →
      (match1Loop M w α pre suf iprev S ique rest = true ↔
        ∃ p ∈ rest, (∃ s ∈ match1Set M w α idx pre p, s ∈ M.accept) ∧
          suf (p + α.length) = true) := by
  have hα' := List.length_pos_iff.mpr hα
  intro rest
  induction rest with
  | nil => intros; simp [match1Loop]
  | cons inext rest ih =>
    intro done iprev S ique hsplit hnone hsome
    have hsorted' : (done ++ inext :: rest).Pairwise (· < ·) := by rw [hsplit]; exact hsorted
    rw [List.pairwise_append, List.pairwise_cons] at hsorted'
    obtain ⟨-, ⟨hrest, -⟩, hcross⟩ := hsorted'
    have hdone : ∀ p ∈ done, p < inext := fun p hp => hcross p hp inext (by simp)
    have hmem : ∀ p, p ∈ idx ↔ p ∈ done ∨ p = inext ∨ p ∈ rest := by
      intro p; rw [← hsplit]; simp
    have hinext : inext ∈ idx := (hmem inext).mpr (by simp)
    have hbelow : ∀ p ∈ idx, p < inext → p ∈ done := by
      intro p hp hlt
      rcases (hmem p).mp hp with h | rfl | h
      · exact h
      · omega
      · have := hrest p h; omega
    have hsplit' : done ++ [inext] ++ rest = idx := by rw [← hsplit]; simp
    have hle_done : ∀ p ∈ done ++ [inext], p ≤ inext := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (hdone p hp).le
      · simp at hp; omega
    -- If no occurrence before `inext` has `Pre`, nothing has been injected yet.
    have hempty : (∀ p ∈ done, pre p = false) → match1Set M w α idx pre inext = ∅ := by
      intro hpre
      have hle : inext ≤ w.length := by have := hlen inext hinext; omega
      ext s
      simp only [Finset.notMem_empty, iff_false]
      rw [mem_match1Set hα hle]
      rintro ⟨p', hp', hpre', hle, -⟩
      rw [hpre p' (hbelow p' hp' (by omega))] at hpre'
      exact Bool.false_ne_true hpre'
    cases ique with
    | none =>
      obtain ⟨rfl, hpre⟩ := hnone rfl
      simp only [match1Loop]
      rw [ih hsplit' ?_ ?_]
      · simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hempty hpre]
        simp
      · intro h
        refine ⟨rfl, fun p hp => ?_⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact hpre p hp
        · obtain rfl := List.mem_singleton.mp hp
          split at h <;> simp_all
      · intro q h
        split at h
        · obtain rfl := Option.some.inj h
          exact ⟨by simp, hle_done, (hempty hpre).symm, .inl ⟨‹_›, rfl⟩⟩
        · simp at h
    | some q =>
      obtain ⟨hiprev, hmax, hS, hq⟩ := hsome q rfl
      have hlt : iprev < inext := hdone iprev hiprev
      have hiprev_idx : iprev ∈ idx := (hmem iprev).mpr (.inl hiprev)
      -- Lines 5 to 7 compute `match1Set` at `inext` (Proposition 9).
      have hS' : M.evalInject M.start (fun p => decide (p + 1 = q)) S iprev
          ((w.drop iprev).take (inext - iprev)) = match1Set M w α idx pre inext := by
        have htake : w.take inext = w.take iprev ++ (w.drop iprev).take (inext - iprev) := by
          rw [← List.take_add, Nat.add_sub_of_le hlt.le]
        have hlen' : (w.take iprev).length = iprev := by
          have := hlen iprev hiprev_idx
          rw [List.length_take]; omega
        rw [hS, match1Set, match1Set, htake, Simulator.evalInject_append, hlen', Nat.zero_add]
        refine Simulator.evalInject_congr fun k hk => ?_
        rw [List.length_take, List.length_drop] at hk
        simp only [match1Mark]
        rw [decide_eq_decide]
        constructor
        · intro hkq
          rcases hq with ⟨hpre, rfl⟩ | ⟨-, hq⟩
          · exact ⟨iprev, hiprev_idx, hpre, hkq⟩
          · omega
        · rintro ⟨p, hp, hpre, hkp⟩
          have hp_done := hbelow p hp (by omega)
          rcases Nat.lt_or_eq_of_le (hmax p hp_done) with hp_lt | rfl
          · have := hno p hp iprev hiprev_idx hp_lt; omega
          · rcases hq with ⟨-, rfl⟩ | ⟨hpre', -⟩
            · exact hkp
            · rw [hpre'] at hpre; exact absurd hpre Bool.false_ne_true
      simp only [match1Loop, hS', Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih hsplit' ?_ ?_]
      · simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      · intro h; split at h <;> simp at h
      · intro q' h
        refine ⟨by simp, hle_done, rfl, ?_⟩
        split at h
        · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
        · refine .inr ⟨by simpa using ‹¬pre inext = true›, ?_⟩
          obtain rfl := Option.some.inj h
          rcases hq with ⟨-, rfl⟩ | ⟨-, hq⟩
          · exact hno iprev hiprev_idx inext hinext hlt
          · omega

/-- Lemma 10, the correctness of Match1: for a nonempty word `α` whose occurrences in `w` do not
overlap, Match1 returns true exactly when `e` matches `α` and `r_α = e₀ α e₁ α e₂` matches `w`.
The paper assumes `α` to be a nonoverlapping right-maximal repeat. -/
theorem match1_eq_true_iff [DecidableEq Symbol] {L₀ L L₁ L₂ : Language Symbol}
    {w α : List Symbol} {idx : List ℕ} {pre suf preα : ℕ → Bool} (hM : M.accepts = L₁)
    (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : IsPrefixOracle L α preα) (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (hno : ∀ i j, α.OccursAt w i → α.OccursAt w j → i < j → i + α.length ≤ j) :
    match1 M w α idx pre suf preα = true ↔ α ∈ L ∧ w ∈ rewbLangWith L₀ L₁ L₂ α := by
  have hmem : ∀ p, p ∈ idx ↔ α.OccursAt w p := fun p => by
    rw [hidx]; exact List.mem_occurrences_of_ne_nil hα
  have hlen : ∀ p ∈ idx, p + α.length ≤ w.length := fun p hp =>
    ((hmem p).mp hp).add_length_le hα
  have hloop := match1Loop_eq_true_iff (M := M) (pre := pre) (suf := suf) hα
    (by rw [hidx]; exact List.pairwise_lt_occurrences α w) hlen
    (fun p hp p' hp' h => hno p p' ((hmem p).mp hp) ((hmem p').mp hp') h)
    (rest := idx) (done := []) (iprev := 0) (S := ∅) (ique := none) rfl
    (fun _ => ⟨rfl, by simp⟩) (by simp)
  rw [match1, Bool.and_eq_true, hloop, hpreα α.length le_rfl, List.take_length,
    mem_rewbLangWith_iff_occursAt]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨p, hp, ⟨s, hs, hacc⟩, hsufp⟩
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    rw [mem_match1Set hα hpw] at hs
    obtain ⟨p', hp', hprep', hle, hs⟩ := hs
    refine ⟨p', p, (hmem p').mp hp', (hmem p).mp hp, hle,
      (hpre p' (by have := hlen p' hp'; omega)).mp hprep', ?_,
      (hsuf (p + α.length) (hlen p hp)).mp hsufp⟩
    rw [← hM]
    exact Simulator.mem_accepts.mpr ⟨s, hs, hacc⟩
  · rintro ⟨p', p, hp', hp, hle, h₀, h₁, h₂⟩
    rw [← hmem] at hp hp'
    rw [← hM, Simulator.mem_accepts] at h₁
    obtain ⟨s, hs, hacc⟩ := h₁
    refine ⟨p, hp, ⟨s, ?_, hacc⟩, (hsuf (p + α.length) (hlen p hp)).mpr h₂⟩
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    rw [mem_match1Set hα hpw]
    exact ⟨p', hp', (hpre p' (by have := hlen p' hp'; omega)).mpr h₀, hle, hs⟩

end Rewb
