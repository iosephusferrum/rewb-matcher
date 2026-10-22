/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Cslib.Foundations.Data.List.ExtendablePrefix
public import Rewb.Intmed
public import Rewb.Match1

/-!
# Match2: the extendable prefixes of the repeat

Algorithm 2 (`Match2(α)`, Section 3.1.2) extends Match1 from `α` to its prefixes. It simulates the
automaton of `e₁` along the input word from every state at once (simulation with summarization),
injecting each state into its own simulation right after each occurrence of `α` that `e₀` can
precede. At each occurrence of `α` it runs Intmed along the occurrence and joins the two results:
a run that Intmed brings to a state `t`, continued by the simulation started from `t`.

## Main definitions

* `Rewb.match2`: Algorithm 2.

## Main statements

* `Rewb.mem_match2Set`: Proposition 13, the simulation with summarization when line 9 is reached.
* `Rewb.match2_eq_true_iff`: what Match2 checks, by Proposition 13 and Lemma 14.
* `Rewb.exists_mem_rewbLangWith_of_match2_eq_true` and `Rewb.match2_eq_true_of_isExtendablePrefix`:
  Lemma 15, the correctness of Match2, for every nonempty `α` whose occurrences do not overlap.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- The loop of Algorithm 2, lines 3 to 11, over the occurrences of `α` still to visit, with the
variables `iprev`, `S` and `ique`. `S t` is the simulation set of the run started from `t`, the
paper's `S[l]` for `t = q_l`. Lines 4 to 7 are those of Algorithm 1 with the simulation with
summarization, line 8 runs Intmed from the start of the occurrence, and line 9 asks whether a state
`t` that Intmed reaches has an accepting state in `S t`. As in the paper, lines 8 and 9 only run
once `ique` is set. -/
def match2Loop (w α : List Symbol) (pre suf preα : ℕ → Bool) :
    ℕ → (State → Finset State) → Option ℕ → List ℕ → Bool
  | _, _, _, [] => false
  | _, S, none, inext :: idx =>
    match2Loop w α pre suf preα inext S (if pre inext then some (inext + α.length) else none) idx
  | iprev, S, some q, inext :: idx =>
    let S := M.evalInjectSum (fun p => decide (p + 1 = q)) S iprev
      ((w.drop iprev).take (inext - iprev))
    let T := intmed M α inext 1 preα suf
    decide (∃ t ∈ T, ∃ s ∈ S t, s ∈ M.accept) ||
      match2Loop w α pre suf preα inext S
        (if pre inext then some (inext + α.length) else some q) idx

/-- Algorithm 2, `Match2(α)`. `M` simulates `e₁`, `idx` lists the occurrences of `α` in `w` in
increasing order (the paper's `Idx_α`), and `pre`, `suf` and `preα` are the arrays `Pre`, `Suf`
and `Pre_α` (line 2). -/
def match2 (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : Bool :=
  match2Loop M w α pre suf preα 0 (fun _ => ∅) none idx

/-! ### Correctness -/

/-- The simulation with summarization at line 9 of Algorithm 2 when `inext = p`, if no injection
is lost (Proposition 13): component `t` injects `{t}` after the last symbol of each occurrence `p'`
of `α` with `Pre[p']`. -/
def match2Set (w α : List Symbol) (idx : List ℕ) (pre : ℕ → Bool) (p : ℕ) (t : State) :
    Finset State :=
  M.evalInject {t} (match1Mark α idx pre) ∅ 0 (w.take p)

variable {M}

/-- Proposition 13: the states of component `t` of `match2Set` at `p` are those that `t` reaches
by reading `w` from the end of an occurrence `p'` of `α` with `Pre[p']` up to position `p`. -/
theorem mem_match2Set {w α : List Symbol} {idx : List ℕ} {pre : ℕ → Bool} {p : ℕ} {t s : State}
    (hα : α ≠ []) (hp : p ≤ w.length) :
    s ∈ match2Set M w α idx pre p t ↔
      ∃ p' ∈ idx, pre p' = true ∧ p' + α.length ≤ p ∧
        s ∈ M.evalFrom {t} ((w.drop (p' + α.length)).take (p - (p' + α.length))) :=
  mem_evalInject_match1Mark hα hp

/-- The loop of Algorithm 2 finds a match exactly at the occurrences `p` where a state `t` that
Intmed reaches has an accepting state in component `t` of `match2Set` at `p`, as long as the
occurrences of `α` don't overlap. The hypotheses describe the variables once the occurrences in
`done` have been visited, as in `match1Loop_eq_true_iff`. -/
theorem match2Loop_eq_true_iff {w α : List Symbol} {pre suf preα : ℕ → Bool} {idx : List ℕ}
    (hα : α ≠ []) (hsorted : idx.Pairwise (· < ·)) (hlen : ∀ p ∈ idx, p + α.length ≤ w.length)
    (hno : ∀ p ∈ idx, ∀ p' ∈ idx, p < p' → p + α.length ≤ p') :
    ∀ {rest done : List ℕ} {iprev : ℕ} {S : State → Finset State} {ique : Option ℕ},
      done ++ rest = idx →
      (ique = none → S = (fun _ => ∅) ∧ ∀ p ∈ done, pre p = false) →
      (∀ q, ique = some q → iprev ∈ done ∧ (∀ p ∈ done, p ≤ iprev) ∧
        S = match2Set M w α idx pre iprev ∧
        (pre iprev = true ∧ q = iprev + α.length ∨ pre iprev = false ∧ q ≤ iprev)) →
      (match2Loop M w α pre suf preα iprev S ique rest = true ↔
        ∃ p ∈ rest, ∃ t ∈ intmed M α p 1 preα suf,
          ∃ s ∈ match2Set M w α idx pre p t, s ∈ M.accept) := by
  have hα' := List.length_pos_iff.mpr hα
  intro rest
  induction rest with
  | nil => intros; simp [match2Loop]
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
    have hempty : (∀ p ∈ done, pre p = false) → ∀ t, match2Set M w α idx pre inext t = ∅ := by
      intro hpre t
      have hle : inext ≤ w.length := by have := hlen inext hinext; omega
      ext s
      simp only [Finset.notMem_empty, iff_false]
      rw [mem_match2Set hα hle]
      rintro ⟨p', hp', hpre', hle, -⟩
      rw [hpre p' (hbelow p' hp' (by omega))] at hpre'
      exact Bool.false_ne_true hpre'
    cases ique with
    | none =>
      obtain ⟨rfl, hpre⟩ := hnone rfl
      simp only [match2Loop]
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
          exact ⟨by simp, hle_done, (funext (hempty hpre)).symm, .inl ⟨‹_›, rfl⟩⟩
        · simp at h
    | some q =>
      obtain ⟨hiprev, hmax, hS, hq⟩ := hsome q rfl
      have hlt : iprev < inext := hdone iprev hiprev
      have hiprev_idx : iprev ∈ idx := (hmem iprev).mpr (.inl hiprev)
      -- Lines 5 to 7 compute `match2Set` at `inext` (Proposition 13).
      have hS' : M.evalInjectSum (fun p => decide (p + 1 = q)) S iprev
          ((w.drop iprev).take (inext - iprev)) = match2Set M w α idx pre inext := by
        have htake : w.take inext = w.take iprev ++ (w.drop iprev).take (inext - iprev) := by
          rw [← List.take_add, Nat.add_sub_of_le hlt.le]
        have hlen' : (w.take iprev).length = iprev := by
          have := hlen iprev hiprev_idx
          rw [List.length_take]; omega
        funext t
        rw [Simulator.evalInjectSum, hS, match2Set, match2Set, htake,
          Simulator.evalInject_append, hlen', Nat.zero_add]
        refine Simulator.evalInject_congr fun k hk => ?_
        rw [List.length_take, List.length_drop] at hk
        exact (match1Mark_eq_decide hα hno hiprev_idx (fun p hp h => hmax p (hbelow p hp h)) hq
          (by omega) (by omega)).symm
      simp only [match2Loop]
      rw [hS']
      simp only [Bool.or_eq_true, decide_eq_true_eq]
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

/-- What Algorithm 2 checks, by Proposition 13 and Lemma 14: for a nonempty `α` whose occurrences
in `w` do not overlap, Match2 returns true exactly when there are occurrences `p'` and `p` of `α`
with `p' + |α| ≤ p` and `Pre[p']`, and a prefix length `k ≥ 1` with `Pre_α[k]` and `Suf` after
`p + k`, such that the automaton accepts the rest `α.drop k` of `α` followed by what lies between
the two occurrences. -/
theorem match2_eq_true_iff [DecidableEq Symbol] {w α : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (hno : ∀ i j, α.OccursAt w i → α.OccursAt w j → i < j → i + α.length ≤ j) :
    match2 M w α idx pre suf preα = true ↔
      ∃ p' p, α.OccursAt w p' ∧ α.OccursAt w p ∧ p' + α.length ≤ p ∧ pre p' = true ∧
        ∃ k, 1 ≤ k ∧ k ≤ α.length ∧ preα k = true ∧ suf (p + k) = true ∧
          α.drop k ++ (w.drop (p' + α.length)).take (p - (p' + α.length)) ∈ M.accepts := by
  have hα' := List.length_pos_iff.mpr hα
  have hmem : ∀ p, p ∈ idx ↔ α.OccursAt w p := fun p => by
    rw [hidx]; exact List.mem_occurrences_of_ne_nil hα
  have hlen : ∀ p ∈ idx, p + α.length ≤ w.length := fun p hp =>
    ((hmem p).mp hp).add_length_le hα
  have hloop := match2Loop_eq_true_iff (M := M) (pre := pre) (suf := suf) (preα := preα) hα
    (by rw [hidx]; exact List.pairwise_lt_occurrences α w) hlen
    (fun p hp p' hp' h => hno p p' ((hmem p).mp hp) ((hmem p').mp hp') h)
    (rest := idx) (done := []) (iprev := 0) (S := fun _ => ∅) (ique := none) rfl
    (fun _ => ⟨rfl, by simp⟩) (by simp)
  rw [match2, hloop]
  constructor
  · rintro ⟨p, hp, t, ht, s, hs, hacc⟩
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    obtain ⟨k, hk₁, hk₂, hpreα, hsuf, ht⟩ := (mem_intmed (by omega)).mp ht
    obtain ⟨p', hp', hpre, hle, hs⟩ := (mem_match2Set hα hpw).mp hs
    exact ⟨p', p, (hmem p').mp hp', (hmem p).mp hp, hle, hpre, k, hk₁, hk₂, hpreα, hsuf,
      Simulator.append_mem_accepts_iff.mpr ⟨t, ht, s, hs, hacc⟩⟩
  · rintro ⟨p', p, hp', hp, hle, hpre, k, hk₁, hk₂, hpreα, hsuf, hacc⟩
    obtain ⟨t, ht, s, hs, hacc⟩ := Simulator.append_mem_accepts_iff.mp hacc
    rw [← hmem] at hp hp'
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    exact ⟨p, hp, t, (mem_intmed (by omega)).mpr ⟨k, hk₁, hk₂, hpreα, hsuf, ht⟩, s,
      (mem_match2Set hα hpw).mpr ⟨p', hp', hpre, hle, hs⟩, hacc⟩

/-- Inside an occurrence of `α` at `p'`: from `p' + k` up to a position `p` past the occurrence,
`w` reads the rest `α.drop k` of `α`, then what lies between the occurrence and `p`. -/
private theorem take_drop_eq_drop_append {w α : List Symbol} {p' p k : ℕ}
    (hocc : α.OccursAt w p') (hk : k ≤ α.length) (hp : p' + α.length ≤ p) :
    (w.drop (p' + k)).take (p - (p' + k)) =
      α.drop k ++ (w.drop (p' + α.length)).take (p - (p' + α.length)) := by
  have e : w.drop p' = α ++ w.drop (p' + α.length) := by
    conv_lhs => rw [← List.take_append_drop α.length (w.drop p')]
    rw [← List.prefix_iff_eq_take.mp hocc, List.drop_drop]
  rw [show w.drop (p' + k) = (w.drop p').drop k by rw [List.drop_drop], e,
    List.drop_append_of_le_length hk,
    show p - (p' + k) = (α.drop k).length + (p - (p' + α.length)) by
      rw [List.length_drop]; omega,
    List.take_length_add_append]

/-- Lemma 15, first part, the soundness of Match2: if Match2 returns true, then `e` matches a
nonempty prefix `β` of `α` and `r_β = e₀ β e₁ β e₂` matches `w`. The paper assumes `α` to be a
nonoverlapping right-maximal repeat. -/
theorem exists_mem_rewbLangWith_of_match2_eq_true [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α : List Symbol} {idx : List ℕ} {pre suf preα : ℕ → Bool}
    (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : IsPrefixOracle L α preα) (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (hno : ∀ i j, α.OccursAt w i → α.OccursAt w j → i < j → i + α.length ≤ j)
    (h : match2 M w α idx pre suf preα = true) :
    ∃ β, β <+: α ∧ β ≠ [] ∧ β ∈ L ∧ w ∈ rewbLangWith L₀ L₁ L₂ β := by
  obtain ⟨p', p, hp', hp, hle, hprep', k, hk₁, hk₂, hpreαk, hsufk, hacc⟩ :=
    (match2_eq_true_iff hidx hα hno).mp h
  have hpw := hp.add_length_le hα
  have hlenk : (α.take k).length = k := List.length_take_of_le hk₂
  refine ⟨α.take k, List.take_prefix k α, ?_, (hpreα k hk₂).mp hpreαk, ?_⟩
  · rw [← List.length_pos_iff, hlenk]; omega
  · rw [mem_rewbLangWith_iff_occursAt, hlenk]
    refine ⟨p', p, hp'.of_prefix (List.take_prefix k α), hp.of_prefix (List.take_prefix k α),
      by omega, (hpre p' (by omega)).mp hprep', ?_, (hsuf (p + k) (by omega)).mp hsufk⟩
    rw [take_drop_eq_drop_append hp' hk₂ hle, ← hM]
    exact hacc

/-- Lemma 15, second part, the completeness of Match2 for extendable prefixes: Match2 returns true
for every extendable prefix `β` of `α` that `e` matches and for which `r_β = e₀ β e₁ β e₂` matches
`w`. -/
theorem match2_eq_true_of_isExtendablePrefix [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α β : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre)
    (hsuf : IsSuffixOracle L₂ w suf) (hpreα : IsPrefixOracle L α preα)
    (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (hno : ∀ i j, α.OccursAt w i → α.OccursAt w j → i < j → i + α.length ≤ j)
    (hβ : β.IsExtendablePrefix α w) (hβL : β ∈ L) (hw : w ∈ rewbLangWith L₀ L₁ L₂ β) :
    match2 M w α idx pre suf preα = true := by
  have hα' := List.length_pos_iff.mpr hα
  -- The empty word occurs at the end of `w`, where `α` cannot.
  have hβne : β ≠ [] := by
    rintro rfl
    have := (hβ.occursAt w.length (List.occursAt_nil w w.length)).add_length_le hα
    omega
  have hβ' := List.length_pos_iff.mpr hβne
  have hk₂ := hβ.isPrefix.length_le
  rw [mem_rewbLangWith_iff_occursAt] at hw
  obtain ⟨p', p, hp', hp, hle, h₀, h₁, h₂⟩ := hw
  have hp'α := hβ.occursAt p' hp'
  have hpα := hβ.occursAt p hp
  have hle' := hno p' p hp'α hpα (by omega)
  have hpw := hpα.add_length_le hα
  refine (match2_eq_true_iff hidx hα hno).mpr ⟨p', p, hp'α, hpα, hle',
    (hpre p' (by omega)).mpr h₀, β.length, hβ', hk₂, (hpreα β.length hk₂).mpr ?_,
    (hsuf (p + β.length) (by omega)).mpr h₂, ?_⟩
  · rwa [← List.prefix_iff_eq_take.mp hβ.isPrefix]
  · rw [← take_drop_eq_drop_append hp'α hk₂ hle', hM]
    exact h₁

end Rewb
