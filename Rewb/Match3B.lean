/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Match2

/-!
# Match3B: matches inside overlapping occurrences of the repeat

Algorithm 5 (`Match3B(α)`, Section 3.2) finds the matches whose two occurrences of the
backreferenced word extend to occurrences of `α` that overlap. By Lemma 21 it only needs to pair
each occurrence `i` of `α` with the last occurrence `f(i)` that starts inside it (Definition 20),
and to run Intmed's loop between the two once: no injection position is visited twice.

## Main definitions

* `Rewb.fwd`: `f(i)` (Definition 20), the entries of the array `Fwd` of Algorithm 5.
* `Rewb.match3B`: Algorithm 5.

## Main statements

* `Rewb.sub_lt_length_of_lt_fwd` and `Rewb.fwd_sub_lt_length`: Lemma 21.
* `Rewb.mem_intmed_take`: Proposition 22, the simulation set when line 15 is reached.
* `Rewb.exists_mem_rewbLangWith_of_match3B_eq_true` and
  `Rewb.match3B_eq_true_of_isExtendablePrefix`: Lemma 23, the correctness of Match3B.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- Definition 20: `f(i)`, the last occurrence in `idx` that starts inside the occurrence of `α` at
`i`, where `n = |α|`: the largest `j ∈ idx` with `j < i + n` (the paper's `j ≤ i + |α| − 1`). The
paper computes the array `Fwd` of these values with two pointers (Algorithm 5, lines 1 to 6); here
it is computed from the definition. -/
def fwd (n : ℕ) (idx : List ℕ) (i : ℕ) : ℕ :=
  (idx.filter fun j => j < i + n).foldr max i

/-- `l.foldr max a` is the largest of `a` and the entries of `l`. -/
private theorem foldr_max_spec (l : List ℕ) (a : ℕ) :
    a ≤ l.foldr max a ∧ (∀ j ∈ l, j ≤ l.foldr max a) ∧ (l.foldr max a = a ∨ l.foldr max a ∈ l) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨le_max_of_le_right h₁, ⟨le_max_left _ _, fun j hj => le_max_of_le_right (h₂ j hj)⟩, ?_⟩
    rcases le_total x (l.foldr max a) with h | h
    · rw [max_eq_right h]
      rcases h₃ with h₃ | h₃
      · exact .inl h₃
      · exact .inr (.inr h₃)
    · rw [max_eq_left h]
      exact .inr (.inl rfl)

/-- `f(i) ≥ i`. -/
theorem le_fwd (n : ℕ) (idx : List ℕ) (i : ℕ) : i ≤ fwd n idx i :=
  (foldr_max_spec _ i).1

/-- `f(i)` is an occurrence. -/
theorem fwd_mem {n : ℕ} {idx : List ℕ} {i : ℕ} (hi : i ∈ idx) : fwd n idx i ∈ idx := by
  rcases (foldr_max_spec (idx.filter fun j => j < i + n) i).2.2 with h | h
  · rw [fwd, h]; exact hi
  · exact (List.mem_filter.mp h).1

/-- `f(i)` starts inside the occurrence at `i`. -/
theorem fwd_lt {n : ℕ} {idx : List ℕ} {i : ℕ} (hn : 0 < n) : fwd n idx i < i + n := by
  rw [fwd]
  rcases (foldr_max_spec (idx.filter fun j => j < i + n) i).2.2 with h | h
  · rw [h]; omega
  · simpa using (List.mem_filter.mp h).2

/-- Every occurrence that starts inside the occurrence at `i` is at most `f(i)`. -/
theorem le_fwd_of_mem {n : ℕ} {idx : List ℕ} {i j : ℕ} (hj : j ∈ idx) (hjn : j < i + n) :
    j ≤ fwd n idx i :=
  (foldr_max_spec _ i).2.1 j (List.mem_filter.mpr ⟨hj, by simpa using hjn⟩)

variable {Symbol : Type*}

/-- Lemma 21, first part: for occurrences `i` and `j < f(i)` of `α`, every extendable prefix of `α`
is longer than `j - i`, so that no prefix of `w[i..j−1]` is extendable. Indeed, the occurrences at
`j` and `f(i)` overlap in more than `j - i` symbols (Lemma 17). -/
theorem sub_lt_length_of_lt_fwd [DecidableEq Symbol] {w α β : List Symbol} {i j : ℕ}
    (hβ : β.IsExtendablePrefix α w) (hα : α ≠ []) (hi : α.OccursAt w i) (hj : α.OccursAt w j)
    (hjf : j < fwd α.length (α.occurrences w) i) : j - i < β.length := by
  have hf := (List.mem_occurrences_of_ne_nil hα).mp
    (fwd_mem (n := α.length) ((List.mem_occurrences_of_ne_nil hα).mpr hi))
  have := hβ.add_length_sub_lt_length hj hf hjf
  have := fwd_lt (idx := α.occurrences w) (i := i) (List.length_pos_iff.mpr hα)
  omega

/-- Lemma 21, second part: for occurrences `i < j` of `α`, every extendable prefix of `α` is longer
than `f(i) - j`, so that no prefix of `w[j..f(i)−1]` is extendable. Indeed, the occurrences at `i`
and `j` overlap in more than `f(i) - j` symbols (Lemma 17). -/
theorem fwd_sub_lt_length [DecidableEq Symbol] {w α β : List Symbol} {i j : ℕ}
    (hβ : β.IsExtendablePrefix α w) (hα : α ≠ []) (hi : α.OccursAt w i) (hj : α.OccursAt w j)
    (hij : i < j) : fwd α.length (α.occurrences w) i - j < β.length := by
  have := hβ.add_length_sub_lt_length hi hj hij
  have := fwd_lt (idx := α.occurrences w) (i := i) (List.length_pos_iff.mpr hα)
  omega

/-- The loop of Algorithm 5, lines 8 to 16, over the pairs `(inext, fnext)` of an occurrence of `α`
and its `f` still to visit, with the variable `fprev`. When the guard of line 9 holds, lines 10 to
14 run Intmed's loop from the prefix of `α` at `inext` to the occurrence at `fnext`: for the prefix
lengths `k` from `max 1 (fprev + 1 - inext)` to `fnext - inext`, inject `cl_ε(q₀)` if `Pre_α[k]`
holds and `Suf` holds after `fnext + k`, then read on. As `α` occurs at `inext` and `fnext` lies
inside that occurrence, this is `intmed` on `α.take (fnext - inext)` with the suffix taken after
`fnext`. Line 15 is the acceptance test and line 16 sets `fprev`. -/
def match3BLoop {State : Type*} [DecidableEq State] (M : Simulator State Symbol) (α : List Symbol)
    (pre suf preα : ℕ → Bool) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => false
  | fprev, (inext, fnext) :: occ =>
    (decide (inext < fnext) && pre inext && decide (fprev < fnext) &&
      (let S := intmed M (α.take (fnext - inext)) fnext (max 1 (fprev + 1 - inext)) preα suf
       decide (∃ s ∈ S, s ∈ M.accept))) ||
    match3BLoop M α pre suf preα fnext occ

variable {State : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Algorithm 5, `Match3B(α)`. `M` simulates `e₁`, `idx` lists the occurrences of `α` in the input
word in increasing order (the paper's `Idx_α`), and `pre`, `suf` and `preα` are the arrays `Pre`,
`Suf` and `Pre_α`. Line 8 runs over `zip(Idx_α, Fwd)`, the pairs `(i, f(i))`, and `fprev` starts at
`0` (line 7). The algorithm reads the input word only inside occurrences of `α`, so `match3B`
reads `α` instead. -/
def match3B (α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : Bool :=
  match3BLoop M α pre suf preα 0 (idx.map fun i => (i, fwd α.length idx i))

/-! ### Correctness -/

variable {M}

/-- Inside an occurrence of `α` at `p`: from `p + k` up to a position `f` within the occurrence,
`w` reads `α.take (f - p)` from `k` on. -/
private theorem take_drop_eq_drop_take {w α : List Symbol} {p f k : ℕ} (hocc : α.OccursAt w p)
    (hk : k ≤ f - p) (hf : f - p ≤ α.length) :
    (w.drop (p + k)).take (f - (p + k)) = (α.take (f - p)).drop k := by
  have e : w.drop p = α ++ w.drop (p + α.length) := by
    conv_lhs => rw [← List.take_append_drop α.length (w.drop p)]
    rw [← List.prefix_iff_eq_take.mp hocc, List.drop_drop]
  rw [show w.drop (p + k) = (w.drop p).drop k by rw [List.drop_drop], e,
    List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega), List.drop_take,
    show f - (p + k) = f - p - k by omega]

/-- Proposition 22: when the guard of line 9 holds for the pair `(p, f)` of Algorithm 5, the
simulation set at line 15 consists of the states that `cl_ε(q₀)` reaches by reading `w` from
`p + k` up to `f`, for the prefix lengths `k` from `kbeg` to `f - p` such that `e` matches
`α.take k` and `e₂` matches the suffix of `w` from `f + k`. The paper writes the single symbol
`w[f(i_j) + i − i_j + 1]` where it means this suffix. -/
theorem mem_intmed_take {w α : List Symbol} {p f kbeg : ℕ} {preα suf : ℕ → Bool} {s : State}
    (hocc : α.OccursAt w p) (hk : kbeg ≤ f - p) (hf : f - p ≤ α.length) :
    s ∈ intmed M (α.take (f - p)) f kbeg preα suf ↔
      ∃ k, kbeg ≤ k ∧ k ≤ f - p ∧ preα k = true ∧ suf (f + k) = true ∧
        s ∈ M.evalFrom M.start ((w.drop (p + k)).take (f - (p + k))) := by
  rw [mem_intmed (by rw [List.length_take]; omega), List.length_take, Nat.min_eq_left hf]
  refine exists_congr fun k => ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, ?_⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, ?_⟩⟩
  · rwa [take_drop_eq_drop_take hocc h₂ hf]
  · rwa [take_drop_eq_drop_take hocc h₂ hf] at h₅

/-- The second entry of the last pair of `y :: l`, or `a` if there is none, is that of `l`, or
`y.2`. -/
private theorem getD_map_snd_getLast?_cons (y : ℕ × ℕ) (l : List (ℕ × ℕ)) (a : ℕ) :
    ((y :: l).getLast?.map Prod.snd).getD a = (l.getLast?.map Prod.snd).getD y.2 := by
  rw [List.getLast?_cons]
  cases l.getLast? <;> rfl

/-- The loop of Algorithm 5 finds a match exactly at a pair `(p, f)` where the guard of line 9
holds, with `fprev` the second entry of the pair before it, and where the simulation set of lines
10 to 14 passes the test of line 15. -/
theorem match3BLoop_eq_true_iff {α : List Symbol} {pre suf preα : ℕ → Bool} :
    ∀ {fprev : ℕ} {occ : List (ℕ × ℕ)}, match3BLoop M α pre suf preα fprev occ = true ↔
      ∃ l₁ p f l₂, occ = l₁ ++ (p, f) :: l₂ ∧ p < f ∧ pre p = true ∧
        (l₁.getLast?.map Prod.snd).getD fprev < f ∧
        ∃ s ∈ intmed M (α.take (f - p)) f
          (max 1 ((l₁.getLast?.map Prod.snd).getD fprev + 1 - p)) preα suf, s ∈ M.accept := by
  intro fprev occ
  induction occ generalizing fprev with
  | nil => simp [match3BLoop]
  | cons x occ ih =>
    obtain ⟨p₀, f₀⟩ := x
    simp only [match3BLoop, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [ih]
    -- The pair that succeeds is the first one, or one further on, which the loop reaches with
    -- `fprev = f₀` (line 16).
    constructor
    · rintro (⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ | ⟨l₁, p, f, l₂, rfl, h⟩)
      · exact ⟨[], p₀, f₀, occ, rfl, h₁, h₂, h₃, h₄⟩
      · refine ⟨(p₀, f₀) :: l₁, p, f, l₂, rfl, ?_⟩
        rwa [getD_map_snd_getLast?_cons]
    · rintro ⟨l₁, p, f, l₂, hocc, h⟩
      cases l₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hocc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hocc
        exact .inl ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
      | cons y l₁ =>
        simp only [List.cons_append, List.cons.injEq] at hocc
        obtain ⟨rfl, rfl⟩ := hocc
        rw [getD_map_snd_getLast?_cons] at h
        exact .inr ⟨l₁, p, f, l₂, rfl, h⟩

/-- Lemma 23, first part, the soundness of Match3B: if Match3B returns true, then `e` matches a
nonempty prefix `β` of `α` and `r_β = e₀ β e₁ β e₂` matches `w`. -/
theorem exists_mem_rewbLangWith_of_match3B_eq_true [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α : List Symbol} {idx : List ℕ} {pre suf preα : ℕ → Bool}
    (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : IsPrefixOracle L α preα) (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (h : match3B M α idx pre suf preα = true) :
    ∃ β, β <+: α ∧ β ≠ [] ∧ β ∈ L ∧ w ∈ rewbLangWith L₀ L₁ L₂ β := by
  subst hidx
  have hα' := List.length_pos_iff.mpr hα
  rw [match3B, match3BLoop_eq_true_iff] at h
  obtain ⟨l₁, p, f, l₂, hocc, hpf, hprep, hfprev, s, hs, hacc⟩ := h
  -- The pair is `(i, f(i))` for an occurrence `i`.
  have hmem : (p, f) ∈ (α.occurrences w).map fun i => (i, fwd α.length (α.occurrences w) i) := by
    rw [hocc]; simp
  obtain ⟨i, hi, hif⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at hif
  obtain ⟨rfl, rfl⟩ := hif
  have hiocc := (List.mem_occurrences_of_ne_nil hα).mp hi
  have hfocc := (List.mem_occurrences_of_ne_nil hα).mp (fwd_mem (n := α.length) hi)
  have hflt := fwd_lt (idx := α.occurrences w) (i := i) hα'
  have hfw := hfocc.add_length_le hα
  -- Proposition 22 gives the prefix length `k` and the run of `e₁` inside the occurrence at `i`.
  obtain ⟨k, hk₁, hk₂, hpreαk, hsufk, hs⟩ := (mem_intmed_take hiocc (by omega) (by omega)).mp hs
  have hlenk : (α.take k).length = k := List.length_take_of_le (by omega)
  refine ⟨α.take k, List.take_prefix k α, ?_, (hpreα k (by omega)).mp hpreαk, ?_⟩
  · rw [← List.length_pos_iff, hlenk]; omega
  · rw [mem_rewbLangWith_iff_occursAt, hlenk]
    refine ⟨i, _, hiocc.of_prefix (List.take_prefix k α), hfocc.of_prefix (List.take_prefix k α),
      by omega, (hpre i (by omega)).mp hprep, ?_, (hsuf _ (by omega)).mp hsufk⟩
    rw [← hM]
    exact Simulator.mem_accepts.mpr ⟨s, hs, hacc⟩

/-- Lemma 23, second part, the completeness of Match3B: Match3B returns true for every extendable
prefix `β` of `α` that `e` matches and for which `r_β = e₀ β e₁ β e₂` matches `w` with occurrences
of `β` at `p₁` and `p₂` that are not `α`-separable, that is, the occurrences of `α` at `p₁` and `p₂`
overlap. -/
theorem match3B_eq_true_of_isExtendablePrefix [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α β : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre)
    (hsuf : IsSuffixOracle L₂ w suf) (hpreα : IsPrefixOracle L α preα)
    (hidx : idx = α.occurrences w) (hα : α ≠ []) (hβ : β.IsExtendablePrefix α w) (hβL : β ∈ L)
    {p₁ p₂ : ℕ} (hp₁ : β.OccursAt w p₁) (hp₂ : β.OccursAt w p₂) (hle : p₁ + β.length ≤ p₂)
    (hnsep : p₂ < p₁ + α.length) (h₀ : w.take p₁ ∈ L₀)
    (h₁ : (w.drop (p₁ + β.length)).take (p₂ - (p₁ + β.length)) ∈ L₁)
    (h₂ : w.drop (p₂ + β.length) ∈ L₂) :
    match3B M α idx pre suf preα = true := by
  subst hidx
  have hα' := List.length_pos_iff.mpr hα
  -- The empty word occurs at the end of `w`, where `α` cannot.
  have hβne : β ≠ [] := by
    rintro rfl
    have := (hβ.occursAt w.length (List.occursAt_nil w w.length)).add_length_le hα
    omega
  have hβ' := List.length_pos_iff.mpr hβne
  have hk₂ := hβ.isPrefix.length_le
  have hp₁α := hβ.occursAt p₁ hp₁
  have hp₂α := hβ.occursAt p₂ hp₂
  have hpw := hp₂α.add_length_le hα
  have hmem₁ := (List.mem_occurrences_of_ne_nil hα).mpr hp₁α
  have hmem₂ := (List.mem_occurrences_of_ne_nil hα).mpr hp₂α
  -- The second occurrence is `f(p₁)`, by the first part of Lemma 21.
  have hf : fwd α.length (α.occurrences w) p₁ = p₂ := by
    have := le_fwd_of_mem (n := α.length) (i := p₁) hmem₂ hnsep
    by_contra hne
    have := sub_lt_length_of_lt_fwd hβ hα hp₁α hp₂α (by omega)
    omega
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hmem₁
  -- The pair before `(p₁, f(p₁))`, if any, has its second entry below `p₁ + |β|`, by the second
  -- part of Lemma 21.
  have hfprev : (l₁.getLast?.map fun i => fwd α.length (α.occurrences w) i).getD 0 <
      p₁ + β.length := by
    cases hlast : l₁.getLast? with
    | none => simp; omega
    | some p' =>
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      have hsorted := List.pairwise_lt_occurrences α w
      rw [hsplit, List.pairwise_append] at hsorted
      have hlt : p' < p₁ := hsorted.2.2 p' (by simp) p₁ (by simp)
      have hp' : α.OccursAt w p' := (List.mem_occurrences_of_ne_nil hα).mp (by rw [hsplit]; simp)
      have := fwd_sub_lt_length hβ hα hp' hp₁α hlt
      simp only [Option.map_some, Option.getD_some]
      omega
  have hfp : ((l₁.map fun i => (i, fwd α.length (α.occurrences w) i)).getLast?.map
      Prod.snd).getD 0 = (l₁.getLast?.map fun i => fwd α.length (α.occurrences w) i).getD 0 := by
    rw [List.getLast?_map, Option.map_map]
    rfl
  -- The part between the two occurrences of `β` is accepted.
  rw [← hM] at h₁
  obtain ⟨s, hs, hacc⟩ := Simulator.mem_accepts.mp h₁
  -- The pair `(p₁, p₂)` passes the guard of line 9, and Intmed injects at prefix length `|β|`.
  rw [match3B, match3BLoop_eq_true_iff]
  refine ⟨l₁.map fun i => (i, fwd α.length (α.occurrences w) i), p₁, p₂,
    l₂.map fun i => (i, fwd α.length (α.occurrences w) i), ?_, by omega,
    (hpre p₁ (by omega)).mpr h₀, by rw [hfp]; omega, s,
    (mem_intmed_take hp₁α (by rw [hfp]; omega) (by omega)).mpr ⟨β.length, by rw [hfp]; omega,
      by omega, (hpreα β.length hk₂).mpr ?_, (hsuf _ (by omega)).mpr h₂, hs⟩, hacc⟩
  · set g : ℕ → ℕ × ℕ := fun i => (i, fwd α.length (α.occurrences w) i) with hg
    rw [hsplit, List.map_append, List.map_cons]
    simp only [hg, hf]
  · rwa [← List.prefix_iff_eq_take.mp hβ.isPrefix]

end Rewb
