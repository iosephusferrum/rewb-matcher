/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Match2

/-!
# Match3A: right-maximal repeats whose occurrences may overlap

Algorithm 4 (`Match3A(α)`, Section 3.2) adapts Match2 to repeats whose occurrences may overlap.
It finds the matches whose two occurrences of the backreferenced word extend to occurrences of `α`
that do not overlap. Two things change. Intmed starts after the longest overlap `d` of two
consecutive occurrences (line 3), since by Lemma 17 no shorter prefix of `α` is extendable. And
the pending injections are kept in a FIFO queue `Que` (lines 6 to 10) instead of the single
`ique`, since several may be due before the next occurrence.

## Main definitions

* `Rewb.maxOverlap`: `d` (Algorithm 4, line 3).
* `Rewb.evalQue`: Algorithm 4, lines 6 to 10.
* `Rewb.match3A`: Algorithm 4.

## Main statements

* `Rewb.maxOverlap_lt`: `d` is below every bound on the overlaps.
* `Rewb.evalQue_fst` and `Rewb.evalQue_snd`: as long as `Que` is sorted and ahead of the
  position being read, the injections it drives are those at the positions it holds, and it keeps
  the positions not yet reached.
* `Rewb.match3ALoop_eq_true_iff`: the claim in the proof of Lemma 18. Thanks to `Que`, the
  simulation with summarization is the one of Proposition 13 at every occurrence, whether or not
  the occurrences overlap.
* `Rewb.match3A_eq_true_iff`: what Match3A checks.
* `Rewb.exists_mem_rewbLangWith_of_match3A_eq_true` and
  `Rewb.match3A_eq_true_of_isExtendablePrefix`: Lemma 18, the correctness of Match3A.

## References

* T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
  Backreferences*, MFCS 2025, arXiv:2504.18247.
-/

@[expose] public section

namespace Rewb

/-- Line 3 of Algorithm 4: `d`, the longest overlap `p + n - p'` of two consecutive occurrences
`p` and `p'` in `idx`, where `n = |α|`, and `0` if none overlap. -/
def maxOverlap (n : ℕ) : List ℕ → ℕ
  | p :: p' :: idx => max (p + n - p') (maxOverlap n (p' :: idx))
  | _ => 0

/-- `d` is below every bound `m > 0` on the overlaps of two occurrences in `idx`. -/
theorem maxOverlap_lt {n m : ℕ} {idx : List ℕ} (hm : 0 < m) (hsorted : idx.Pairwise (· < ·))
    (h : ∀ p ∈ idx, ∀ p' ∈ idx, p < p' → p + n - p' < m) : maxOverlap n idx < m := by
  induction idx with
  | nil => exact hm
  | cons p idx ih =>
    cases idx with
    | nil => exact hm
    | cons p' idx =>
      rw [maxOverlap, max_lt_iff]
      have hpp' : p < p' := List.rel_of_pairwise_cons hsorted (by simp)
      exact ⟨h p (by simp) p' (by simp) hpp',
        ih hsorted.of_cons fun q hq q' hq' hlt => h q (by simp [hq]) q' (by simp [hq']) hlt⟩

variable {State Symbol : Type*} [DecidableEq State] (M : Simulator State Symbol)

/-- Lines 6 to 10 of Algorithm 4: the simulation with summarization reads `u`, whose first symbol
is at position `i`, and right after reading a position `p` it injects (the paper's
`S[l] ← S[l] ∪ {q_l}`) and dequeues if the head of the queue `Que` is `p + 1`, the paper's number
for position `p`. It returns the simulation sets and what is left of `Que`. -/
def evalQue :
    (State → Finset State) → List ℕ → ℕ → List Symbol → (State → Finset State) × List ℕ
  | S, que, _, [] => (S, que)
  | S, que, p, a :: u =>
    let S := fun t => M.stepSet (S t) a
    if que.head? = some (p + 1) then evalQue (fun t => S t ∪ {t}) que.tail (p + 1) u
    else evalQue S que (p + 1) u

variable {M}

/-- In a sorted queue whose entries are past `i`, the entry `i + 1` can only be at the head. -/
private theorem head?_eq_some_iff_mem {que : List ℕ} {i : ℕ} (hsorted : que.Pairwise (· < ·))
    (hgt : ∀ q ∈ que, i < q) : que.head? = some (i + 1) ↔ i + 1 ∈ que := by
  cases que with
  | nil => simp
  | cons q que =>
    simp only [List.head?_cons, Option.some.injEq, List.mem_cons]
    constructor
    · intro h; exact .inl h.symm
    · rintro (h | h)
      · exact h.symm
      · have := List.rel_of_pairwise_cons hsorted h
        have := hgt q (by simp)
        omega

/-- The simulation sets after lines 6 to 10 of Algorithm 4: as long as `Que` is sorted and its
entries are past `i`, it injects exactly after the positions `p` with `p + 1` in `Que`. -/
theorem evalQue_fst {S : State → Finset State} {que : List ℕ} {i : ℕ} {u : List Symbol}
    (hsorted : que.Pairwise (· < ·)) (hgt : ∀ q ∈ que, i < q) :
    (evalQue M S que i u).1 = M.evalInjectSum (fun p => decide (p + 1 ∈ que)) S i u := by
  induction u generalizing S que i with
  | nil => rfl
  | cons a u ih =>
    rw [evalQue]
    split
    -- The head of `Que` is due: inject and dequeue it. Being sorted, `Que` holds it only once.
    · rename_i hhead
      obtain ⟨que', rfl⟩ := List.head?_eq_some_iff.mp hhead
      rw [List.tail_cons, ih hsorted.of_cons fun q hq => List.rel_of_pairwise_cons hsorted hq]
      funext t
      simp only [Simulator.evalInjectSum, Simulator.evalInject_cons, List.mem_cons, true_or,
        decide_true, ite_true]
      refine Simulator.evalInject_congr fun k _ => ?_
      have hne : i + 1 + k + 1 ≠ i + 1 := by omega
      simp only [hne, false_or]
    -- Nothing is due: no injection, and `Que` stays as it is.
    · rename_i hhead
      have hnot : i + 1 ∉ que := fun h => hhead ((head?_eq_some_iff_mem hsorted hgt).mpr h)
      rw [ih hsorted fun q hq => by
        have := hgt q hq
        have : q ≠ i + 1 := fun h => hnot (h ▸ hq)
        omega]
      funext t
      simp only [Simulator.evalInjectSum, Simulator.evalInject_cons, hnot, decide_false,
        Bool.false_eq_true, ite_false]

/-- What is left of `Que` after lines 6 to 10 of Algorithm 4: as long as `Que` is sorted and its
entries are past `i`, the entries past the end `i + |u|` of `u`. -/
theorem evalQue_snd {S : State → Finset State} {que : List ℕ} {i : ℕ} {u : List Symbol}
    (hsorted : que.Pairwise (· < ·)) (hgt : ∀ q ∈ que, i < q) :
    (evalQue M S que i u).2 = que.filter (fun q => i + u.length < q) := by
  induction u generalizing S que i with
  | nil =>
    refine (List.filter_eq_self.mpr fun q hq => ?_).symm
    simpa using hgt q hq
  | cons a u ih =>
    rw [evalQue]
    split
    · rename_i hhead
      obtain ⟨que', rfl⟩ := List.head?_eq_some_iff.mp hhead
      rw [List.tail_cons, ih hsorted.of_cons fun q hq => List.rel_of_pairwise_cons hsorted hq,
        List.length_cons, show i + (u.length + 1) = i + 1 + u.length by omega, List.filter_cons,
        ite_eq_right (by simp)]
    · rename_i hhead
      have hnot : i + 1 ∉ que := fun h => hhead ((head?_eq_some_iff_mem hsorted hgt).mpr h)
      rw [ih hsorted fun q hq => by
          have := hgt q hq
          have : q ≠ i + 1 := fun h => hnot (h ▸ hq)
          omega,
        List.length_cons, show i + (u.length + 1) = i + 1 + u.length by omega]

variable (M)

/-- The loop of Algorithm 4, lines 4 to 16, over the occurrences of `α` still to visit, with the
variables `iprev`, `S` and `Que`, where `none` is the paper's `⊥`. Lines 6 to 10 are `evalQue`,
line 11 runs Intmed from the prefix length `d + 1`, and line 12 is the test of Algorithm 2. As in
the paper, lines 6 to 12 only run once `Que` is set, and an occurrence with `Pre` enqueues its end
(lines 14 to 16). -/
def match3ALoop (w α : List Symbol) (pre suf preα : ℕ → Bool) (d : ℕ) :
    ℕ → (State → Finset State) → Option (List ℕ) → List ℕ → Bool
  | _, _, _, [] => false
  | _, S, none, inext :: idx =>
    match3ALoop w α pre suf preα d inext S
      (if pre inext then some [inext + α.length] else none) idx
  | iprev, S, some que, inext :: idx =>
    let (S, que) := evalQue M S que iprev ((w.drop iprev).take (inext - iprev))
    let T := intmed M α inext (d + 1) preα suf
    decide (∃ t ∈ T, ∃ s ∈ S t, s ∈ M.accept) ||
      match3ALoop w α pre suf preα d inext S
        (some (if pre inext then que ++ [inext + α.length] else que)) idx

/-- Algorithm 4, `Match3A(α)`. `M` simulates `e₁`, `idx` lists the occurrences of `α` in `w` in
increasing order (the paper's `Idx_α`), `pre`, `suf` and `preα` are the arrays `Pre`, `Suf` and
`Pre_α` (line 2), and `d` comes from `idx` (line 3). -/
def match3A (w α : List Symbol) (idx : List ℕ) (pre suf preα : ℕ → Bool) : Bool :=
  match3ALoop M w α pre suf preα (maxOverlap α.length idx) 0 (fun _ => ∅) none idx

variable {M}

/-- The claim in the proof of Lemma 18, as a statement about the loop of Algorithm 4: it finds a
match exactly at the occurrences `p` where a state `t` that Intmed reaches from the prefix length
`d + 1` has an accepting state in component `t` of `match2Set` at `p`. Unlike for Algorithms 1
and 2, the occurrences may overlap: `Que` holds the ends of the occurrences visited so far that
have `Pre` and are not yet passed, so no injection is lost. -/
theorem match3ALoop_eq_true_iff {w α : List Symbol} {pre suf preα : ℕ → Bool} {d : ℕ}
    {idx : List ℕ} (hα : α ≠ []) (hsorted : idx.Pairwise (· < ·))
    (hlen : ∀ p ∈ idx, p + α.length ≤ w.length) :
    ∀ {rest done : List ℕ} {iprev : ℕ} {S : State → Finset State} {que : Option (List ℕ)},
      done ++ rest = idx →
      (que = none → S = (fun _ => ∅) ∧ ∀ p ∈ done, pre p = false) →
      (∀ l, que = some l → iprev ∈ done ∧ (∀ p ∈ done, p ≤ iprev) ∧
        S = match2Set M w α idx pre iprev ∧
        l = (done.filter fun p => pre p && decide (iprev < p + α.length)).map (· + α.length)) →
      (match3ALoop M w α pre suf preα d iprev S que rest = true ↔
        ∃ p ∈ rest, ∃ t ∈ intmed M α p (d + 1) preα suf,
          ∃ s ∈ match2Set M w α idx pre p t, s ∈ M.accept) := by
  have hα' := List.length_pos_iff.mpr hα
  intro rest
  induction rest with
  | nil => intros; simp [match3ALoop]
  | cons inext rest ih =>
    intro done iprev S que hsplit hnone hsome
    -- The occurrences in `done` lie below `inext`, those in `rest` above it.
    have hsorted' : (done ++ inext :: rest).Pairwise (· < ·) := by rw [hsplit]; exact hsorted
    rw [List.pairwise_append, List.pairwise_cons] at hsorted'
    obtain ⟨hdone_sorted, ⟨hrest, -⟩, hcross⟩ := hsorted'
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
    cases que with
    | none =>
      obtain ⟨rfl, hpre⟩ := hnone rfl
      -- Nothing is pending, so nothing is simulated: go on with `inext` in `done`.
      simp only [match3ALoop]
      rw [ih hsplit' ?_ ?_]
      · simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, hempty hpre]
        simp
      · intro h
        refine ⟨rfl, fun p hp => ?_⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact hpre p hp
        · obtain rfl := List.mem_singleton.mp hp
          split at h <;> simp_all
      · intro l h
        split at h
        · rename_i hpi
          obtain rfl := Option.some.inj h
          refine ⟨by simp, hle_done, (funext (hempty hpre)).symm, ?_⟩
          rw [List.filter_append, List.filter_eq_nil_iff.mpr fun p hp => by simp [hpre p hp]]
          simp [hpi, hα']
        · simp at h
    | some l =>
      obtain ⟨hiprev, hmax, hS, hl⟩ := hsome l rfl
      have hlt : iprev < inext := hdone iprev hiprev
      have hiprev_idx : iprev ∈ idx := (hmem iprev).mpr (.inl hiprev)
      -- `Que` is sorted and its entries are past `iprev`.
      have hl_sorted : l.Pairwise (· < ·) := by
        rw [hl, List.pairwise_map]
        exact (hdone_sorted.filter _).imp fun h => by omega
      have hl_gt : ∀ q ∈ l, iprev < q := by
        intro q hq
        rw [hl] at hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
        exact hp.2.2
      have hseg : ((w.drop iprev).take (inext - iprev)).length = inext - iprev := by
        have := hlen inext hinext
        rw [List.length_take, List.length_drop]; omega
      -- Lines 6 to 10 compute `match2Set` at `inext` and leave in `Que` the ends past `inext`.
      have hS' : (evalQue M S l iprev ((w.drop iprev).take (inext - iprev))).1 =
          match2Set M w α idx pre inext := by
        have htake : w.take inext = w.take iprev ++ (w.drop iprev).take (inext - iprev) := by
          rw [← List.take_add, Nat.add_sub_of_le hlt.le]
        have hlen' : (w.take iprev).length = iprev := by
          have := hlen iprev hiprev_idx
          rw [List.length_take]; omega
        rw [evalQue_fst hl_sorted hl_gt]
        funext t
        rw [Simulator.evalInjectSum, hS, match2Set, match2Set, htake,
          Simulator.evalInject_append, hlen', Nat.zero_add]
        refine Simulator.evalInject_congr fun k hk => ?_
        rw [hseg] at hk
        simp only [match1Mark]
        rw [decide_eq_decide, hl]
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨p, ⟨hp, hpre, -⟩, hpk⟩
          exact ⟨p, (hmem p).mpr (.inl hp), hpre, by omega⟩
        · rintro ⟨p, hp, hpre, hpk⟩
          exact ⟨p, ⟨hbelow p hp (by omega), hpre, by omega⟩, by omega⟩
      have hque' : (evalQue M S l iprev ((w.drop iprev).take (inext - iprev))).2 =
          (done.filter fun p => pre p && decide (inext < p + α.length)).map (· + α.length) := by
        rw [evalQue_snd hl_sorted hl_gt, hseg, Nat.add_sub_of_le hlt.le, hl, List.filter_map,
          List.filter_filter]
        congr 1
        refine List.filter_congr fun p _ => ?_
        rw [Bool.eq_iff_iff]
        simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨h₁, h₂, -⟩; exact ⟨h₂, h₁⟩
        · rintro ⟨h₂, h₁⟩; exact ⟨h₁, h₂, by omega⟩
      have hpair : evalQue M S l iprev ((w.drop iprev).take (inext - iprev)) =
          (match2Set M w α idx pre inext,
            (done.filter fun p => pre p && decide (inext < p + α.length)).map (· + α.length)) :=
        Prod.ext hS' hque'
      -- Line 12 joins Intmed's `T` with the summary at `inext`; lines 14 to 16 enqueue the end of
      -- `inext` if `Pre` holds there.
      simp only [match3ALoop]
      rw [hpair]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rw [ih hsplit' ?_ ?_]
      · simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      · intro h; simp at h
      · intro l' h
        obtain rfl := Option.some.inj h
        refine ⟨by simp, hle_done, rfl, ?_⟩
        rw [List.filter_append, List.map_append]
        split
        · rename_i hpi; simp [hpi, hα']
        · rename_i hpi; simp [hpi]

/-- What Algorithm 4 checks, by the claim in the proof of Lemma 18 and Lemma 14: for a nonempty
`α`, Match3A returns true exactly when there are occurrences `p'` and `p` of `α` with
`p' + |α| ≤ p` and `Pre[p']`, and a prefix length `k > d` with `Pre_α[k]` and `Suf` after `p + k`,
such that the automaton accepts the rest `α.drop k` of `α` followed by what lies between the two
occurrences. -/
theorem match3A_eq_true_iff [DecidableEq Symbol] {w α : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hidx : idx = α.occurrences w) (hα : α ≠ []) :
    match3A M w α idx pre suf preα = true ↔
      ∃ p' p, α.OccursAt w p' ∧ α.OccursAt w p ∧ p' + α.length ≤ p ∧ pre p' = true ∧
        ∃ k, maxOverlap α.length idx < k ∧ k ≤ α.length ∧ preα k = true ∧ suf (p + k) = true ∧
          α.drop k ++ (w.drop (p' + α.length)).take (p - (p' + α.length)) ∈ M.accepts := by
  have hα' := List.length_pos_iff.mpr hα
  have hmem : ∀ p, p ∈ idx ↔ α.OccursAt w p := fun p => by
    rw [hidx]; exact List.mem_occurrences_of_ne_nil hα
  have hlen : ∀ p ∈ idx, p + α.length ≤ w.length := fun p hp =>
    ((hmem p).mp hp).add_length_le hα
  have hsorted : idx.Pairwise (· < ·) := by rw [hidx]; exact List.pairwise_lt_occurrences α w
  -- Intmed starts within `α`.
  have hd : maxOverlap α.length idx + 1 ≤ α.length :=
    maxOverlap_lt hα' hsorted fun p _ p' _ hlt => by omega
  have hloop := match3ALoop_eq_true_iff (M := M) (pre := pre) (suf := suf) (preα := preα)
    (d := maxOverlap α.length idx) hα hsorted hlen
    (rest := idx) (done := []) (iprev := 0) (S := fun _ => ∅) (que := none) rfl
    (fun _ => ⟨rfl, by simp⟩) (by simp)
  rw [match3A, hloop]
  -- In line 12, `t` comes from Intmed (Lemma 14) and `s` from the summary (Proposition 13).
  constructor
  · rintro ⟨p, hp, t, ht, s, hs, hacc⟩
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    obtain ⟨k, hk₁, hk₂, hpreα, hsuf, ht⟩ := (mem_intmed hd).mp ht
    obtain ⟨p', hp', hpre, hle, hs⟩ := (mem_match2Set hα hpw).mp hs
    exact ⟨p', p, (hmem p').mp hp', (hmem p).mp hp, hle, hpre, k, hk₁, hk₂, hpreα, hsuf,
      Simulator.append_mem_accepts_iff.mpr ⟨t, ht, s, hs, hacc⟩⟩
  · rintro ⟨p', p, hp', hp, hle, hpre, k, hk₁, hk₂, hpreα, hsuf, hacc⟩
    obtain ⟨t, ht, s, hs, hacc⟩ := Simulator.append_mem_accepts_iff.mp hacc
    rw [← hmem] at hp hp'
    have hpw : p ≤ w.length := by have := hlen p hp; omega
    exact ⟨p, hp, t, (mem_intmed hd).mpr ⟨k, hk₁, hk₂, hpreα, hsuf, ht⟩, s,
      (mem_match2Set hα hpw).mpr ⟨p', hp', hpre, hle, hs⟩, hacc⟩

/-- Lemma 18, first part, the soundness of Match3A: if Match3A returns true, then `e` matches a
nonempty prefix `β` of `α` and `r_β = e₀ β e₁ β e₂` matches `w`. -/
theorem exists_mem_rewbLangWith_of_match3A_eq_true [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α : List Symbol} {idx : List ℕ} {pre suf preα : ℕ → Bool}
    (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre) (hsuf : IsSuffixOracle L₂ w suf)
    (hpreα : IsPrefixOracle L α preα) (hidx : idx = α.occurrences w) (hα : α ≠ [])
    (h : match3A M w α idx pre suf preα = true) :
    ∃ β, β <+: α ∧ β ≠ [] ∧ β ∈ L ∧ w ∈ rewbLangWith L₀ L₁ L₂ β := by
  obtain ⟨p', p, hp', hp, hle, hprep', k, hk₁, hk₂, hpreαk, hsufk, hacc⟩ :=
    (match3A_eq_true_iff hidx hα).mp h
  have hpw := hp.add_length_le hα
  have hlenk : (α.take k).length = k := List.length_take_of_le hk₂
  refine ⟨α.take k, List.take_prefix k α, ?_, (hpreα k hk₂).mp hpreαk, ?_⟩
  · rw [← List.length_pos_iff, hlenk]; omega
  · rw [mem_rewbLangWith_iff_occursAt, hlenk]
    refine ⟨p', p, hp'.of_prefix (List.take_prefix k α), hp.of_prefix (List.take_prefix k α),
      by omega, (hpre p' (by omega)).mp hprep', ?_, (hsuf (p + k) (by omega)).mp hsufk⟩
    -- What `e₁` reads, the rest of `α` and then the gap, lies between the two occurrences of
    -- `α.take k`.
    rw [take_drop_eq_drop_append hp' hk₂ hle, ← hM]
    exact hacc

/-- Lemma 18, second part, the completeness of Match3A: Match3A returns true for every extendable
prefix `β` of `α` that `e` matches and for which `r_β = e₀ β e₁ β e₂` matches `w` with occurrences
of `β` at `p₁` and `p₂` that are `α`-separable, that is, the occurrences of `α` at `p₁` and `p₂`
do not overlap. -/
theorem match3A_eq_true_of_isExtendablePrefix [DecidableEq Symbol]
    {L₀ L L₁ L₂ : Language Symbol} {w α β : List Symbol} {idx : List ℕ}
    {pre suf preα : ℕ → Bool} (hM : M.accepts = L₁) (hpre : IsPrefixOracle L₀ w pre)
    (hsuf : IsSuffixOracle L₂ w suf) (hpreα : IsPrefixOracle L α preα)
    (hidx : idx = α.occurrences w) (hα : α ≠ []) (hβ : β.IsExtendablePrefix α w) (hβL : β ∈ L)
    {p₁ p₂ : ℕ} (hp₁ : β.OccursAt w p₁) (hp₂ : β.OccursAt w p₂) (hsep : p₁ + α.length ≤ p₂)
    (h₀ : w.take p₁ ∈ L₀) (h₁ : (w.drop (p₁ + β.length)).take (p₂ - (p₁ + β.length)) ∈ L₁)
    (h₂ : w.drop (p₂ + β.length) ∈ L₂) :
    match3A M w α idx pre suf preα = true := by
  have hα' := List.length_pos_iff.mpr hα
  -- The empty word occurs at the end of `w`, where `α` cannot.
  have hβne : β ≠ [] := by
    rintro rfl
    have := (hβ.occursAt w.length (List.occursAt_nil w w.length)).add_length_le hα
    omega
  have hβ' := List.length_pos_iff.mpr hβne
  have hk₂ := hβ.isPrefix.length_le
  -- Both occurrences of `β` are occurrences of `α`.
  have hp₁α := hβ.occursAt p₁ hp₁
  have hp₂α := hβ.occursAt p₂ hp₂
  have hpw := hp₂α.add_length_le hα
  -- By Lemma 17, `β` is longer than every overlap of two occurrences of `α`.
  have hd : maxOverlap α.length idx < β.length := by
    subst hidx
    exact maxOverlap_lt hβ' (List.pairwise_lt_occurrences α w) fun p hp p' hp' hlt =>
      hβ.add_length_sub_lt_length ((List.mem_occurrences_of_ne_nil hα).mp hp)
        ((List.mem_occurrences_of_ne_nil hα).mp hp') hlt
  refine (match3A_eq_true_iff hidx hα).mpr ⟨p₁, p₂, hp₁α, hp₂α, hsep,
    (hpre p₁ (by omega)).mpr h₀, β.length, hd, hk₂, (hpreα β.length hk₂).mpr ?_,
    (hsuf (p₂ + β.length) (by omega)).mpr h₂, ?_⟩
  · rwa [← List.prefix_iff_eq_take.mp hβ.isPrefix]
  · rw [← take_drop_eq_drop_append hp₁α hk₂ hsep, hM]
    exact h₁

end Rewb
