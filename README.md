# rewb-matcher

A Lean 4 formalisation of the matching algorithm for regular expressions with backreferences in

> T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
> Backreferences*, MFCS 2025, [arXiv:2504.18247](https://arxiv.org/abs/2504.18247).

The algorithm decides whether a word matches an expression `e₀(e)₁e₁\1e₂`, where `e₀`, `e`, `e₁`
and `e₂` are regular expressions and `\1` repeats the word matched by `(e)₁`.

It builds on [CSLib](https://github.com/leanprover/cslib). Until the CSLib pull requests it still
needs (leanprover/cslib#1147, #1148 and #1149) are merged, it depends on the branch
`thompson-and-repeats` of the fork [iosephusferrum/cslib](https://github.com/iosephusferrum/cslib).

## What is proved

The formalisation proves that the algorithm Main is correct, and that it runs in the time that
Theorem 5 states.

- `Rewb.main_eq_true_iff`: Main returns true exactly when the word is in the language of the
  rewb. It holds for any automaton for `e₁`, given as a simulator, and any arrays `Pre`, `Suf` and
  `Pre_α` that meet their specifications.
- `Rewb.rmatch_eq_true_iff`: the same for regular expressions. `Rewb.rmatch e₀ e e₁ e₂ w` runs
  Main with Thompson's automaton of `e₁` and decides each entry of the arrays with Mathlib's
  `RegularExpression.rmatch`, so membership in the language of a rewb is decidable.
- `Rewb.Timed.time_main_le_mul_sq_mul_sq`: Main runs in `O(n²m²)` time, counted in steps of its
  simulations as in the paper, when it is given EnumRM and the arrays with their costs
  ([Time complexity](#time-complexity)).

The two correctness theorems rest on the standard axioms only (`RewbTests/Axioms.lean`). The space
bound of Theorem 5, `O(n + m²)`, is not formalised.

## Layout

| File | Contents | In the paper |
|---|---|---|
| `Rewb/Basic.lean` | the language of a rewb, the simulator, what the arrays contain | Definition 1, Section 2, Lemma 8 |
| `Rewb/Injection.lean` | simulation with injection and with summarization | Sections 3.1.1 and 3.1.2 |
| `Rewb/Match1.lean` | Match1 | Algorithm 1, Proposition 9, Lemma 10 |
| `Rewb/Intmed.lean` | Intmed | Algorithm 3, Lemma 14 |
| `Rewb/Match2.lean` | Match2 | Algorithm 2, Proposition 13, Lemma 15 |
| `Rewb/Match3A.lean` | Match3A | Algorithm 4, Lemma 18 |
| `Rewb/Match3B.lean` | Match3B | Algorithm 5, Definition 20, Lemma 21, Proposition 22, Lemma 23 |
| `Rewb/Main.lean` | Match and Main | Lemma 6, Theorem 5 |
| `Rewb/EpsilonNA.lean` | the simulator of a finite ε-NFA | Section 2, after Definition 3 |
| `Rewb/RegularExpression.lean` | Thompson's automaton as a simulator | Section 2 |
| `Rewb/Matching.lean` | Main for regular expressions | Theorem 5 |
| `Rewb/Timed/Simulation.lean` | the cost model; simulation with injection and Intmed, timed | Section 2, Algorithm 3 |
| `Rewb/Timed/Match3A.lean` | Match3A, timed | Algorithm 4, Section 3.2 |
| `Rewb/Timed/Fwd.lean` | `Fwd` with two pointers | Algorithm 5, lines 1 to 6 |
| `Rewb/Timed/Match3B.lean` | Match3B, timed | Algorithm 5, Section 3.2 |
| `Rewb/Timed/Main.lean` | the check of `e₀ e₁ e₂` in one pass, and Match, timed | Section 3 |
| `Rewb/Timed/Theorem5.lean` | Main, timed, and its time bound | Theorem 5 |
| `Rewb/ForCslib/Occurrence.lean` | a word occurs at most `n` times | Section 2 |
| `Rewb/ForCslib/Repeat.lean` | a word has at most `n − 1` right-maximal repeats | Section 2 |

CSLib, through the pull requests above, provides the occurrences and the right-maximal repeats of
a word, extendable prefixes with Lemma 17, and Thompson's construction. `Rewb/ForCslib/` holds
further facts about words of this kind, meant for a later CSLib pull request.

## Time complexity

The paper bounds the time of its algorithms by counting the steps of their simulations.
`Rewb/Timed/` restates the algorithms in CSLib's `TimeM ℕ`, which pairs a result with a cost. Each
timed function in `Rewb.Timed` comes with two lemmas: `ret_*` says that it computes the untimed
one, and `time_*` bounds its cost. The cost model (`Rewb/Timed/Simulation.lean`) charges

- `C.step` for reading a symbol in a simulation, with the injection after it and the lookups in
  `Pre`, `Suf` and `Pre_α`, and for an acceptance test: `O(m_e₁)` in the paper;
- `C.sumStep` for reading a symbol in a simulation with summarization, and for testing a summary
  against the set `T` of Intmed: `O(m²_e₁)`;
- `1` for each occurrence of the repeat that a loop visits,

and nothing else. The charges are written into the timed code by hand, so the cost model is part
of what a reader has to trust, as with any `TimeM` analysis.

The timed algorithms follow the paper where the untimed ones take shortcuts: Match3B computes
`Fwd` with the two pointers of Algorithm 5 (lines 1 to 6), and the check of `e₀ e₁ e₂` is a single
pass over `w`. With `n = |w|`:

- `time_match3A_le`: Match3A takes at most
  `|Idx_α|·(2 + C.sumStep + C.step) + n·(C.sumStep + C.step)`. Intmed starts `d` symbols into
  each occurrence, and consecutive occurrences overlap by at most `d`, so it reads no position
  twice.
- `time_fwdList_le` and `time_match3B_le`: `Fwd` takes at most `4·|Idx_α|`, and Match3B at most
  `|Idx_α|·(5 + C.step) + n·C.step`.
- `time_matchRepeat_le`: Match(α) takes at most
  `|Idx_α|·(7 + C.sumStep + 2·C.step) + n·(C.sumStep + 2·C.step)`, the paper's
  `O(n(m_e + m²_e₁))` apart from building `Pre_α`.
- `List.length_occurrences_le` and `List.length_rightMaximalRepeats_le`: a nonempty word occurs at
  most `n` times in `w`, and `w` has at most `n − 1` right-maximal repeats (Gusfield's bound,
  proved by adding one letter at a time).
- `time_main_le`: Main takes at most the time of building `Pre` and `Suf` and of the enumeration,
  plus `cₑ + (2n + 1)·C.step` for testing whether `e` matches `ε` and checking `e₀ e₁ e₂`, plus
  `(n + 1)·cₑ + n·(7 + 2·C.sumStep + 4·C.step)` for each of the at most `n − 1` right-maximal
  repeats, when building `Pre_α` costs at most `(|α| + 1)·cₑ`. This is the refined bound of
  Theorem 5, `O(n² + n(m_e₀ + m_e₂) + µ_right·n(m_e + m²_e₁))`.
- `time_main_le_mul_sq_mul_sq`: if `C.step ≤ m` and `C.sumStep ≤ m²`, building `Pre` and `Suf`
  costs at most `(n + 1)·m` each and `Pre_α` at most `(|α| + 1)·m`, and the enumeration at most
  `(n + 1)²·m`, for some `m ≥ 1` (the length of the rewb, scaled by the constants), then Main
  takes at most `20·(n + 1)²·m²`. This is Theorem 5's `O(n²m²)`.

The timed Main is given the enumeration of the right-maximal repeats (EnumRM, Appendix A) and the
constructions of `Pre`, `Suf` (Remark 4) and `Pre_α` as computations with their costs, which the
paper takes from the literature and from simulation. `Rewb.Timed.ret_main` shows that it computes
`Rewb.main` whenever the enumeration lists the right-maximal repeats with their occurrences, in
any order. Not formalised: EnumRM itself with its suffix and LCP arrays, that a step costs
`O(m_e₁)` and a step with summarization `O(m²_e₁)` for Thompson's automaton, and the space bound.

## Departures from the paper

- Positions are 0-based. `Pre` and `Pre_α` keep the paper's indices; `suf j` is the paper's
  `Suf[j + 1]`.
- The algorithms are generic over the simulated automaton.
- In `Rewb.main`, the right-maximal repeats and their occurrences are listed directly instead of
  by EnumRM (Appendix A), and `Fwd` is computed from its definition instead of by a two-pointer
  scan; in `Rewb.rmatch`, each entry of `Pre`, `Suf` and `Pre_α` is decided by `rmatch` instead of
  by NFA simulation (Remark 4). The results stay the same. The timed Main computes `Fwd` with two
  pointers and is given the rest ([Time complexity](#time-complexity)).
- When `e` matches `ε`, Main checks `e₀ e₁ e₂` by simulating `e₁` with injection after every
  prefix that `e₀` matches, instead of with an automaton for `e₀ e₁ e₂`.

## Notes on the paper

The formalisation turned up the following points. None of them affects Theorem 5.

1. Remark 11 says that Match1 is correct for any repeat, not only right-maximal ones. This holds
   for repeats whose occurrences do not overlap (Lemma 10 does not need right-maximality), but
   not for overlapping ones: for `w = aaaa`, `e₀ = ε|a`, `e = aa` and `e₁ = e₂ = ε`, Match1 on
   `aa` returns false although `w` matches, because `ique` is overwritten
   (`RewbTests/Match1.lean`).
2. Proposition 22, and its restatement in the proof of Lemma 23, should require the suffix
   `w[f(i_j)+i−i_j+1..]` to be in `L(e₂)`, not `w[f(i_j)+i−i_j+1]`; line 12 of Algorithm 5 has it
   right.
3. In the text after Lemma 21, `w[fnext+i−inext..]` should be `w[fnext+i−inext+1..]`.
4. Examples 16 and 24 refer to `Suf` one index too low: `Suf[11]` and `Suf[13]` should be
   `Suf[12]` and `Suf[14]`, and `Suf[7]`, `Suf[9]` and `Suf[11]` should be `Suf[8]`, `Suf[10]` and
   `Suf[12]` (`RewbTests/Match2.lean`, `RewbTests/Match3B.lean`).
5. In condition (2) of the proof of Lemma 10, `i_j′ + |α| < i_j` should be `i_j′ + |α| ≤ i_j`:
   the two occurrences may be adjacent when `e₁` matches `ε`.
6. The proofs of Proposition 9 and Lemma 14 use that `S = ∅` implies `J′ = ∅`, which fails when
   all simulated runs die out. The conclusions still hold, since `Δ(∅, c) = ∅`.

## Tests

`RewbTests/` runs Examples 16, 19 and 24 with a hand-written automaton for `e₁`, checks Remark 11's
counterexample, checks the simulator of Thompson's automaton against `rmatch`, runs the paper's
instances end to end with regular expressions, and compares `Rewb.rmatch` with a decider that
tries every split `w = w₀ β w₁ β w₂` (Definition 1), on all words over `{a, b}` of length at
most 6. The checks are `#guard`s, which Mathlib's `#`-command linter reports as warnings; as in
CSLib's tests, those warnings are expected.

## Building

```bash
lake exe cache get
lake build
lake test
```
