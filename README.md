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

The formalisation proves that the algorithm Main is correct, which is the part of Theorem 5 that
is not about complexity.

- `Rewb.main_eq_true_iff`: Main returns true exactly when the word is in the language of the
  rewb. It holds for any automaton for `e₁`, given as a simulator, and any arrays `Pre`, `Suf` and
  `Pre_α` that meet their specifications.
- `Rewb.rmatch_eq_true_iff`: the same for regular expressions. `Rewb.rmatch e₀ e e₁ e₂ w` runs
  Main with Thompson's automaton of `e₁` and decides each entry of the arrays with Mathlib's
  `RegularExpression.rmatch`, so membership in the language of a rewb is decidable.

Both rest on the standard axioms only (`RewbTests/Axioms.lean`). The time and space bounds of
Theorem 5, `O(n²m²)` and `O(n + m²)`, are not formalised yet.

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

CSLib, through the pull requests above, provides the occurrences and the right-maximal repeats of
a word, extendable prefixes with Lemma 17, and Thompson's construction.

## Departures from the paper

- Positions are 0-based. `Pre` and `Pre_α` keep the paper's indices; `suf j` is the paper's
  `Suf[j + 1]`.
- The algorithms are generic over the simulated automaton.
- The right-maximal repeats and their occurrences are listed directly instead of by EnumRM
  (Appendix A), `Fwd` is computed from its definition instead of by a two-pointer scan, and each
  entry of `Pre`, `Suf` and `Pre_α` is decided by `rmatch` instead of by NFA simulation (Remark 4).
  The results stay the same; the complexity bounds do not carry over.
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
