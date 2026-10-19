# rewb-matcher

A Lean 4 formalisation of the matching algorithm for regular expressions with backreferences in

> T. Nogami and T. Terauchi, *Efficient Matching of Some Fundamental Regular Expressions with
> Backreferences*, MFCS 2025, [arXiv:2504.18247](https://arxiv.org/abs/2504.18247).

The algorithm decides whether a word matches an expression `e₀(e)₁e₁\1e₂`, where `e₀`, `e`, `e₁`
and `e₂` are regular expressions and `\1` repeats the word matched by `(e)₁`.

It builds on [CSLib](https://github.com/leanprover/cslib). Until the CSLib pull requests it needs
(leanprover/cslib#1146 to #1149) are merged, it depends on the branch `thompson-and-repeats` of
the fork [iosephusferrum/cslib](https://github.com/iosephusferrum/cslib).

## Building

```bash
lake exe cache get
lake build
lake test
```
