/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.Matching

/-! # Matching a rewb of regular expressions -/

namespace RewbTests.Matching

open Rewb

/-- The expression of the symbol `a`. -/
abbrev a : RegularExpression Char := .char 'a'

/-- The expression of the symbol `b`. -/
abbrev b : RegularExpression Char := .char 'b'

/-- The expression `a|b` of a single symbol of `Σ = {a, b}`. -/
abbrev σ : RegularExpression Char := a + b

/-! Remark 11's counterexample: `w = aaaa`, `e₀ = ε|a`, `e = aa` and `e₁ = e₂ = ε`. Match1 misses
it for the overlapping repeat `aa`, but Main finds it. -/

#guard rmatch (1 + a) (a * a) 1 1 "aaaa".toList
#guard !rmatch (1 + a) (a * a) 1 1 "aaa".toList

/-! The instance of Examples 16, 19 and 24: `w = abbabbabbabba`, `e = Σ*` and `e₂ = (ΣΣ)*`, where
the paper describes `e₀` and `e₁` by their languages. Main returns true; Example 19 shows the
match that Match3A finds for `α = abba`. -/

/-- `e₀`: the words with at most two `b`s. -/
def atMostTwoB : RegularExpression Char := a.star * (b + 1) * a.star * (b + 1) * a.star

/-- `e₁`: the words with an odd number of `b`s, at least three. -/
def oddB : RegularExpression Char :=
  a.star * b * a.star * b * (a.star * b * a.star * b).star * a.star * b * a.star

/-- The input word. -/
def w : List Char := "abbabbabbabba".toList

#guard rmatch atMostTwoB σ.star oddB (σ * σ).star w

/-! The rewb `ε(ab)₁ε\1Σ*` on `ababa`: `β = ab` occurs at `0` and `2` and extends to the
right-maximal repeat `aba`, whose occurrences at `0` and `2` overlap. Match3A misses the match
and Match3B finds it. -/

#guard rmatch 1 (a * b) 1 σ.star "ababa".toList

#guard
  let w := "ababa".toList
  let α := "aba".toList
  let pre := prefixOracle (RegularExpression.matches' 1) w
  let suf := suffixOracle σ.star.matches' w
  let preα := prefixOracle (a * b).matches' α
  !match3A (Simulator.ofRegularExpression 1) w α (α.occurrences w) pre suf preα &&
    match3B (Simulator.ofRegularExpression 1) α (α.occurrences w) pre suf preα

/-! `rmatch` decides membership in the language of a rewb. -/

#guard "abab".toList ∈ rewbLang (RegularExpression.matches' 1) (a * b).matches'
  (RegularExpression.matches' 1) (RegularExpression.matches' 1)

/-! A cross-check against Definition 1, by trying every split of the word. -/

/-- Whether `u = u₀ β u₁ β u₂` with `u₀`, `β`, `u₁` and `u₂` matched by `e₀`, `e`, `e₁` and `e₂`
(Definition 1), by trying every split and deciding each part with Mathlib's `rmatch`. -/
def rmatchBySplits (e₀ e e₁ e₂ : RegularExpression Char) (u : List Char) : Bool :=
  (List.range (u.length + 1)).any fun i =>
    (List.range (u.length + 1)).any fun k =>
      (List.range (u.length + 1 - (i + 2 * k))).any fun l =>
        let β := (u.drop i).take k
        e₀.rmatch (u.take i) && e.rmatch β && e₁.rmatch ((u.drop (i + k)).take l) &&
          (u.drop (i + k + l)).take k == β && e₂.rmatch (u.drop (i + 2 * k + l))

#guard rmatchBySplits atMostTwoB σ.star oddB (σ * σ).star w

/-- The words over `{a, b}` of length at most `6`. -/
def words : List (List Char) :=
  (List.range 7).flatMap fun n => (List.replicate n ['a', 'b']).sections

#guard words.length == 127

/-- `rmatch` and `rmatchBySplits` agree on `words`. -/
def agrees (e₀ e e₁ e₂ : RegularExpression Char) : Bool :=
  words.all fun u => rmatch e₀ e e₁ e₂ u == rmatchBySplits e₀ e e₁ e₂ u

-- the squares `ββ`, the empty one included
#guard agrees 1 σ.star 1 1
-- the words with a nonempty square inside
#guard agrees σ.star (σ * σ.star) 1 σ.star
-- the words that begin with a nonempty word and contain it again later, without overlap
#guard agrees 1 (σ * σ.star) σ.star σ.star
-- the words with some `aᵏbaᵏ` inside
#guard agrees σ.star a.star b σ.star
-- the expressions of Remark 11, and those of the Match3B example above
#guard agrees (1 + a) (a * a) 1 1
#guard agrees 1 (a * b) 1 σ.star
-- `e₁ = b*` and `e₂ = (ΣΣ)*`
#guard agrees σ.star (σ * σ.star) b.star (σ * σ).star

end RewbTests.Matching
