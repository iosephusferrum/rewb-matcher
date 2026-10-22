/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.Match3A
import RewbTests.Match2

/-! # Match3A (Algorithm 4) -/

namespace RewbTests.Match3A

open Rewb
open RewbTests.Match2 (oddB w pre suf preα)

/-! Example 19: the instance of Example 16 (Figure 2 (a)), now with `α = abba`, whose occurrences
overlap. -/

/-- The right-maximal repeat that the example examines. -/
def α : List Char := ['a', 'b', 'b', 'a']

/-- The occurrences of `α`: the paper's `Idx_α = [1, 4, 7, 10]`, in 0-based positions. Each
overlaps the next in one symbol, so `d = 1` (line 3). -/
example : List.occurrences α w = [0, 3, 6, 9] := by decide

example : maxOverlap α.length (List.occurrences α w) = 1 := by decide

/-- Line 11 at the occurrence `9` (the paper's `10`): Intmed starts at the prefix length
`d + 1 = 2`, skipping the prefix `a`, which is not extendable by Lemma 17. It injects after the
prefixes `ab` and `abba`, so `T` holds the states after `ba` and after nothing. -/
example : intmed oddB α 9 2 preα suf = {0, 1} := by decide

/-- The simulation with summarization at line 12 there: the occurrences `0` and `3` have `Pre`,
so component `t` holds what `t` reaches by reading `bbabb` and `bb`. When the occurrence `3`
enqueues its end, the end of the occurrence `0` is still pending, so `Que` holds both; the single
`ique` of Algorithm 2 would have been overwritten, losing the `4` in component `0`. From `1` both
reach `3`, which accepts. -/
example : match2Set oddB w α (List.occurrences α w) pre 9 1 = {3} := by decide

example : match2Set oddB w α (List.occurrences α w) pre 9 0 = {2, 4} := by decide

/-- So Match3A returns true at the occurrence `9`, with `β = ab`: `w` is both
`ε · ab · babbabb · ab · ba` and `abb · ab · babb · ab · ba`, where `e₁` matches the paper's
`w[3..9]` and `w[6..9]`. -/
example : match3A oddB w α (List.occurrences α w) pre suf preα = true := by decide

end RewbTests.Match3A
