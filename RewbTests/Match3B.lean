/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.Match3B
import RewbTests.Match2

/-! # Match3B (Algorithm 5) -/

namespace RewbTests.Match3B

open Rewb
open RewbTests.Match2 (oddB w pre suf preα)

/-! Example 24: the instance of Examples 16 and 19 (Figure 2 (b)), now with `α = abbabba`. -/

/-- The right-maximal repeat that the example examines. -/
def α : List Char := ['a', 'b', 'b', 'a', 'b', 'b', 'a']

/-- The occurrences of `α`: the paper's `Idx_α = [1, 4, 7]`, in 0-based positions. All three start
inside the first, so `f` is `6` for each (Definition 20). -/
example : List.occurrences α w = [0, 3, 6] := by decide

example : (List.occurrences α w).map (fwd α.length (List.occurrences α w)) = [6, 6, 6] := by
  decide

/-- Lines 10 to 14 for the pair `(0, 6)`, the only one whose guard holds: `(3, 6)` comes after
`fprev = 6`, and `(6, 6)` pairs an occurrence with itself. Intmed's loop injects after the prefixes
`a`, `abb` and `abbab` of `α` (the squares at the paper's positions 1, 3 and 5), where `Suf` holds
after `6 + k` for `k = 1, 3, 5`. The paper calls these `Suf[7]`, `Suf[9]` and `Suf[11]`; they are
our `suf 7`, `suf 9` and `suf 11`, its `Suf[8]`, `Suf[10]` and `Suf[12]`. The simulation set holds
the states after `bbabb`, `abb` and `b`. -/
example : intmed oddB (α.take 6) 6 1 preα suf = {1, 2, 4} := by decide

/-- None of them accepts, since `e₁` matches none of `bbabb`, `abb` and `b` (the paper's `w[2..6]`,
`w[4..6]` and `w[6]`), so Match3B returns false. The prefixes `a` and `abb` are not extendable, so
their checks are redundant. -/
example : match3B oddB α (List.occurrences α w) pre suf preα = false := by decide

end RewbTests.Match3B
