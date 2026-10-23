/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb.RegularExpression

/-! # The simulator of a regular expression -/

namespace RewbTests.RegularExpression

open Rewb

/-- The words over `{a, b}` of length at most `4`. -/
def words : List (List Char) :=
  (List.range 5).flatMap fun n => (List.replicate n ['a', 'b']).sections

#guard words.length == 31

/-- The simulator of `r` and Mathlib's matcher `rmatch` agree on `words`. -/
def agrees (r : RegularExpression Char) : Bool :=
  words.all fun w => decide (w ∈ (Simulator.ofRegularExpression r).accepts) == r.rmatch w

/-- The expression of the symbol `a`. -/
abbrev a : RegularExpression Char := .char 'a'

/-- The expression of the symbol `b`. -/
abbrev b : RegularExpression Char := .char 'b'

#guard agrees 0
#guard agrees 1
#guard agrees a
#guard agrees (a + b)
#guard agrees (a * b)
#guard agrees a.star
#guard agrees ((a + b).star * b)
#guard agrees (a * b + b).star
#guard agrees (a.star * b).star

/-! Nested stars, and the star of an expression that matches `ε`, give the automaton cycles of
ε-transitions. -/

#guard agrees a.star.star
#guard agrees (1 : RegularExpression Char).star
#guard agrees (b * (a + 1)).star

end RewbTests.RegularExpression
