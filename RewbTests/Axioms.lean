/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

import Rewb

/-! # Axioms

The correctness of Main (Theorem 5), for any simulator and oracles and for regular expressions,
rests on the standard axioms only. -/

/-- info: 'Rewb.main_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rewb.main_eq_true_iff

/-- info: 'Rewb.rmatch_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rewb.rmatch_eq_true_iff
