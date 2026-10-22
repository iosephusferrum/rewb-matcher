/-
Copyright (c) 2026 Yusuf Demir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yusuf Demir
-/

module

public import Rewb.Basic
public import Rewb.Injection
public import Rewb.Intmed
public import Rewb.Match1
public import Rewb.Match2
public import Rewb.Match3A

/-!
# Matching regular expressions with a backreference

A formalisation of the matching algorithm of T. Nogami and T. Terauchi, *Efficient Matching of Some
Fundamental Regular Expressions with Backreferences* (MFCS 2025, arXiv:2504.18247), for
expressions of the form `e₀(e)₁e₁\1e₂` with `e₀`, `e`, `e₁` and `e₂` regular.
-/
