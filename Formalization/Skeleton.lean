/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/

/-!
# The skeleton library — currently empty

*Stated but unproved* targets live here: the Lean type of a blueprint node, with `sorry` for the
proof, so that the node can carry a `\lean{...}
otready` tag instead of no tag at all. See the
comment in `lakefile.toml` for why they sit outside `Hemigroup` and what that buys.

A declaration **moves** into `Hemigroup/` when it is proved, and its node goes `\leanok`. Both
entries this library has carried so far left that way: `thm:increments-bernstein` to
`Hemigroup/LevyTriple.lean`, and `lem:action-rigidity` and `prop:canonical-gauge` to
`Hemigroup/Covariance.lean` and `Hemigroup/Gauge.lean`. The next `[T]` node attacked starts here
again.
-/
