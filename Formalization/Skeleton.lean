/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Skeleton.Chapter7
import Skeleton.Chapter9
import Skeleton.Chapter10
import Skeleton.Chapter11

/-!
# The skeleton library

*Stated but unproved* targets live here: the Lean type of a blueprint node, with `sorry` for the
proof, so that the node can carry a `\lean{...}\notready` tag rather than no tag at all. See the
comment in `lakefile.toml` for why they sit outside `Hemigroup` and what that buys.

A declaration **moves** into `Hemigroup/` when it is proved, and its node goes `\leanok`. Every
entry this library has carried has left that way: `thm:increments-bernstein` to
`Hemigroup/LevyTriple.lean`, `lem:action-rigidity` and `prop:canonical-gauge` to
`Hemigroup/Covariance.lean` and `Hemigroup/Gauge.lean`, `thm:main-analysis` to
`Hemigroup/MainAnalysis.lean` once ledger A18 was taken, chapter 12's
`lem:local-polynomial-symbol` to `Hemigroup/ProfileEuler.lean` --- which emptied
`Skeleton/Chapter12.lean` entirely, so that file is gone --- and `prop:moments` to
`Hemigroup/MeanDelay.lean`, which emptied `Skeleton/Chapter8.lean` the same way. The next `[T]`
node attacked starts here again.
-/
