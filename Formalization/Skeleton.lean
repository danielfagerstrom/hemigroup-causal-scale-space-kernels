/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Skeleton.MainAnalysis

/-!
# The skeleton library

*Stated but unproved* targets live here: the Lean type of a blueprint node, with `sorry` for the
proof, so that the node can carry a `\lean{...}\notready` tag rather than no tag at all. See the
comment in `lakefile.toml` for why they sit outside `Hemigroup` and what that buys.

A declaration **moves** into `Hemigroup/` when it is proved, and its node goes `\leanok`. Both
earlier entries left that way: `thm:increments-bernstein` to `Hemigroup/LevyTriple.lean`, and
`lem:action-rigidity` and `prop:canonical-gauge` to `Hemigroup/Covariance.lean` and
`Hemigroup/Gauge.lean`.

The current entry is different in kind, and worth flagging: `thm:main-analysis`'s `sorry` stands
for a **review decision**, not for work left undone. Its entire hypothesis is proved, as
`CascadeCore.similarity_form`; what is missing is one interface that would widen the trust
boundary. See that file's own docstring.
-/
