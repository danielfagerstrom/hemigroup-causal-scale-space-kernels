/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Skeleton.ActionRigidity

/-!
# The skeleton library

*Stated but unproved* targets: the Lean type of a blueprint node, with `sorry` for the proof, so
that the node can carry a `\lean{...}\notready` tag instead of no tag at all. See the comment in
`lakefile.toml` for why they live outside `Hemigroup` and what that buys. A declaration **moves**
into `Hemigroup/` when it is proved, and its node goes `\leanok`; the first entry this library
carried, the target type of `thm:increments-bernstein`, left that way.
-/
