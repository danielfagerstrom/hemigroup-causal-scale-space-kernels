/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/

/-!
# The skeleton library — currently empty

This library holds *stated but unproved* targets: the Lean type of a blueprint node, with
`sorry` for the proof, so that the node can carry a `\lean{...}\notready` tag instead of no tag
at all. See the comment in `lakefile.toml` for why they live outside `Hemigroup` and what that
buys.

It is empty right now because the one entry it has had so far — the target type of
`thm:increments-bernstein` — was proved and moved to `Hemigroup/LevyTriple.lean`, which is what
the convention prescribes. The library is kept rather than deleted because the next `[T]` node
attacked will start here: writing the target type first is the point.
-/
