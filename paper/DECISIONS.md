# Editorial decisions of record — content review, 2026-08-16

Taken by the author in one sitting (Step 0 of `PLAN-content-review.md`) after the fourteen blind
draft reviews. Each section step applies these; a decision is not re-opened section by section.

## D-A · The pure delay is in the class

`F(s) = b₀s`, `μ_{0,x} = δ_x`, is a member: the theorem admits it, `cor:semigroup-case` returns it as
α = 1, `prop:extreme-rays` names it an extreme ray, and the Lean witness `delayCore` is it. The axioms
use the identity operator throughout, so excising the Dirac kernel would be clumsy for no gain; the
accurate reading — that a point measurement is not physically realizable and is a *limit* of extended
ones — was not built into the axiomatization and is not worth building in now.

**How the prose handles it.** The pure delay is separated *in the text*, not excluded from the class:

- speak of kernels as **measures**; say "density" only where one exists;
- state absolute continuity, unimodality and every other property that fails on the drift ray
  **under `k ≢ 0`** (as `appendix-memory.tex` already does), naming the drift ray as the exception;
- §1: the semigroup case is the stable family *together with* the pure delay, not "precisely the
  sub-case"; §2 `rem:axiom-provenance`: no "nothing else", no "the convolution kernels"; §4: measures;
  §7 `rem:extreme-rays`: both universal bounds under `k ≢ 0`; §8 `rem:heavy-tails`: "the only `k` with
  a density …"; §10: case (1) is a case, `rem:drift-boundary` says why the semigroup theory excluded
  it; §11 and App. A carry the `b₀` term where it was omitted.

### D-A′ · The closed half-line: the extended point motivates, the formalization includes scale 0

(Author, 2026-08-16, on reflection during the §2 step.) The extended point — no record is the
signal, no stage is the identity — is a requirement on *physical realization* and is the motivation.
The *formal* theory is set on the closed half-line `[0,∞)` with the signal as the record at scale 0
and `Φ_{x,x} = Id` on the diagonal; both are admitted as the limits (A7) refers to, in the same way
`δ` enters 2005's extended-point axiom `lim φ_τ = δ`. Nothing is measured *at* scale 0. Taking
"measurement of a measurement" as a formal requirement (every stage strictly smoothing) would give a
discrete ladder and would still need the diagonal in its closure to state continuity — not pursued.
The pure delay is the degenerate member admitted for the same reason as the identity. §2 says this
once, explicitly (the paragraph after the operator is introduced, and the worked-member paragraph
after Def. 2.1).

**Later sections must keep to it:** the signal is "the record at scale 0" (§1 too); kernel language
never implies a density; (H)'s "no atom at zero *delay*" is a different zero and is phrased so it
cannot be read as scale 0; §7's drift ray and §10's case (1) are this same member. Checked in the
global sweep.

## D-B · (H) has one home, and the summaries carry it carefully

`def:standing-hypothesis` stays in §9's opening; every result on the memory line says "Assume (H)" as
now. Additions:

1. §1's roadmap paragraph gets **one sentence** announcing that the memory-line results hold under a
   standing hypothesis (H) stated in §9. **It must not explain (H) in unexplained terms** — no
   `z_*`, no negative moments, no "atom at zero delay" before those objects exist. Acceptable form:
   "…under a mild standing hypothesis on the exponent, (H), stated in §9 and satisfied by every family
   in §8 except the Gamma family at small shape".
2. §2's embodiment promise is qualified by a pointer, in the same non-technical form.
3. §8's Gamma proposition is unchanged (true for all γ > 0); a one-line remark after it says the
   memory line needs γ > 1.
4. §9's paragraph after the definition says what is true: the extreme rays with `b₀ = 0` lie on
   (H)'s boundary (`z_* = 1`); `b₀ > 0` gives `z_* = ∞`; the Gamma family at γ ≤ 1 is excluded although
   it is not extreme. "(H) excludes the cone's extreme boundary and nothing else" is dropped.
5. §7 `rem:extreme-rays` loses its forward-stated (H)-boundary half, which moves to §9 (item 4).
6. §12: "the entire temporal jet" → the jet up to order `< z_* − 1`.

## D-G · One working gauge, and the parabolic gauge has its own symbol

The **canonical gauge** `x̃ = χ(x)` (Prop. 6.x) is the working gauge from §6 to the end;
`rem:gauge-freedom`'s "used in the sequel" is corrected to "used where the diffusive realization is
written out". The **parabolic gauge** is written **`ξ`** (`ξ = x²/2` relative to the canonical gauge —
the ½ is the heat-equation normalization that makes the Bessel generator `½∂²_ξ + (β/ξ)∂_ξ`), defined
once at its first use in §8 and named at each later use (§9's Bessel example, §10's Bessel remark,
§12's display). `x̃` is never used for the parabolic gauge again. Blueprint-side where the symbol sits
in a shared statement (`prop:bessel-family`).

## D-D · Economy claims: exact or removed; §1.1 is the one statement of what rests on what

§1.1 states, in the words the axiom guard checks, what the *verified* results rest on. Elsewhere:

- counts that are not load-bearing are deleted (§3 "exactly three places", §4 "each used once");
- where a printed proof and the verified proof take different routes (§7's use of Bernstein–Widder),
  one sentence at the point of claim says so — the printed proofs **stay classical**, and the sentence
  marks the divergence; printed proofs are not rewritten to follow the Lean route;
- §10's Mellin-uniqueness appeal vs §1.5's "eliminated": checked against the current blueprint proof
  in the §10 step, and whichever is false is changed;
- §13 restates §1.1's sentence with its scope ("the verified results"), not "the results here".

## Registries (applied per section, no further decision)

- **Notation** — rename the *later* introduction of a colliding symbol; define at first use; the delay
  semigroup `T_r` is written as the translation `τ_r` it is (`T_1`, `T_x` stay the subordinator —
  ~100 uses against ~15; decided in the §3 step);
  `\SDclass`, `\GGC`, `\CBF` and the other undefined symbols are defined where first used or dropped.
- **Figures** — generous; see the table in `PLAN-content-review.md`.
- **Pointers** — mechanical, in the owning step.
