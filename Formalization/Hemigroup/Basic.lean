import ScaleSpaceCore

/-!
# Hemigroup causal scale-space kernels — formalisation

Nothing is stated yet. The blueprint drives this: a node gets a `\lean{...}` tag here once
its statement is written, and `\leanok` once proved.

The `require` of `ScaleSpaceCore` and this import record where this article's causal cone
mathematics went: it was extracted to the trunk in v0.1.1 and is now `CausalAdmissible` there.
This package (v1.0.0, frozen at this release) does not use `ScaleSpaceCore` — the `require` is
provenance, not a dependency. The definitions here are proved from Mathlib alone, so importing
it adds nothing to this article's trust base.
-/
