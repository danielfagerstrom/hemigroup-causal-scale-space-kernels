# Detailed review of *Time-Causal Scale Space from Hemigroup Axioms*

## Overall assessment

This is an ambitious, original, and potentially important manuscript. Its strongest contribution is the characterization theorem: replacing the one-parameter semigroup by a two-parameter hemigroup/evolution family appears to enlarge the admissible causal, covariant scale spaces from the stable family to the self-decomposable laws. That is a clean conceptual move with a satisfying probabilistic answer. The Gamma family then gives the paper an excellent concrete representative: finite moments, exponential tails, exact covariance, a recursive realization for integer shape, and endpoint variation-diminishing behavior.

My journal-style recommendation would be **major revision**. The central characterization looks worthy of publication, but several claims are currently stronger than the results actually establish. The most important concern is the treatment of “non-creation”: the manuscript proves an input-to-scale variation bound for certain endpoint kernels, while classical scale-space non-creation is a scale-to-scale property. The paper itself notes that its increments are not variation-diminishing and that extremum counts can rise between scales. This is not a small terminological matter, because “non-creation is recovered” is one of the headline claims in the abstract, introduction, and conclusion.

I would encourage the author to revise rather than retreat. The core story remains strong after the necessary qualifications:

> Dropping stationarity/interchangeability of scale increments preserves causal recursive composition, yields exactly the self-decomposable delay laws, removes the stable-family moment obstruction, and opens useful Gamma and Bessel subfamilies. Certain endpoint maps are variation-diminishing relative to the raw input, while local positive memory-line realizations are exactly Bessel-type.

That is already a substantial paper.

## What is especially strong

1. **The central conceptual move is memorable.** The paper correctly isolates two assertions hidden in the semigroup law: composability and stationarity/interchangeability of scale increments. Replacing the semigroup by a hemigroup retains the first and releases the second. Figures 1–4 communicate this well.

2. **The characterization has an elegant final form.** The sequence
   
   - translation covariance and causality imply convolution by probability measures;
   - the cascade makes exponents additive and infinitely divisible;
   - scale covariance produces the similarity form;
   - self-decomposability characterizes the remaining exponent;
   
   is mathematically natural and gives the paper a real theorem-driven backbone.

3. **The random-delay interpretation is excellent.** Reading a causal kernel as a law of random delay makes the drift, Lévy measure, moments, and implementation consequences intuitive. This should remain the primary interpretation.

4. **The three example families are well chosen.** Stable, Gamma, and Bessel expose different principles: homogeneity, finite-state rational implementation, and local positive memory-line dynamics. Tables 1–3 and Figures 6, 10, and 11 make the tradeoffs tangible.

5. **The author is unusually transparent about formalization.** Section 1.1 distinguishes what is machine-checked, what is paper-only, and which analytic facts are imported. That is valuable, provided the repository and exact revision are made directly accessible.

6. **The paper often anticipates the right objection.** For example, it explicitly distinguishes uniqueness of the inversion operator from uniqueness of a solution, notes the period-one ambiguity, and acknowledges that synthetic data are not empirical validation. This intellectual honesty makes the remaining overclaims easier to repair.

## Publication-critical issues

### 1. “Non-creation” is not recovered in the classical scale-space sense

This is the issue I would expect a mathematical computer-vision reviewer to raise first.

Proposition 8.13 classifies cases in which the **endpoint kernel** from the raw signal to scale $x$ is Polya-frequency/variation-diminishing. It yields, for a fixed level $c$, an input-relative bound of the form

$$
S^-(u(\cdot,x)-c)\leq S^-(f-c).
$$

But the manuscript also explains that the increment kernel from scale $a$ to scale $b$ is generally not Polya frequency. Consequently, the number of crossings or extrema can increase as scale moves from $a$ to scale $b$, even though it remains bounded by the raw input count. Example 12.7 reports precisely such increases.

That is not the classical scale-space causality/non-creation property, which compares every coarser representation with every finer one. A feature absent at scale $a$ but present at scale $b>a$ has been created along the scale evolution, even if the total number at $b$ does not exceed the number in the original signal.

I recommend the following changes:

- Replace “non-creation is recovered” with **“endpoint variation diminution relative to the input”** or **“an input-relative variation bound.”**
- State explicitly in the abstract and introduction that classical scale-monotone non-creation is *not* recovered because the hemigroup increments need not be variation-diminishing.
- Recast Remark 8.14 as a comparison of two different properties, not as dissolution of the original obstruction. The hemigroup avoids the obstruction by weakening the property being required of increments.
- Rename the relevant row in Table 1 from “non-creation in time” to “endpoint VD relative to input.”
- Reword the Figure 14 discussion. “Arches never reopening” is a stronger scale-to-scale statement than Proposition 8.13 supplies and is not certified by one numerical example.

There is also a concrete flaw in the proof on PDF page 33. The sentence “a function with $n$ local extrema admits a level $c$ with $n+1$ sign changes” is false in general: different oscillations can occupy disjoint value ranges, so no single horizontal level intersects all of them. The displayed level-by-level variation bound therefore does not by itself imply that the total number of local extrema is bounded. A correct route would require additional regularity and application of variation diminution to the derivative, for example

$$
(\mu*f)'=\mu*f'
$$

for an appropriate class of differentiable signals, followed by a sign-change bound for $f'$. The theorem must state the needed function class and how flat extrema or distributional derivatives are counted.

### 2. There is an internal inconsistency in the semigroup/canonical gauge

On PDF page 24, immediately after Proposition 6.3, the paper says that in the semigroup case $S_\sigma x=\sigma x$, the gauge $\chi$ is the identity, and $F(s)=s^\alpha$. Later, Proposition 8.7 correctly says that in the one-parameter semigroup parametrization $\chi(x)=x^{1/\alpha}$, and Remark A.23 identifies the old semigroup parameter as $\tau=x^\alpha$.

The correct distinction appears to be:

- in the additive semigroup parameter $\tau$, $G(\tau,s)=\tau s^\alpha$ and $S_\sigma\tau=\sigma^\alpha\tau$;
- the canonical delay-scale coordinate is $x=\chi(\tau)=\tau^{1/\alpha}$, in which $G=F(xs)$, $F(s)=s^\alpha$, and $S_\sigma x=\sigma x$.

Thus $\chi$ is not the identity in the original semigroup parameter unless $\alpha=1$, or unless the variable has already been silently renamed to the canonical coordinate. This should be corrected everywhere and supported by a small notation table distinguishing original scale, canonical delay scale, and the parabolic/Bessel gauge.

### 3. “Well posed” is stronger than what Corollary 9.21 proves

The paper does good work distinguishing operator uniqueness from solution uniqueness. However, Corollary 9.21 proves existence and uniqueness only in a specially defined Mellin class whose modes satisfy analyticity and a profile-domination/bounded-periodic-factor condition. It does not establish continuous dependence on the boundary data in a declared solution topology.

In the standard PDE usage, well-posedness normally comprises existence, uniqueness, and stability/continuous dependence. I therefore suggest one of two routes:

- prove a stability estimate for the solution map in explicit data and solution norms; or
- rename the result **“existence and uniqueness in the profile-dominated Mellin class.”**

The abstract and introduction should use the same qualified language. The present phrase “well posed: ... the solution too is unique in a natural class” makes the restriction sound milder than it is. The class may well be appropriate, but it needs motivation independent of the known solution and a short discussion of whether perturbations of a profile-dominated mode remain controlled.

### 4. The “Gamma substrate for the entire Thorin subclass” claim outruns Proposition 11.6

Proposition 11.6 establishes that an atomic positive Thorin measure gives a finite sum of Gamma exponents and remains inside the admissible class. It also states that the resulting transfer is rational **when the atomic weights are integers**. Standard quadrature weights are arbitrary positive real numbers, not integers. A factor

$$
(1+s/\tau)^{-w}
$$

with non-integer $w$ is not a finite cascade of first-order sections.

Therefore the bold statement on PDF page 60—“the Gamma family is the implementation substrate for the entire Thorin subclass ... the machine one builds is a bank of first-order Gamma sections”—is not established as written. The result currently supports:

- approximation inside the admissible class by finite **fractional-shape Gamma factors**;
- exact finite first-order realizations for integer weights;
- a heuristic rational-fitting route for the rest, without an error theorem.

To retain the stronger implementation claim, the paper needs a constructive theorem showing that arbitrary positive Thorin measures can be approximated to a stated norm/bandwidth tolerance by integer-weight first-order sections, together with a state-count/error bound. Otherwise, qualify the claim and separate “admissible atomic approximation” from “finite-state rational implementation.”

Two smaller implementation qualifications belong here:

- a deterministic drift delay is an exact sample delay only when it is commensurate with the sampling interval; otherwise it is a fractional-delay problem;
- “a fixed number of sections per decade” is explicitly called a heuristic later, so it should not be advertised earlier as a general logarithmic state-count result.

### 5. The signal model needs a clearer bridge to computer vision

The axioms are posed on $L^1(\mathbb R)$, and mass conservation replaces literal preservation of constant gray levels. This is mathematically convenient for probability kernels and Laplace transforms, but live temporal image signals, stationary streams, steps, and nonzero baselines are typically not $L^1$. The numerical example itself contains a persistent step over the displayed interval.

For a mathematical computer-vision journal, the paper should say what is technical scaffolding and what is the intended signal class in applications. At minimum:

- explain whether every constructed convolution family extends consistently to $L^p$, $L^\infty$, bounded continuous signals, finite measures, or distributions;
- distinguish mass conservation on transients from preservation of a constant intensity level;
- state which characterization steps genuinely require $L^1$ and which conclusions survive after extension;
- either add one natural-signal experiment or make the paper’s scope explicitly theoretical and reduce application rhetoric.

The [official record for the author’s 2005 paper](https://kth.diva-portal.org/smash/record.jsf?pid=diva2%3A417092) foregrounds temporal causality, positivity, recursivity, and time-recursive state realization. The present manuscript should make it very easy for that readership to see, within the first two pages, which old limitation is removed and what an implementer gains.

### 6. Several broad claims need proof, citation scope, or relocation

- **Markov media (pages 49–50 and Table 1).** Remark 9.27 records substantial assertions without proof, including a symbol characterization and the existence/nonexistence of Markov media in parts of the stable family. Table 1 then presents the conclusions as settled facts. Either prove/cite them precisely or mark them as context/conjectural scope rather than as results of this paper.

- **All one-dimensional diffusion hitting times (page 36).** The sentence “the first-passage time of every one-dimensional diffusion...” is broader than the hypotheses stated in [Kent’s original result](https://doi.org/10.1007/BF00538895), which concerns a non-singular diffusion on an interval and an interior hitting problem. State the boundary, regularity, killing, and accessibility assumptions that make the cited theorem applicable.

- **Finite limit-kernel truncations (page 69).** The statement that finite truncations are not dilation-closed appears to conflict with Proposition 11.6: every finite atomic exponent $F_N$ generates a fully covariant similarity family $F_N(xs)$. If the text instead means the old fixed-time-constant cascade viewed without rescaling all poles, say so explicitly.

- **Signed Laplace uniqueness.** Proposition 3.8/3.9 is repeatedly invoked to identify real $L^1$ functions or signed locally finite measures (for example in Corollary 9.21 and Theorem A.19), while the stated propositions appear phrased for measures in the positive-measure vocabulary. State and prove/cite the finite signed version, or explain the reduction by Jordan decomposition/exponential tilting.

## Appendix-specific corrections

1. **PDF page 74:** the sentence saying that Section 10 “identifies” the complete-Bernstein subfamily with the locality corner is misleading or false. Section 10 shows that the real-root local ladder lies inside the Thorin/complete-Bernstein class and classifies the local-plus-PMP case. The complete-Bernstein/Thorin class is much larger and generally nonlocal. Replace “identifies with” by “contains” or “includes the local families classified in Section 10.”

2. **PDF page 75:** “at its left endpoint $t=b_0x$—where $\varphi_x$ itself vanishes” is false in general. A Gamma density with shape $\gamma=1$ is positive at its left endpoint, and for $0<\gamma<1$ it diverges there. What vanishes is the coefficient $t-b_0x$, and the density vanishes *to the left* of its support endpoint.

3. The paragraph after Proposition A.12 informally claims that the singular homogeneous Volterra equation plus unit mass selects a unique density and that Picard iteration preserves positivity. Since no theorem or hypotheses are supplied, this is too strong for the general nonincreasing $k$ allowed by the paper. Either prove a precise well-posedness result under explicit regularity assumptions or present this only as a numerical heuristic.

4. “Exact invertibility” in Corollary A.8 is a one-sided identity $D^{(x)}I^{(x)}=\mathrm{Id}$ in distributions. The surrounding “conservation of information” language should continue to emphasize that this is not a proof that every smoothing increment $\Phi_{x,y}$ has a stable causal inverse.

## Storytelling and organization

The manuscript currently contains enough material for roughly two papers:

1. hemigroup axioms, characterization, examples, moments, and endpoint variation diminution;
2. Mellin signaling, locality, implementations, jets, and the scale-Cauchy/Sonine theory.

Keeping it as one paper is possible, but 82 pages and the number of theorem-level contributions obscure the most original message. A reader reaches the main characterization only on page 26 and the practical Gamma payoff later still.

### A cleaner narrative spine

I suggest organizing the story around four questions:

1. **Which classical assumption causes the heavy-tail obstruction?** The stationarity/interchangeability hidden in the semigroup.
2. **What replaces the stable family after that assumption is removed?** Exactly self-decomposable delay laws.
3. **What useful new members appear?** Gamma for finite moments and recursive filters; Bessel for local positive memory media.
4. **What is and is not preserved?** Exact continuous covariance and endpoint input-relative variation diminution are preserved; classical scale-monotone non-creation generally is not.

This would make the paper easier to trust because the tradeoff is explicit rather than revealed after the headline claim.

### Specific structural suggestions

- Shorten the abstract to about 180–220 words. It currently introduces self-decomposability, Sato subordinators, Gamma filters, variation diminution, Mellin inversion, Riemann–Liouville memory, Bessel media, jets, and Lean in one paragraph. Keep the main theorem, one concrete consequence, and one memory-line consequence.
- Reduce Section 1.1 to a half-page table in the main text and move the detailed formalization ledger to an appendix or supplement.
- Move the HCM/GGC/Stieltjes catalogue from Section 3 to the sections where each class first does work. The reader is asked to retain too many named classes before seeing why they matter.
- Add a one-page notation table for $g_{x,y},G,F,H,B,m,\phi_x,k,\kappa^{(x)},\ell^{(x)}$ and for the original, canonical, semigroup, and parabolic scale coordinates.
- Keep the random-delay/subordinator metaphor as the main explanatory device. The optical-depth, dye, catalogue, cliff, ladder, collar, and embodiment metaphors are individually good, but together they compete for attention.
- Consider moving the full proofs of the convolution representation and some Mellin technical lemmas to appendices if the journal permits. The main line should let the reader reach Theorem 7.3 sooner.
- Give the repository URL, immutable commit or release tag, Lean/Mathlib versions, and one-command verification instructions in the paper itself.

### Title options

The present title undersells the second half of the paper. Possible alternatives are:

- *Time-Causal Scale Spaces beyond Semigroups: Hemigroup Characterization and Memory-Line Realizations*
- *Causal Covariant Scale Spaces from Hemigroups: Self-Decomposable Kernels, Local Media, and Temporal Jets*

If the paper is split, the current title would fit the characterization paper well.

## Presentation and visual polish

- The visible red and green hyperlink rectangles around nearly every citation and cross-reference are highly distracting across all 82 pages. Compile with hidden links or unobtrusive colored text and no boxes.
- The main figures are generally sharp and useful. Figure 14 becomes almost solid black in the noise region; an inset, density plot, or thresholded/prominence-coded rendering would communicate more.
- Table 1 is information-rich but small and mixes proved results, implementation heuristics, and an unproved Markov-medium remark. Split it or label the evidentiary status of each row.
- On PDF page 62, check the script name `make-figureps.py`; it looks like a typo for `make-figures.py`.
- Use one theorem-numbering scheme. Labels such as “Theorem 4-prime (Theorem 9.17)” and “Theorem 5-prime (Theorem 10.6)” make the paper feel dependent on the earlier article and increase navigation cost.
- Define precisely how extrema and zero crossings are counted in Example 12.7, including threshold, prominence, sampling boundary, flat regions, and interpolation. The counts currently look more definitive than the discretization discussion permits.

## Prioritized revision plan

### First pass: correctness and claims

1. Reframe Proposition 8.13 and every “non-creation recovered” claim as endpoint/input-relative variation diminution.
2. Repair or remove the false local-extrema inference on page 33.
3. Fix the semigroup/canonical-gauge contradiction on page 24.
4. Qualify “well posed” or add a stability theorem.
5. Separate atomic Thorin approximation from finite-state integer-weight realization.
6. Correct the Appendix A.9/A.12 statements and clarify the signed Laplace-uniqueness tool.
7. Scope or prove the Markov-medium and diffusion-hitting-time claims.

### Second pass: focus

1. Decide whether to split the characterization and memory-line papers.
2. Rewrite the abstract and first two introduction pages around the four-question spine above.
3. Move the formalization ledger and secondary named-class material out of the main flow.
4. Add a notation/gauge table and a compact theorem-dependency map.

### Third pass: computer-vision relevance and reproducibility

1. Explain extension beyond $L^1$ transients.
2. Add a natural temporal signal/video/audio example or explicitly narrow the claims to mathematical foundations.
3. Publish the code and Lean artifact at an immutable revision.
4. Remove link boxes and improve the densest figure/table.

## Suggested editorial decision

**Major revision.** The characterization theorem and its Gamma/Bessel consequences are strong enough to justify substantial revision. I would not recommend acceptance in the current form because the non-creation headline, the gauge inconsistency, the restricted notion of well-posedness, and the implementation overclaim affect the paper’s central advertised contributions. All appear repairable without sacrificing the main theorem or the most interesting narrative.

The friendly-professor version of the same verdict is: there is a very good paper here, possibly two. The next revision should make the reader remember one decisive move—composition without interchangeable stages—and then earn each consequence with deliberately calibrated language.