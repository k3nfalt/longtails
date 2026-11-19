# SphericalPreferenceDescent: novelty assessment

[`result`](../../LongTails/Theorems/SphericalPreferenceDescent.lean) proves the following. Let f be convex on the ball ‖x‖ ≤ R in ℝ^d, with d ≥ 2. Each query (x, y) is answered by one fresh IID respondent Z ~ μ with the bit 1[f(x)+⟨Z,x⟩ ≥ f(y)+⟨Z,y⟩]. Here μ is an unknown rotation-invariant law (atoms and heavy tails are allowed), and μ{z : f+⟨z,·⟩ is B-Lipschitz on the ball} ≥ 1/2 ([setup](../../LongTails/Setups/SphericalRandomUtility.lean)). Under these assumptions, a jittered one-bit sign-descent method that knows d, R, B and ε ([algorithm](../../LongTails/Algorithms/SphericalPreferenceDescent.lean)) returns the projected average of its iterates with 𝔼 f(x̄) − min f ≤ ε.

**Complexity.** For d ≥ 2 and 0 < ε ≤ BR/16, the budget is ⌈672² dB²R²/ε²⌉, i.e.

  N = O(d B²R²/ε²) comparisons,

with no logarithmic factor. Here d is the dimension, R the ball radius, B the median bound on sample-utility Lipschitz constants and ε the expected objective accuracy. The theorem assumes no separate Lipschitz constant for f; the proof derives Lip(f) ≤ B.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kovalev–Stonyakin–Gasnikov, [arXiv 2611.19611 v1](https://arxiv.org/abs/2611.19611) (14 Nov 2026, preprint), Thm 2(a), probit model eq. (4). Special case: Z ~ N(0,σ²I) and f M-Lipschitz, which lies in this class with B = M + σ√d because median‖Z‖ ≤ σ√d. | O(C(M/σ)² d²σ²R²/ε²), where the explicit constant (App. B.1) satisfies C(M/σ) ≥ max{c, (M/σ)²}, so the bound is ≳ d²R²(σ² + M⁴/σ²)/ε² → O(dM²R²/ε² + d²σ²R²/ε²) | If σ ≥ M: none, same order. If σ < M: a factor of at least ½(M/σ)²·min{d, (M/σ)²}. Example: σ = M/√d gives d³M²R²/ε² → dM²R²/ε². At σ = 0 their bound is undefined; this one is finite. | Gaussian Z with known σ → any unknown spherical law with only a median-radius condition (atoms, infinite mean, discontinuous induced link). The classes are nested: Gaussian ⊂ spherical. | Known σ, M and inverse-probit link in the updates → only B, R, d, ε needed. Both give an expected objective gap of an averaged point; theirs is anytime via doubling, this one uses a fixed n. | Ball domain only (theirs allows B(c,r) ⊆ Q ⊆ B(c,R)). No strongly convex rate (theirs has d²σ²/(με)). Requires d ≥ 2 and ε ≤ BR/16. f and noise share one envelope B. |
| Lu et al., [arXiv 2608.15050](https://arxiv.org/abs/2608.15050) Thm 2; Saha–Koren–Mansour [ICML 2021](https://proceedings.mlr.press/v139/saha21b.html) (special-case/other model) | Not comparable. Their bit has law ρ(f(x)−f(y)) (known ρ′(0), or a constant flip rate ν), with no ‖x−y‖ scaling. | Not comparable | Incomparable classes: here the induced link is a function of the slope (f(x)−f(y))/‖x−y‖, which is not a fixed function of the gap | — | Their links are differentiable or known; SKM 2021 also needs smoothness |

**Mechanism and reductions.** By rotation invariance, the expected bit-direction 𝔼[sign⟨∇f+Z,u⟩u] is parallel to ∇f. Unit-step projected SGD then gives the rate, once the gain is bounded below by ‖∇f‖/(B√d) using only the median condition (via an antipodal good pair, giving ‖Z‖ ≤ 2B on good draws), and once a jittered secant bound handles nonsmooth f. The uniform-direction sign identity is proof ancestry (Lobanov et al.; normalized comparison GD, Saha et al.). The median-only radial bound and calibration-free secant handling are what Kovalev et al.'s inverse-probit debiasing cannot supply when the link is unknown or discontinuous. I found no standard reduction yielding this bound.

**Lower-bound context.** Kovalev et al. Thm 2(b) gives Ω(d²σ²R²/ε²) on the Gaussian subclass, so the bound is order-optimal there when σ√d ≳ M. The repository's paired [lower bound](../../LongTails/Theorems/SphericalPreferenceLowerBound.lean) states Ω(dB²R²/ε²) for this class; I inspected its statement only, not the construction. On the noiseless subclass Z = 0 (exact comparisons, B-Lipschitz f), cutting-plane-type comparison methods might do much better in ε; I did not check this.

**Search coverage (2026-11-18).** I searched arXiv, PMLR and NeurIPS for dueling, comparison and preference-oracle convex optimization. I read Kovalev et al. (HTML v1; Appendix G lemmas unread), plus the theorem statements of Lu et al. and Kornilov et al. [2502.07923](https://arxiv.org/abs/2502.07923); the latter is first-order sign-SGD and not comparable. I did not independently verify the note's Lobanov (NeurIPS 2024), Saha (ICML 2025) and Chayti citations. The note's description of Kovalev Thm 2 matches the source. Kovalev v1 predates the result's commit (19 Nov 2026) by five days.

**Conclusion**

**Yes: on its overlap with the closest prior theorem the proved complexity is no worse and sometimes better, and the class is much broader.** The strongest baseline is Kovalev–Stonyakin–Gasnikov's probit theorem (Gaussian tastes, known σ). On Gaussian tastes with an M-Lipschitz objective:

| | comparisons for expected gap ε |
|---|---|
| Kovalev et al. Thm 2(a) | ≳ d²R²(σ² + M⁴/σ²)/ε² |
| This result | O(dM²R²/ε² + d²σ²R²/ε²) |

These have the same order when σ ≥ M, and the new bound wins polynomially when σ < M. The theorem also covers σ → 0, where the probit analysis breaks down.

The main gain is scope and information. The respondents' taste law may be any unknown rotation-invariant distribution, including atoms and infinite means. Only a median bound on the sample Lipschitz constant is required, and the method needs no calibration of σ or the link. A link that is unknown and possibly discontinuous blocks the inverse-probit debiasing.

The tradeoffs are a ball-only domain, no strongly convex rate, a fixed horizon, and a single shared envelope B. Whether exact-comparison methods beat this on low-noise subclasses is unchecked. Priority is plausible but recent: the closest paper appeared five days earlier, and my search is not exhaustive.

What can be claimed: a calibration-free expected-gap bound of O(dB²R²/ε²) for nonsmooth convex minimization from one-bit comparisons under unknown spherical random-coefficient noise. It is order-optimal on the Gaussian subclass when σ√d ≳ M.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
