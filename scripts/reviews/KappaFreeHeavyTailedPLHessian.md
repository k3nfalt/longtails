# KappaFreeHeavyTailedPLHessian: κ-free heavy-tailed statistical rate under PL plus a Lipschitz Hessian

[`result`](../../LongTails/Theorems/KappaFreeHeavyTailedPLHessian.lean) covers L-smooth objectives with a ρ-Lipschitz Hessian that satisfy the global μ-PL inequality with an attained minimum on a finite-dimensional Hilbert space. Minimizers need not be isolated. The oracle returns IID unbiased gradients whose centered p-th moment is at most σ^p, with 1 < p ≤ 2. Under these assumptions, SGD driven by a nested-medoid pilot and centered clipping (65 calls per step) returns a uniformly sampled final-window iterate with **E[f(x_out) − f⋆] ≤ ε** ([setup](../../LongTails/Setups/HeavyTailedPLHessian.lean), [algorithm](../../LongTails/Algorithms/HeavyTailedPLHessian.lean)). The updates need L, μ, ρ, σ, p, ε and Δ. The result was introduced in commit 65ec22e on 2026-10-30.

**Complexity.** Here Δ ≥ f(x₀) − f⋆, q = p/(2(p−1)), and C_p = 2^{(128/p+27)q}. The theorem's budget is 65(K+1) calls, with K read off the Lean `budget`:

$$N=O\Big(\Big[(L/\mu)^{5/4}+C_p\Big(\frac{\sigma^2}{\mu\varepsilon}+\frac{(L/\mu)^{5/2}\sigma^2\rho^2}{\mu^4}\Big)^{q}\Big]\log\Big(2+\frac{\sqrt{L/\mu}\,\Delta}{\varepsilon}\Big)\Big).$$

Below, κ = L/μ, Q = (σ²/(με))^q, and ℓ = log(2+√κΔ/ε).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ou–Wang, [arXiv 2609.03990](https://arxiv.org/abs/2609.03990) v1 3 Sep, v2 26 Sep 2026, under review, Thm 4.3. Prior. Direct competitor on a broader class (smooth PL, no Hessian assumption). | Õ(κ log(Δ/ε) + κQ)·log(κ/δ·log(Δ/ε)) w.p. 1−δ → above | Statistical term κQ → Q·ℓ, a gain of ≈ κ/ℓ. This needs Q ≫ κ^{1/4}ℓ and ε ≪ μ³κ^{2(p−1)/p−5/2}/ρ², i.e. ε ≪ μ³/(κ^{3/2}ρ²) at p=2. Their Thm 3.1 shows Ω(κQ) is unavoidable on smooth PL in dimension ≳ κ²(Δ/ε+Q). | None; the class is narrower. | Worse: last iterate w.p. 1−δ → expectation of a random window iterate. | Adds a Lipschitz Hessian and needs ρ. Deterministic term κ log → κ^{5/4}ℓ. Adds an ε-independent ρ-term. Theirs allows mirror-PL on convex domains and non-IID conditional oracles. |
| Ou–Wang, same paper, Thm 5.3 / D.1, fixed dimension. Prior. Special-case baseline (fixed d, constants depend on d). | d=1: Õ(log + Q). d=2: Õ(κ^{2/3} log + Q). d=3 or d−1 ≤ p/(p−1): Õ(κ^{(d−1)/2} log + Q). All w.p. 1−δ → above | None on the statistical term in those dimensions (both are κ-free up to polylog κ). Worse for d ≤ 2 in the deterministic term. In d−1 > p/(p−1) their stochastic term carries κ^{(d−1−p/(p−1))/2}, which this result removes. | Fixed d with d-dependent constants → dimension-free bound. | Same output loss as above. | Theirs needs no Hessian assumption. |
| Sadiev et al., ICML 2023, [arXiv 2302.00999](https://arxiv.org/abs/2302.00999), Thm 3.3 (R-clipped-SSTM). Prior. Strongly convex special case (assumptions only on a ball around x⋆). | Õ(√κ + Q) w.p. 1−β → above | Worse on this overlap: √κ → κ^{5/4}ℓ, plus the ρ-term and the log on Q. | Unique strongly convex minimizer → PL with non-isolated minimizers. | Same output loss. | — |
| Repository [KappaFreeSgdPLHessian](../../LongTails/Theorems/KappaFreeSgdPLHessian.lean), 2026-10-17. Prior, unpublished. Special-case baseline (p=2 with kurtosis K). | (κ^{5/4} + Kκ^{3/2}σ²ρ²/μ⁴ + σ²/(με))ℓ → at p=2: (κ^{5/4} + Cκ^{5/2}σ²ρ²/μ⁴ + Cσ²/(με))ℓ | Worse in the ρ-term when K ≲ κ; a gain only when K ≫ κ. | Fourth moment Kσ⁴ → none. Variance → p-th moment with p < 2 (allows infinite variance). | None (both use a window iterate). | 65 calls per step; huge C_p as p→1. |

**Reduction check and ancestry.** The heavy-tailed results cited above do not yield this bound. Feeding the clipped estimator into the sibling theorem fails because that theorem needs an unbiased oracle with a fourth moment. Generic biased-SGD under PL keeps the κ factor. The new step is absorbing the clipping bias into the distance-plus-gap potential by balancing B² = μηV, and I could not reduce it to a published theorem. The ingredients are inherited: the medoid pilot and clipping are the same robust-estimation mechanism as Ou–Wang's Lemma C.4, local aiming comes from Liu et al. ([arXiv 2306.02601](https://arxiv.org/abs/2306.02601), Thm 2.2), and the global potential comes from the repository sibling.

**Search coverage (2026-10-30).** I read Ou–Wang v2 (Thms 3.1, 4.3, 5.3, D.1–D.2) and Sadiev et al. (Thm 3.1 cases 2/4, Thm 3.3). I ran searches on heavy-tailed PL, clipping, and non-isolated minima, and found no prior κ-free heavy-tailed bound in arbitrary dimension under PL. The Masiha et al. lower bound and the local-manifold papers were not re-read; I relied on the repository's sibling review for them. The companion note matches the Lean budget. It omits the strongly convex R-clipped-SSTM row and the fact that Ou–Wang's d ≤ 3 bounds are already κ-free without Hessian regularity. I did not check whether Ou–Wang's Thm 3.1 hard instances have a bounded Hessian-Lipschitz constant.

**Conclusion**

**Yes: for small ε in high dimension, the proved bound beats the best applicable smooth-PL heavy-tailed method by about a factor κ.** The strongest baseline is Ou–Wang's centered-clipped method, which costs κ log(Δ/ε) + κQ; their own lower bound shows that cost is unavoidable for smooth PL alone in large dimension. Adding a Lipschitz Hessian lets this result pay the statistical cost only once:

| | calls (polylogs aside) |
|---|---|
| Ou–Wang Thm 4.3 | κ log(Δ/ε) + κ(σ²/(με))^q |
| this result | [κ^{5/4} + (σ²/(με))^q + (κ^{5/2}σ²ρ²/μ⁴)^q]·ℓ |

The gain survives once (σ²/(με))^q ≫ κ^{1/4}ℓ and ε ≪ μ³κ^{2(p−1)/p−5/2}/ρ². For example, with p=2, μ=σ=ρ=Δ=1 and ε=κ⁻³, the cost drops from κ⁴ to κ³ log κ. The result loses for moderate ε, on strongly convex instances (where Sadiev et al. get √κ + Q), and in dimensions d ≤ 3 (where Ou–Wang are already κ-free without any Hessian assumption). Its guarantee is only an expectation for a random window iterate.

The comparison proves the gain. Priority is less certain. Within the repository, the step beyond the p=2 bounded-kurtosis sibling consists of swapping in a known robust estimator and controlling its bias, which is narrower. Even so, I found no published κ-free heavy-tailed PL bound in arbitrary dimension. What can be claimed is removing κ from the heavy-tailed statistical term, uniformly in dimension and without a fourth moment, under PL plus a Lipschitz Hessian.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
