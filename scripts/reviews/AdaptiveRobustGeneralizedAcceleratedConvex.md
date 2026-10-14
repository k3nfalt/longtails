# AdaptiveRobustGeneralizedAcceleratedConvex: novelty assessment

The [theorem](../../LongTails/Theorems/AdaptiveRobustGeneralizedAcceleratedConvex.lean) makes the following guarantee in its [setup](../../LongTails/Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean). Consider a convex, twice-differentiable \(f\) on a separable real Hilbert space with \(\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|\), and an IID, jointly measurable, unbiased stochastic-gradient oracle with variance at most \(\sigma^2\) and no higher moments. Then the final iterate \(\hat x\) of the [algorithm](../../LongTails/Algorithms/AdaptiveRobustGeneralizedAccelerated.lean) satisfies \(P[f(\hat x)-f(x^\star)>\varepsilon]\le\delta\). The algorithm is a non-restarted damped accelerated method with majority-vote-centred clipped estimates.

Parameters: \(L_0>0\) and \(L_1\ge0\) are the curvature constants. A minimizer satisfies \(\|x_0-x^\star\|\le R\) and \(f(x_0)-f^\star\le\Delta\). \(\sigma\ge0\) is the noise level, \(\varepsilon>0\) the accuracy, and \(0<\delta<1\) the failure probability. All are known to the method. The budget counts every pilot and correction sample (two estimates per step) and the padding after the deterministic stop at accumulated weight \(16R^2/\varepsilon\). I loosened the proved ceiling only by universal constants, using \(S'\ge\ell\sqrt V\) and \(\log(e+u/c)\ge\log(e+u)/(1+\log c)\). The result is

\[
\begin{aligned}
K=O\Big(&\Big[1+R\sqrt{\tfrac{L_0}{\varepsilon}}+\tfrac{\sigma R}{\varepsilon}\log\tfrac e\delta+\log(4+\tfrac{4\Delta}{\varepsilon})+\big(L_1R\log(4+\tfrac{4\Delta}{\varepsilon})\big)^{2/3}\Big]
\Big[1+\frac{\log\frac{e\,M}{\delta}}{\log\!\Big(e+\frac{\varepsilon^2\big(1+R\sqrt{L_0/\varepsilon}+\log(4+4\Delta/\varepsilon)+(L_1R\log(4+4\Delta/\varepsilon))^{2/3}\big)\sqrt{M}}{\sigma^2R^2\log^2(e/\delta)}\Big)}\Big]\\
&+\tfrac{\sigma^2R^2}{\varepsilon^2}\log\tfrac e\delta+\tfrac{\sigma R}{\varepsilon}\log\tfrac e\delta\,\log\tfrac{e\,M}{\delta}\Big),
\qquad M=1+\tfrac{L_0R^2}{\varepsilon}+L_1R+\log(4+\tfrac{4\Delta}{\varepsilon})+\tfrac{\sigma^2R^2}{\varepsilon^2}\log^2\tfrac e\delta .
\end{aligned}
\]

Here \(M\) only abbreviates the explicit expression shown. The proved bound is the formula above; the following simplification is a consequence I spot-checked from the companion's Corollary 1 and is not formalized. If \(\delta\ge(e+W)^{-c}\), where \(W=1+R\sqrt{L_0/\varepsilon}+\log(4+4\Delta/\varepsilon)+(L_1R\log(4+4\Delta/\varepsilon))^{2/3}\), then \(K=O_c\big(W+\tfrac{\sigma^2R^2}{\varepsilon^2}\log\tfrac e\delta\big)\).

The comparisons below use the same units: stochastic-gradient calls for \(P[\text{gap}>\varepsilon]\le\delta\). Universal constants are dropped, \(\Delta>\varepsilon\), and "regime" means \(\delta\ge(e+W)^{-c}\).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv 2609.33415v1, Thm. 9, App. B–C](https://arxiv.org/html/2609.33415v1), Sept. 27, 2026 preprint (**prior**). Reduction: \(H_0=eL_0\), \(H_1=\tfrac54eL_1^2\), \(Q=B(x_0,R)\), \(p=2\), \(\sigma_0=\sigma\), \(\sigma_1=\sigma_2=0\) | Before: \((\lceil\log_2\frac\Delta\varepsilon\rceil+R\sqrt{L_0/\varepsilon}+L_1R\,\min\{\lceil\log_2\frac\Delta\varepsilon\rceil,\lceil\log_2^+\frac{cL_1^2\Delta}{L_0}\rceil\}+\frac{\sigma^2R^2}{\varepsilon^2})\log\frac{e(1+\log(\Delta/\varepsilon))}{\delta}\). After (regime): \(1+R\sqrt{L_0/\varepsilon}+\log(4+\frac{4\Delta}\varepsilon)+(L_1R\log(4+\frac{4\Delta}\varepsilon))^{2/3}+\frac{\sigma^2R^2}{\varepsilon^2}\log\frac e\delta\) | (i) Speedup \(\approx\log(e/\delta)\) when \(R\sqrt{L_0/\varepsilon}\) dominates. Example: \(\delta=\varepsilon/(L_0R^2)\) and \(\sigma^2R^2\log(e/\delta)/\varepsilon^2\le R\sqrt{L_0/\varepsilon}\). (ii) Curvature term \(L_1R\log\frac\Delta\varepsilon\log\frac e\delta\to(L_1R\log\frac\Delta\varepsilon)^{2/3}\) when \(L_1^2\varepsilon\ge cL_0\). The noise term has the same order. At constant \(\delta\), gain (i) is only a \(\log\log(\Delta/\varepsilon)\) factor. | \(\mathbb R^d\) → separable Hilbert space; I did not check whether their proof is dimension-free | None: both need all parameters, including \(\Delta\), and both return a final point | Prior allows \(p\in(1,2]\), gradient- and gap-dependent noise, and first-order local smoothness; this result needs a Hessian bound and \(p=2\). **Worse** for tiny \(\delta\): \((\sigma R/\varepsilon)\log^2(e/\delta)\) can exceed the prior total. Example: \(\sigma R/\varepsilon=L_0R^2/\varepsilon=1\), \(\Delta=2\varepsilon\), \(L_1=0\), \(\delta=e^{-100}\), worse by a factor of about \(\log(e/\delta)/4\). The prior's projection onto a ball and its restarts cost no extra oracle calls. |
| Nguyen–Ene–Nguyen, [arXiv 2304.01119v2, Thm. 4.1](https://arxiv.org/html/2304.01119v2), Apr. 2023 (**prior**). Special case \(L_1=0\), with \(\Delta\) replaced by \(\min\{\Delta,L_0R^2/2\}\) | Before: \(R\sqrt{L_0/\varepsilon}\log\frac e\delta+\frac{\sigma^2R^2}{\varepsilon^2}\log\frac e\delta\) (from \(T\) with both terms of their bound \(\le\varepsilon/6\), \(p=2\), Euclidean mirror map). After (regime \(\delta\ge(e+L_0R^2/\varepsilon)^{-c}\)): \(1+R\sqrt{L_0/\varepsilon}+\frac{\sigma^2R^2}{\varepsilon^2}\log\frac e\delta\) | \(\log(e/\delta)\) factor on the \(R\sqrt{L_0/\varepsilon}\) term, in the same regime as (i) above. None at constant \(\delta\). | \(L_1=0\) → \(L_1\ge0\); but row 1 already covers \(L_1>0\) | None: both use an accelerated-sequence point and known parameters | Prior needs no \(\Delta\), allows \(p<2\) and mirror geometries, and needs no second derivatives. Same tiny-\(\delta\) loss as row 1. |
| Repository [finite-variance theorem](../../LongTails/Theorems/FiniteVarianceGeneralizedAcceleratedConvex.lean), `c7f1583`, Sept. 28, 2026; same setup | Before: \([W+\frac{\sigma^2R^2}{\varepsilon^2}\log^2\frac e\delta]\log\frac{e(1+L_0R^2/\varepsilon+L_1R+\log(4+4\Delta/\varepsilon))}{\delta}\). After: the formula above | The noise term loses a factor \(\log\frac e\delta\cdot\log\frac{eM}{\delta}\). In the regime, the outer logarithm on \(W\) is removed. Never worse in order (the companion's argument, which I spot-checked). | None | None | None |

**Reductions and proof ancestry.** I checked the reduction for row 1. A local Taylor bound on \(\|y-x\|\le1/L_1\) together with \(\|\nabla f\|^2\le2e(L_0+L_1\|\nabla f\|)(f-f^\star)\), which follows from one descent step, gives \(L_0+L_1\|\nabla f\|\le c(L_0+L_1^2(f-f^\star))\). Their phase sum puts \(\log(\pi^2(s+1)^2/\rho)\) on every term. Standard routes do not reproduce the selected bound:
- A per-step median-of-means at confidence \(\delta/T\) puts \(\log(T/\delta)\) on every step.
- proxBoost needs strong convexity or regularization, which adds logarithms.

The new mechanism has three parts: a pilot group count \(\lceil 28H/\log(4/y)\rceil\) that adapts to each step's noise-to-radius ratio, a concavity charging inequality, and the curvature floor \(L_0+\sigma^2\log^2(e/\delta)/\varepsilon\). The damped acceleration and the \((L_1R\log)^{2/3}\) shape come from the repository's earlier theorems; that ancestry traces to Carmon et al., NeurIPS 2022. Centred clipping descends from [Gorbunov et al., NeurIPS 2020](https://arxiv.org/abs/2005.10785) and median-of-means from Minsker and Hsu–Sabato. The polynomial curvature gain in row 1 was therefore already in the September 28 theorem; what this theorem adds is the confidence-logarithm gain.

**Search coverage (2026-10-07 UTC).** I searched arXiv and proceedings and read theorem statements from LDG, NEN, Sadiev et al. ([ICML 2023, Thm. 3.2](https://arxiv.org/html/2302.00999v2): \((\sqrt{L_0R^2/\varepsilon}+\sigma^2R^2/\varepsilon^2)\log(K/\delta)\), dominated by NEN), and He–Li–Lu ([2510.11676v2](https://arxiv.org/html/2510.11676v2): polynomial in \(1/\delta\), bounded domain). I also checked:
- [Chezhegov et al. v3](https://arxiv.org/abs/2505.20817), Sept. 29, 2026: non-accelerated.
- [ARC-SG](https://arxiv.org/abs/2609.06555): sub-Gaussian noise.
- [Puchkin et al.](https://arxiv.org/abs/2311.04161): structured noise densities.

None is a direct competitor. The theorem was introduced in `02b2cca` on 2026-10-05, and all table sources predate it. I found no subsequent work. I read LDG's per-phase constants through a summarizing fetch, not line by line.

Discrepancies in the companion note:
- It cites NEN as "Nguyen, Ene, Nguyen, NeurIPS 2023" with an arXiv link; the NeurIPS version has four authors.
- Its optimality claim (Corollary 2) and its lower bounds are not formalized. I checked the two-point \(\Omega(\sigma^2R^2\log(1/\delta)/\varepsilon^2)\) construction by hand.

I ran no build or axiom audit.

**Conclusion**

**Yes, but only by a logarithmic factor: the confidence price on the optimization term is removed when \(\delta\) is polynomially small.**

The strongest prior baseline is Lobanov–Dvinskikh–Gasnikov's Theorem 9, which applies to this class by a verified reduction. In the \(L_1=0\) special case, it and Nguyen–Ene–Nguyen give

| | optimization term | noise term |
|---|---|---|
| prior | \(R\sqrt{L_0/\varepsilon}\,\log(e/\delta)\) | \(\frac{\sigma^2R^2}{\varepsilon^2}\log(e/\delta)\) |
| this result, \(\delta\ge(e+W)^{-c}\) | \(R\sqrt{L_0/\varepsilon}\) | \(\frac{\sigma^2R^2}{\varepsilon^2}\log(e/\delta)\) |

At \(L_1=0\) this matches the classical lower bounds up to constants. The speedup is about \(\log(1/\delta)\), for example at \(\delta=\varepsilon/(L_0R^2)\) when the optimization term dominates. There is no gain at constant \(\delta\).

The result loses when \(\delta\) is exponentially small and the problem is otherwise easy: an extra \((\sigma R/\varepsilon)\log^2(e/\delta)\) term makes it worse than the prior bound. It is also narrower than LDG: it needs a Hessian bound and finite variance, while LDG allows \(p<2\) moments and gradient-dependent noise. Its larger curvature gain over LDG, \(L_1R\log\to(L_1R\log)^{2/3}\), was already proved in the repository's September 28 theorem.

The comparison establishes the gain against every checked method. The search found no earlier finite-variance accelerated bound with this confidence dependence, but that does not establish priority. What can be claimed is the first checked finite-variance, high-probability accelerated guarantee that matches the light-tailed complexity, and hence optimality at \(L_1=0\), for \(\delta\ge(e+W)^{-c}\). It rests on a non-routine adaptive median-of-means mechanism.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED** — **Confidence: medium**
