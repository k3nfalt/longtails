# FiniteVarianceGeneralizedAcceleratedConvex: novelty assessment

The [theorem](../../LongTails/Theorems/FiniteVarianceGeneralizedAcceleratedConvex.lean) shows the following for every convex \(f\) on a separable real Hilbert space with differentiable gradient and \(\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|\), under its [setup](../../LongTails/Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean). Given an IID, jointly measurable, unbiased stochastic-gradient oracle with variance at most \(\sigma^2\), the non-restarted, clipped [accelerated algorithm](../../LongTails/Algorithms/RobustGeneralizedAccelerated.lean) returns \(\hat x\) with \(P[f(\hat x)-f^\star>\varepsilon]\le\delta\).

Here \(\|x_0-x^\star\|\le R\) and \(f(x_0)-f^\star\le\Delta\), and \(\varepsilon\) and \(\delta\) are the accuracy and the failure probability. All of these parameters are known to the method. The parameters satisfy \(L_0,R,\Delta,\varepsilon>0\), \(L_1,\sigma\ge0\), and \(\delta<1\). The proved budget counts every pilot and correction sample, two estimates per step, and padding after the stop. With universal constants suppressed, it is

\[
N=O\Big(\Big[1+R\sqrt{\tfrac{L_0}{\varepsilon}}+\log\tfrac{4\Delta+4\varepsilon}{\varepsilon}+\big(L_1R\log\tfrac{4\Delta+4\varepsilon}{\varepsilon}\big)^{2/3}+\tfrac{\sigma^2R^2}{\varepsilon^2}\log^2\tfrac e\delta\Big]\log\frac{e\,(1+L_0R^2/\varepsilon+L_1R+\log(4+4\Delta/\varepsilon))}{\delta}\Big).
\]

All rows count stochastic-gradient calls and assume \(\Delta>\varepsilon\). In the table, \(\lambda=\log(4+4\Delta/\varepsilon)\) and \(\Lambda=\log\frac{e(1+L_0R^2/\varepsilon+L_1R+\lambda)}{\delta}\).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lobanov–Dvinskikh–Gasnikov, [arXiv 2609.33415v1](https://arxiv.org/abs/2609.33415), Thm. 9 and App. C, Eq. (40), preprint dated Sept. 27, 2026 (**prior, by one day**). Applied via my reduction \(H_0=eL_0\), \(H_1=2e^2L_1^2\), \(Q=B(x_0,R)\), \(p=2\), \(\sigma_0=\sigma\), \(\sigma_1=\sigma_2=0\) | Before: \(\big[\lambda+R\sqrt{L_0/\varepsilon}+L_1R\,J+\frac{\sigma^2R^2}{\varepsilon^2}\big]\log\frac{e(1+\lambda)}{\delta}\), where \(J=1+\min\{\log_2\frac\Delta\varepsilon,\log_2^+\frac{L_1^2\Delta}{L_0}\}\). After: \(\big[1+R\sqrt{L_0/\varepsilon}+\lambda+(L_1R\lambda)^{2/3}+\frac{\sigma^2R^2}{\varepsilon^2}\log^2\frac e\delta\big]\Lambda\) | Curvature term \(L_1R\,J\to(L_1R\lambda)^{2/3}\). The gain survives if \(L_1RJ\log\frac{e(1+\lambda)}\delta\ge C\big[R\sqrt{L_0/\varepsilon}+\lambda+(L_1R\lambda)^{2/3}+\frac{\sigma^2R^2}{\varepsilon^2}\log^2\frac e\delta\big]\Lambda\). Example: \(L_0R^2=\varepsilon\), \(\sigma R\le\varepsilon\), \(\Delta=4\varepsilon\), \(\delta=1/2\), \(L_1R=q\to\infty\) gives \(q\to q^{2/3}\log q\). **Worse** elsewhere: about \(\log\frac e\delta\cdot\Lambda/\log\frac{e(1+\lambda)}\delta\) on the noise term, and \(\Lambda/\log\frac{e(1+\lambda)}{\delta}\) on \(R\sqrt{L_0/\varepsilon}\) | \(\mathbb R^d\) → separable Hilbert space; I did not check whether the prior proof is dimension-free | None: both need all parameters, including \(\Delta\), and both return the final point of a run of fixed length | Prior covers a broader class: first-order local \((H_0,H_1)\) smoothness (Hessian class ⊂ it), moments \(p\in(1,2]\), and gradient- and gap-dependent noise. Its ball projection and restarts cost no oracle calls |
| Tyurin, [arXiv 2508.06884v2](https://arxiv.org/abs/2508.06884), Thm. 4.3, ICML 2026 (**prior**). Special case \(\sigma=0\) with exact gradients | Before: \(R\sqrt{L_0/\varepsilon}+L_1R\log\min\{\frac{2L_1^2\Delta}{L_0},\frac{2\Delta}{\varepsilon}\}+\log^+\frac{2\Delta}{L_0R^2}\). After: \([1+R\sqrt{L_0/\varepsilon}+\lambda+(L_1R\lambda)^{2/3}]\Lambda\) | Same \(L_1R\to(L_1R\lambda)^{2/3}\) gain when \(L_1R\) dominates. **Worse** by \(\Lambda\) when \(R\sqrt{L_0/\varepsilon}\) dominates | Exact oracle → stochastic finite variance (not a gain on the overlap) | None | On the overlap the selected method still runs about \(\Lambda\) pilot groups per estimate |
| Repository [light-tail theorem](../../LongTails/Theorems/StochasticGeneralizedAcceleratedConvex.lean), `5d708bd`, Sept. 28, 2026 (**prior**) | Before: \(1+R\sqrt{L_0/\varepsilon}+\lambda+(L_1R\lambda)^{2/3}+\frac{\sigma^2R^2}{\varepsilon^2}\log\frac e\delta\) (it takes a min with a second curvature form). After: the bound in row 1 | Worse by \(\Lambda\), and by \(\log\frac e\delta\cdot\Lambda\) on the noise term | \(\mathbb E\exp(\|g-\nabla f\|^2/\sigma^2)\le e\) → finite variance (a strictly larger class) | None | Pads to the full budget even when \(\Delta\le\varepsilon\) |
| Repository [adaptive theorem](../../LongTails/Theorems/AdaptiveRobustGeneralizedAcceleratedConvex.lean), `02b2cca`, Oct. 5, 2026 (**subsequent**, identical setup) | Never worse in order than this result. Its noise term is \(\frac{\sigma^2R^2}{\varepsilon^2}\log\frac e\delta\) plus lower-order terms, and it drops \(\Lambda\) on the optimization term when \(\delta\) is at least polynomially large | None for this result; it is dominated | None | None | None |

**Reductions and proof ancestry.** The class reduction for row 1 works as follows.
- On \(\|y-x\|\le1/L_1\), the Hessian is at most \(e(L_0+L_1\|\nabla f(x)\|)\).
- A descent step gives \(\|\nabla f\|^2\le2e(L_0+L_1\|\nabla f\|)(f-f^\star)\), and therefore \(L_0+L_1\|\nabla f\|\le2L_0+4eL_1^2(f-f^\star)\). This yields the stated \(H_0,H_1\), whose radius \(r_H<1/L_1\).
- Summing Eq. (40) over the halving phases, with \(\rho_s\propto\rho/(s+1)^2\), gives the formula in row 1.

The shape \(\lceil(L_1R)^{2/3}\rceil\lceil\log_2(2F_0/\varepsilon)\rceil\) comes from deterministic AGMsDR ([Vankov et al., arXiv 2410.10800v3, Thm. 6.2](https://arxiv.org/abs/2410.10800)). That method needs one-dimensional minimizations with an unbounded number \(\nu\) of extra calls, so it is proof ancestry rather than a baseline. Centred clipping descends from [Gorbunov et al., NeurIPS 2020](https://proceedings.neurips.cc/paper_files/paper/2020/file/abd1c782880cc59759f4112fda0b8f98-Paper.pdf). Substituting a clipped, biased estimate into the light-tail proof does not work directly. The repository supplies the extra steps: bias control at both adaptive queries, compensation proportional to the nominal weight, and pathwise accounting of the attempted weights. I found no published stochastic transfer of the \(2/3\) shape.

**Search coverage (2026-10-07 UTC).**
- **Sources checked:** arXiv and proceedings searches. Besides the table sources, I read [ARC-SG](https://arxiv.org/abs/2609.06555) (sub-Gaussian noise, restarted) and [Yu–Hong–Lin, arXiv 2502.11125](https://arxiv.org/abs/2502.11125), whose deterministic term is not accelerated.
- **Unverified:** I read the Lobanov–Dvinskikh–Gasnikov constants through a summarizing fetch, not line by line. The [SNAG appendix](https://openreview.net/pdf?id=AlYT0ZD51A) was inaccessible.
- **Companion-note discrepancies:** the note omits Lobanov–Dvinskikh–Gasnikov. That paper already combines acceleration, curvature linear in \(L_1R\), and an additive noise cost, which contradicts the note's framing of that combination as the contribution. The note's Nguyen–Ene–Nguyen localization row (\(e^{L_1R}\)) is therefore not the strongest baseline.

**Conclusion**

**Partly: it improves only the curvature term, from \(L_1R\) to roughly \((L_1R)^{2/3}\), and only when curvature dominates.**

The strongest prior baseline is Lobanov–Dvinskikh–Gasnikov's Theorem 9 (preprint dated Sept. 27, 2026). It applies to this class through the verified reduction to \((H_0,H_1)\) smoothness.

| | curvature term | noise term |
|---|---|---|
| prior (×\(\log\frac{e(1+\lambda)}{\delta}\)) | \(L_1R\cdot\min\{\log\frac\Delta\varepsilon,\log^+\frac{L_1^2\Delta}{L_0}\}\) | \(\sigma^2R^2/\varepsilon^2\) |
| this result (×\(\Lambda\)) | \((L_1R\log\frac{\Delta}{\varepsilon})^{2/3}\) | \(\frac{\sigma^2R^2}{\varepsilon^2}\log^2\frac e\delta\) |

The gain is about \((L_1R)^{1/3}\) up to logarithms, for example \(q\to q^{2/3}\log q\) when \(L_1R=q\) is large and \(L_0R^2/\varepsilon\), \(\sigma R/\varepsilon\), and \(\Delta/\varepsilon\) are bounded.

The result is worse whenever noise dominates, by roughly \(\log(1/\delta)\cdot\log(L_0R^2/\varepsilon+L_1R)\). It also needs a Hessian bound and \(p=2\), where the prior allows \(p<2\) and gradient-dependent noise. Today it retains no advantage over the repository's own Oct. 5 theorem on the identical setup.

The comparison proves the regime-specific gain. The search did not establish priority for the stochastic \(2/3\) shape, because the deterministic shape is Vankov et al.'s and one source was unread.

What can be claimed is the first checked finite-variance stochastic transfer of the deterministic \((L_1R)^{2/3}\) curvature dependence. It is a modest improvement on a lower-order term, paid for with extra logarithms on the dominant noise term.

**Verdict: LIMITED OR INCREMENTAL NOVELTY** — **Confidence: medium**
