# StochasticGeneralizedAcceleratedConvex: novelty assessment

The [theorem](../../LongTails/Theorems/StochasticGeneralizedAcceleratedConvex.lean) ([setup](../../LongTails/Setups/StochasticGeneralizedSmoothAndConvex.lean), [algorithm](../../LongTails/Algorithms/StochasticGeneralizedAccelerated.lean)) proves that a batched, damped, non-restarted accelerated method returns a measurable point $\hat x$ with $\Pr[f(\hat x)-f^\star>\varepsilon]\le\delta$. Here $f$ is a convex function on a separable Hilbert space with differentiable gradient and $\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|$. The oracle is IID, unbiased and norm-sub-Gaussian: $\mathbb E\exp(\|g-\nabla f\|^2/\sigma^2)\le e$.

**Parameters.** $R\ge\|x_0-x^\star\|$ and $\Delta\ge f(x_0)-f^\star$. The algorithm is given $L_0,L_1,R,\Delta,\varepsilon,\sigma,\delta$ and uses no projections, function values or restarts. It returns the accelerated $x$-sequence at its stopping time, $A_k\ge16R^2/\varepsilon$. Batch sizes are $\max\{1,\lceil2^{20}\sigma^2a_k\log(e/\delta)/\varepsilon\rceil\}$, and the budget counts every sample plus padding. With $\ell:=\log(4+4\Delta/\varepsilon)$, the proved budget is $0$ if $\Delta\le\varepsilon$ and otherwise

$$
O\!\Big(1+\sqrt{L_0R^2/\varepsilon}+\min\{\lceil(L_1R)^{2/3}\rceil\ell,\ \ell+(L_1R\ell)^{2/3}\}+\sigma^2R^2\log(e/\delta)/\varepsilon^2\Big).
$$

All rows use the same units (stochastic-gradient samples) and the same criterion (an objective gap of at most $\varepsilon$ with probability at least $1-\delta$). Õ marks polylogarithmic factors suppressed by the cited theorem.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Gaash–Levy–Carmon, clipped SGD, [NeurIPS 2025; arXiv 2502.16492v2, Thm 1](https://arxiv.org/html/2502.16492v2) (prior) | $O\big((L_0R^2/\varepsilon+L_1^2R^2)\log\frac T\delta+\frac{\sigma^2R^2}{\varepsilon^2}\log^3\frac T\delta\big)$, with $T$ the resulting count → the bound above | When $\sigma^2\log(e/\delta)\le L_0\varepsilon$, the optimization term improves from $L_0R^2/\varepsilon$ to $\sqrt{L_0R^2/\varepsilon}$. The startup term improves from $L_1^2R^2$ to $(L_1R\ell)^{2/3}+\ell$. In the noise-dominated regime the gain is only $\log^3(T/\delta)\to\log(e/\delta)$. | Finite-dimensional space → separable Hilbert space (the prior proof does not appear to depend on dimension) | Averaged unclipped iterates → stopped accelerated iterate; same parameter knowledge, apart from $\Delta$ | Current method needs $\Delta$ (enters only through $\ell$). The prior method uses two samples per step and no batching. |
| Dvinskikh–Gasnikov–Lobanov–Latypov, ARC-SG, [arXiv 2609.06555v1, 6 Sep 2026, Thm 1/3](https://arxiv.org/html/2609.06555) (prior preprint, same light-tailed $(L_0,L_1)$ model) | Õ$\big(1+L_1R+(1+L_1R)^{1/2}\sqrt{L_0R^2/\varepsilon}+(1+L_1R)^3\frac{\sigma^2R^2}{\varepsilon^2}+(1+L_1R)^3\frac{\sigma^2L_1^2}{L_0^2}\big)$, with gap certificate $\Delta$ → the bound above | Removes the factor $(1+L_1R)^3$ on the noise term and $(1+L_1R)^{1/2}$ on the optimization term, plus the burn-in and polylog factors. The gain is polynomial whenever $L_1R\gg1$. | Projection onto a ball → none; $\mathbb R^d$ → Hilbert space | None: both return a certified final point with known parameters | Prior curvature term is $L_1R$ times polylog factors. The current $\ell+(L_1R\ell)^{2/3}$ can be larger only through logarithms when $\ell^2\gtrsim L_1R$. |
| Lobanov–Dvinskikh–Gasnikov, RCSAG, [arXiv 2609.33415v1, 27 Sep 2026, Thm 9](https://arxiv.org/html/2609.33415) (contemporaneous: posted one day before the repository commit). Reduction: $H_0=O(L_0)$, $H_1=O(L_1^2)$, $Q=B(x_0,R)$, $p=2$, $\sigma_0=\sigma$ | Õ$\big(\ell+R\sqrt{L_0/\varepsilon}+L_1R\min\{\ell,\log(2+L_1^2\Delta/L_0)\}+\sigma^2R^2/\varepsilon^2\big)$, with logs in $1/\delta$ and the phase count → the bound above | Curvature term $L_1R\cdot J\to(L_1R\ell)^{2/3}+\ell$. Example: $\sigma=0$, $\Delta=L_0R^2$, $\varepsilon=L_0R^2/t^{4/3}$ with $t=L_1R\to\infty$ gives about $t\log t$ → $t^{2/3}\log^{2/3}t$. Otherwise the terms have the same order. | None: the prior covers a broader noise class | None | The prior allows finite $p$-th moments ($1<p\le2$) and gradient- or gap-dependent noise, and needs no batching. It needs projections and restarts. It can win by logarithms when $L_1^2\Delta\lesssim L_0$ and $\ell^2\gg L_1R$. |

**Reduction check.** Freezing curvature on a radius-$R$ ball and running batched AC-SA (Ghadimi–Lan) gives a factor $e^{O(L_1R)}$, so a simple substitution does not produce this bound. Proof ancestry:
- The deterministic curvature term already appears in [Vankov et al., ICLR 2025, Thm 6.2](https://arxiv.org/pdf/2410.10800). That result needs a line search.
- The repository's [GeneralizedAcceleratedConvex](../../LongTails/Theorems/GeneralizedAcceleratedConvex.lean) (25 Sep) proves the same term with gradients only.
- Damped Monteiro–Svaiter acceleration comes from Carmon et al. (NeurIPS 2022).
- Batch sizes proportional to $a_k/\varepsilon$ that sum to $\sigma^2R^2/\varepsilon^2$ are the standard batched similar-triangles method (STM).

What is new is extending this to noisy curvature tests and damped attempts, charging their batches to nominal weights with a single $\log(1/\delta)$. Whether that step is original is unchecked.

**Search coverage.** Searches were run on 2026-10-07 UTC and covered arXiv, the ICLR/NeurIPS proceedings and forward citations. The checked sources include Yu et al. (arXiv 2502.11125, Thm 2: an unaccelerated $O(1/T)$ optimization term), Gorbunov et al. (stochastic results for gradient descent only), Lobanov–Gasnikov (2501.18198) and Tyurin (ICML 2026, deterministic). The prior public ICLR 2026 submission ["Convergence analysis of Nesterov's accelerated gradient descent under relaxed assumptions"](https://openreview.net/forum?id=AlYT0ZD51A) was inaccessible (HTTP 403). ARC-SG reports that it gives a high-probability rate $\tilde O(T^{-2}+\sqrt{(A+B+C)/T})$ for this model, "parameter factors suppressed". There is no companion note. Git introduces the theorem in `5d708bd` (2026-09-28). The [earlier repository review](../reviews/StochasticGeneralizedAcceleratedConvex.md) mentions ARC-SG only in its search coverage, without comparing complexities. I ran no Lean build and no axiom audit.

**Conclusion**

**The proved bound beats every prior bound I could verify, but one possibly decisive prior result could not be checked.** Under identical light-tailed $(L_0,L_1)$ assumptions, the strongest checked prior result is ARC-SG (6 Sep 2026):

| | optimization | noise |
|---|---|---|
| ARC-SG | $(1+L_1R)^{1/2}\sqrt{L_0R^2/\varepsilon}+L_1R$ | $(1+L_1R)^3\sigma^2R^2/\varepsilon^2$ (+burn-in, polylogs) |
| This result | $\sqrt{L_0R^2/\varepsilon}+\ell+(L_1R\ell)^{2/3}$ | $\sigma^2R^2\log(e/\delta)/\varepsilon^2$ |

So the proved gain is polynomial in $L_1R$ whenever $L_1R\gg1$; ARC-SG can be better only by logarithmic factors. Against unaccelerated clipped SGD (Gaash–Levy–Carmon), the gain is $L_0R^2/\varepsilon\to\sqrt{L_0R^2/\varepsilon}$ when $\sigma^2\log(e/\delta)\le L_0\varepsilon$. Against the contemporaneous RCSAG, the gain is a curvature term of $(L_1R\ell)^{2/3}$ instead of $L_1R\cdot\ell$. RCSAG, however, covers heavier-tailed noise.

These comparisons establish a gain over the checked baselines; they do not establish priority. An earlier public ICLR 2026 submission reportedly reaches the same accuracy exponents in a broader model. Its parameter factors, which would decide whether it already matches this bound, could not be read.

What can be claimed: a batched accelerated method without restarts or projections, with explicit additive $L_1$ dependence and a single $\log(1/\delta)$. It improves on the verified prior bounds in the regimes above. Whether the result is new to the literature depends on that unread submission.

**Verdict: INCONCLUSIVE**
**Confidence: medium**
