# Nonlinear accelerated method under bounded temporal discrepancy: novelty assessment

The [theorem](../../LongTails/Theorems/NonlinearTemporalAcceleration.lean), with its [setup](../../LongTails/Setups/HessianLipschitzTemporalDiscrepancy.lean) and [algorithm](../../LongTails/Algorithms/NonlinearTemporalAccelerated.lean), proves the following. A two-phase accelerated method makes a batched warm-up run and then an unbatched run, and outputs a tail average $\bar x$. For every seed, $f(\bar x)-f(x_*)\le\varepsilon$. The theorem covers every finite-dimensional $C^2$ objective that is $\mu$-strongly convex, $L$-smooth and $M$-Hessian-Lipschitz, with $f(x_0)-f_*\le\Delta$. Call $k$ returns $\nabla f(x)+e_k$, where the error sequence is hidden, query-independent and seed-independent, and satisfies $\sup_n\|\sum_{k<n}e_k\|\le D$.

**Proved budget:** zero calls if $\Delta\le\varepsilon$; otherwise

$$O\Big(\big[\sqrt{L/\mu}\,(1+MD/\mu^2)+D/\sqrt{\mu\varepsilon}+1\big]\log\big(2+\Delta/\varepsilon+M^2\Delta/\mu^3\big)\Big)$$

gradient calls. This counts every warm-up batch call and every padding call. The parameters $L,\mu,M,D,\Delta,\varepsilon,x_0$ must all be known, and they enter both the updates and the stopping rule. When $M=0$ the objective is quadratic and the warm-up is skipped. When $D=0$ the result is plain acceleration with no novelty.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Cohen–Diakonikolas–Orecchia, ICML 2018](https://proceedings.mlr.press/v80/cohen18a/cohen18a.pdf), AGD+ Lemma 3.2 and Eq. (3.2), combined with restarts and consecutive-call batching (reduction below) | $O(\sqrt{L/\mu}[\log(2+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon}]+1)$ → the budget above | The noise term drops from $\sqrt{L/\mu}\,D/\sqrt{\mu\varepsilon}$ to $D/\sqrt{\mu\varepsilon}$, up to the logarithm $\ell=\log(2+\Delta/\varepsilon+M^2\Delta/\mu^3)$. The speedup is about $\sqrt{L/\mu}/\ell$ when $\sqrt{L/\mu}\ge C\ell$, $D\ge C\ell\sqrt{\mu\varepsilon}$ and $M\sqrt\varepsilon\,\ell\le\mu^{3/2}/C$ | None. The reduction already covers all $L$-smooth strongly convex $f$ | None. Both need $D,\Delta,\varepsilon$; the reduction outputs a restart iterate, the selected method a tail average | Requires $C^2$ with an $M$-Lipschitz Hessian and a known $M$. Adds a $\sqrt{L/\mu}\,MD/\mu^2$ term and the extra log factor $\ell$. It is worse when $M\sqrt\varepsilon\,\ell\gg\mu^{3/2}$, or when $D\lesssim\sqrt{\mu\varepsilon}\log(2+\Delta/\varepsilon)$ (same order up to $\ell$) |
| Repository [quadratic result](../../LongTails/Theorems/TemporalAcceleratedQuadratic.lean) (2026-09-24); a [Schmidt–Le Roux–Bach](https://arxiv.org/pdf/1109.2415v2) Prop. 4 dilation reduction gives the same order. Applies only on the $M=0$ overlap | $O(1+\sqrt{L/\mu}\log(2+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon})$ → $O((\sqrt{L/\mu}+D/\sqrt{\mu\varepsilon}+1)\log(2+\Delta/\varepsilon))$ | Worse: an extra $\log(2+\Delta/\varepsilon)$ factor on the noise term | Quadratic → Hessian-Lipschitz nonlinear objectives (a strict enlargement) | None | The dilation trick is exact only for affine gradients and fails for nonlinear $f$. The quadratic theorem also covers Hilbert spaces |

**Reduction check (derived here).** Batching $b$ consecutive calls at one query point gives gradient error at most $2D/b$. Consider AGD+ restricted to a ball of radius $r$ around the current point that contains $x_*$. With gradient error $\delta$, its gap after $N$ steps is $O(Lr^2/N^2+\delta r)$. Choose $N\approx8\sqrt{L/\mu}$ and $b\approx64D/(\mu r)$, then halve $r$ from $\sqrt{2\Delta/\mu}$ down to order $\sqrt{\varepsilon/\mu}$. Summing over all stages gives the first row's cost, and no Hessian assumption is needed.

Rescaling and batching therefore do not produce the selected bound. A query-independent change of variables $z_k=x_k+\eta S_k$ just moves the error into the evaluation point, where its first-order effect does not cancel. The new step is the nonlinear stability analysis in [NonlinearTemporalConvergence](../../LongTails/Proofs/NonlinearTemporalConvergence.lean). It splits the response to cancelling errors into a linearised part, which telescopes, and a quadratic Hessian remainder of order $M$. The remainder is controlled after a batched warm-up brings the iterate within distance $\mu/M$ of the minimizer.

Proof ancestry: Nesterov's energy potential and summation by parts. [Gao et al., arXiv 2503.08427 v2](https://arxiv.org/abs/2503.08427) (2025-03-29) gives an error-feedback cumulative-error potential; I did not re-derive its specialization to this setup. The [obstruction](../../LongTails/Proofs/TemporalNonlinearObstruction.lean) applies only to the unbatched method on a non-$C^2$ objective. It is not a lower bound showing $M$ is necessary.

**Lower-bound sanity check (derived here).** Take $f=\mu x^2/2$, with replies carrying a constant error $D/n$ for $n$ calls. These replies match exact replies for the objective shifted by $D/(\mu n)$. So every method needs $n\ge D/(2\sqrt{2\mu\varepsilon})$. Together with the classical high-dimensional $\Omega(\sqrt{L/\mu}\log(\Delta/\varepsilon))$, the selected noise term is optimal up to $\ell$. The $MD/\mu^2$ term has no matching lower bound.

Search coverage (2026-10-07 UTC): arXiv, ICML, NeurIPS and journal searches on inexact and noise-robust acceleration, cumulative and telescoping errors, anticorrelated and linearly correlated noise, and Markov noise.
- [Koloskova et al.](https://arxiv.org/pdf/2302.01463v3) (NeurIPS 2023, v3 2024-01-15) studies GD with noise $BZ$, where $Z$ is i.i.d. Gaussian, and gives no accelerated deterministic bound.
- [Beznosikov et al.](https://arxiv.org/abs/2305.15938) (NeurIPS 2023) assumes ergodic Markov noise. A periodic or arbitrary bounded-partial-sum sequence does not satisfy that assumption.
- The ICML text was read through ar5iv; the constants were not rechecked against the proceedings PDF.

Git introduces this result in `abcd78c` (2026-09-28). No companion Markdown note exists, and no subsequent result covering the same setup was found. No build or axiom audit was run.

**Conclusion**

**Yes: when noise dominates and the problem is ill-conditioned, the proved total complexity beats the strongest applicable baseline I found.** That baseline is restarted AGD+ (Cohen–Diakonikolas–Orecchia 2018) with batching. It handles every smooth strongly convex objective, but it pays the condition number on the noise term:

| | noise term | other terms |
|---|---|---|
| batched AGD+ | $\sqrt{L/\mu}\,D/\sqrt{\mu\varepsilon}$ | $\sqrt{L/\mu}\log(\Delta/\varepsilon)$ |
| this result | $D\,\ell/\sqrt{\mu\varepsilon}$ | $\sqrt{L/\mu}(1+MD/\mu^2)\,\ell$ |

For example, with $\mu=M=D=\Delta=1$ and $L=1/\varepsilon$, the cost falls from about $\varepsilon^{-1}$ to $\varepsilon^{-1/2}\log(1/\varepsilon)$. The price is a Lipschitz Hessian with a known $M$. The result loses when $M\sqrt\varepsilon\gg\mu^{3/2}$, when noise is small, and on quadratics, where an existing reduction is a log factor better.

The noise term is within a log factor of a simple $\Omega(D/\sqrt{\mu\varepsilon})$ lower bound. Batching, rescaling and change-of-variables reductions do not reproduce it. Separately, the literature search found no prior accelerated analysis of nonlinear objectives under errors with bounded partial sums, but that does not prove priority. It is also open whether the Hessian assumption is needed.

What can be claimed: for Hessian-Lipschitz strongly convex objectives, a condition-number-free noise cost under bounded-partial-sum gradient errors, obtained through a genuinely new nonlinear cancellation analysis.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED** — **Confidence: medium**
