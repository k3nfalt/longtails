# Temporal accelerated quadratic: novelty assessment

The [theorem](../../LongTails/Theorems/TemporalAcceleratedQuadratic.lean) ([setup](../../LongTails/Setups/QuadraticTemporalDiscrepancy.lean), [algorithm](../../LongTails/Algorithms/TemporalAccelerated.lean)) proves the following. Nesterov's constant-momentum method uses $\theta=\sqrt{\mu/L}$ and runs for $2K$ calls. Its output $\bar x$ is the average of the iterates $K+1,\dots,2K$, and it satisfies $f(\bar x)-f(x_*)\le\varepsilon$ for every seed. The objective is $f(x)=\tfrac12\|A(x-x_*)\|^2$ on any real Hilbert space, with $\mu\|v\|^2\le\|Av\|^2\le L\|v\|^2$ and $f(x_0)\le\Delta$. Each call $k$ returns $A^*A(x-x_*)+e_k$, where $(e_k)$ is a hidden, deterministic sequence that does not depend on the query and satisfies $\sup_n\|\sum_{k<n}e_k\|\le D$.

**Proved budget.** The method makes $2\max\{1,\lceil\sqrt{L/\mu}\log(1+8\Delta/\varepsilon)+8D/\sqrt{\mu\varepsilon}\rceil\}$ gradient calls, so

$$N=O\Big(1+\sqrt{L/\mu}\,\log(1+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon}\Big).$$

The parameters are:
- $L,\mu$: the curvature bounds;
- $\Delta$: the initial gap;
- $D$: the bound on the error partial sums;
- $\varepsilon$: the target accuracy.

The domain is $0<\mu\le L$, $D,\Delta\ge0$, $\varepsilon>0$. The updates need only $L,\mu,x_0$; the stopping rule also needs $D,\Delta,\varepsilon$. The method spends at least 2 calls even when $\Delta\le\varepsilon$. With $D=0$ the result reduces to classical acceleration.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Schmidt–Le Roux–Bach, NeurIPS 2011, Prop. 4](https://arxiv.org/pdf/1109.2415v2) (arXiv v2), plus the dilation reduction derived below; covers the full target class | $O(1+\sqrt{L/\mu}\log(1+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon})$ → $O(1+\sqrt{L/\mu}\log(1+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon})$ | None: same order | None: same class | The reduction needs $D,\varepsilon$ in its updates (to set the batch size $m$ and the dilation $t$); the selected method needs them only for stopping. Output: last iterate → tail average, which is not stronger | The reduction queries at precision-dependent dilated points $x_0+tv$, with $t$ arbitrarily large. Prop. 4 is stated in $\mathbb R^n$; its proof uses only inner products |
| Batching without dilation: $b$ consecutive calls per point give error $\le 2D/b$, then Prop. 4 (derived) | $O(\sqrt{L/\mu}\log(1+\Delta/\varepsilon)\,[1+\sqrt{L/\mu}\,D/\sqrt{\mu\varepsilon}])$ → selected $N$ | Noise term shrinks by a factor of about $\sqrt{L/\mu}\log(1+\Delta/\varepsilon)$ when $D\ge\sqrt{\mu\varepsilon}$ and $L\gg\mu$ | None | Same as row 1 | This baseline is dominated by row 1. The comparison only shows that naive batching is weaker |
| Repository [NonlinearTemporalAcceleration](../../LongTails/Theorems/NonlinearTemporalAcceleration.lean) (subsequent, 2026-09-28) | quadratic overlap: $O((1+\sqrt{L/\mu}+D/\sqrt{\mu\varepsilon})\log(2+\Delta/\varepsilon))$ → $N$ | The selected bound is better by a log factor on the noise term | The subsequent result is broader: it covers Hessian-Lipschitz objectives | None | The subsequent result needs finite dimension and a known $M$ |

**Reduction check (derived here).** Write $H=A^*A$.
1. Average the first $m=\lceil 2D/\sqrt{\mu\varepsilon}\rceil$ replies at $x_0$. This gives $c=\nabla f(x_0)+\bar e$ with $\|\bar e\|\le D/m$.
2. Answer each surrogate query $v$ with $c+(g_k(x_0+tv)-c)/t$. This equals $Hv+c$ up to an error of at most $3D/t$, since $\|e_k\|\le2D$.
3. The surrogate is $F(v)=f(x_0+v)-f(x_0)+\langle\bar e,v\rangle$. Completing the square gives
$$\sqrt{2(f(x_0+v)-f_*)}\le\sqrt{2(F(v)-\min F)}+D/(m\sqrt\mu)$$
and $F(0)-\min F\le2\Delta+\varepsilon$.
4. Prop. 4 with $\gamma=\mu/L$, exact prox and error $\|e_i\|\le3D/t\to0$ gives the rate $(1-\sqrt{\mu/L})^k$. Reaching $F-\min F\le\varepsilon/8$ takes $O(\sqrt{L/\mu}\log(1+\Delta/\varepsilon))$ steps.

The total, $m$ plus the number of steps, is the row-1 bound. The reduction works because the errors do not depend on the query and the gradient is affine.

Order-optimality is also derived here, not cited. A constant error $D/n$ over $n$ calls looks exactly like a shifted minimizer, so every method needs $\Omega(D/\sqrt{\mu\varepsilon})$ calls. Nesterov's span-method bound supplies $\Omega(\sqrt{L/\mu}\log(\Delta/\varepsilon))$ in $\ell_2$. So no method can beat $N$ by more than constants, up to the regime where $\log(1+\Delta/\varepsilon)$ is not $\Theta(\log(\Delta/\varepsilon))$, i.e. $\Delta$ near $\varepsilon$.

**Proof ancestry.** The proof combines a Nesterov energy contraction with summation by parts ([cumulative response](../../LongTails/Proofs/TemporalLinearResponse.lean)). That is the deterministic analogue of the Polyak–Juditsky averaging identity for linear recursions. I found no new mechanism beyond its accelerated tail-average bookkeeping.

**Search coverage.** I searched on 2026-10-07 UTC, covering arXiv and NeurIPS/ICML/COLT sources on inexact acceleration, anticorrelated noise and linearly correlated noise:
- [Koloskova et al., NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/70255afc962aca0930327c090eb7d8c5-Abstract.html) studies GD only, with Gaussian correlated noise.
- [Orvieto et al., ICML 2022](https://proceedings.mlr.press/v162/orvieto22a.html) is about generalization.
- I did not recheck [Flammarion–Bach, COLT 2015](https://proceedings.mlr.press/v40/Flammarion15.pdf) or Cohen–Diakonikolas–Orecchia (ICML 2018).

The result entered the repository in `d64d9ed` (2026-09-24 16:21 UTC). There is no companion note. An earlier local [review](../reviews/TemporalAcceleratedQuadratic.md) reached the same reduction, and I re-derived it independently. No build or axiom audit was run.

**Conclusion**

**No: the complexity is unchanged, and a simple reduction from 2011 already achieves it.** The strongest baseline is Schmidt–Le Roux–Bach's inexact accelerated method (Prop. 4) applied after a batching-and-dilation reduction. The errors do not depend on the query and the gradient is affine, so querying at far-away dilated points makes the error negligible. Both approaches then cost

$$O\big(1+\sqrt{L/\mu}\,\log(1+\Delta/\varepsilon)+D/\sqrt{\mu\varepsilon}\big),$$

and a short indistinguishability argument suggests this order cannot be beaten.

The selected method's real differences are practical. It makes ordinary queries, needs no dilation, and its updates do not use $D$ or $\varepsilon$. Both still need those parameters to decide when to stop, so this is not an adaptive guarantee. The tail-average output is no stronger than the reduction's last iterate.

The method-specific analysis (accelerated iteration plus summation by parts over the tail average) may well be new in this exact form; the search found no earlier instance. Its mechanism, however, is the classical averaging identity for linear recursions. What can be claimed is a clean, dilation-free accelerated method that attains the already achievable optimal-order bound on quadratics.

**Verdict: NO IMPROVEMENT**

**Confidence: medium**
