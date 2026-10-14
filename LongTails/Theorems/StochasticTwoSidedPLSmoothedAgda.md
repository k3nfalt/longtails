# Stochastic smoothed AGDA under two-sided PL: $\tilde O(\kappa_x^2\kappa_y^2\,\sigma^2/(L\varepsilon))$ samples

Lean: [`StochasticTwoSidedPLSmoothedAgda.lean`](StochasticTwoSidedPLSmoothedAgda.lean) (theorem `result`, budget `budget`),
setup [`../Setups/StochasticTwoSidedPL.lean`](../Setups/StochasticTwoSidedPL.lean),
algorithm [`../Algorithms/StochasticSmoothedAgda.lean`](../Algorithms/StochasticSmoothedAgda.lean),
proofs [`../Proofs/TwoSidedPLEnvelope.lean`](../Proofs/TwoSidedPLEnvelope.lean) (value functions and Danskin-free envelope lemmas),
[`../Proofs/TwoSidedPLStep.lean`](../Proofs/TwoSidedPLStep.lean) (pathwise one-step potential inequality),
[`../Proofs/TwoSidedPLGap.lean`](../Proofs/TwoSidedPLGap.lean) (PL inequality for the potential, criterion bound),
[`../Proofs/TwoSidedPLSum.lean`](../Proofs/TwoSidedPLSum.lean), [`../Proofs/TwoSidedPLPath.lean`](../Proofs/TwoSidedPLPath.lean) (pathwise unrolling),
[`../Proofs/TwoSidedPLSampling.lean`](../Proofs/TwoSidedPLSampling.lean), [`../Proofs/TwoSidedPLProcess.lean`](../Proofs/TwoSidedPLProcess.lean) (independence, moments, martingale terms),
[`../Proofs/TwoSidedPLExecution.lean`](../Proofs/TwoSidedPLExecution.lean), [`../Proofs/TwoSidedPLBudget.lean`](../Proofs/TwoSidedPLBudget.lean),
[`../Proofs/TwoSidedPLConvergence.lean`](../Proofs/TwoSidedPLConvergence.lean).

## Problem class

We study
$$\min_{x\in E}\max_{y\in F} f(x,y),$$
where $E$ is a finite-dimensional real inner-product space and $F$ is any real Hilbert space. The assumptions are those of
Yang, Kiyavash and He, *Global convergence and variance reduction for a class of nonconvex-nonconcave minimax problems*
(NeurIPS 2020, [arXiv:2002.09621](https://arxiv.org/abs/2002.09621)), Assumptions 1–3:

- **Smoothness.** $f$ has partial gradients $g_x(x,y)=\nabla_x f$ and $g_y(x,y)=\nabla_y f$ that satisfy, for all points,
  $\|g_x(x,y)-g_x(x',y')\|\le L(\|x-x'\|+\|y-y'\|)$, and the same for $g_y$. This is implied by $L$-smoothness of $f$ jointly.
- **Two-sided PL.** For all $x,x',y,y'$:
  - $2\mu_x\,(f(x,y)-f(x',y))\le\|g_x(x,y)\|^2$, i.e. $f(\cdot,y)$ is $\mu_x$-PL;
  - $2\mu_y\,(f(x,y')-f(x,y))\le\|g_y(x,y)\|^2$, i.e. $-f(x,\cdot)$ is $\mu_y$-PL.

  Here $0<\mu_x,\mu_y\le L$. Writing PL against an arbitrary competitor avoids any issue of $\inf=-\infty$.
- **Attainment.** For every $x$, $\max_y f(x,y)$ is attained. Then $\Phi(x):=\max_y f(x,y)$ is defined, and
  $\Phi^*=\inf_x\Phi$ is finite automatically, since PL in $x$ bounds $f(\cdot,y_0)$ below.

**Not assumed:**
- existence of a saddle point or of a minimiser of $\Phi$;
- convexity in either variable;
- bounded domains, gradients or iterates;
- Hessian conditions, or mean-squared smoothness of the stochastic oracle.

Write $\kappa_x=L/\mu_x$ and $\kappa_y=L/\mu_y$.

**Instances.** The two-sided PL class contains nonconvex–nonconcave problems. Examples:
- robust least squares and other PL regression problems with an adversary;
- linear-quadratic games in policy space (Zhang et al. 2019; Fazel et al. 2018 show PL for LQR costs);
- hidden-convex games $f(x,y)=F(u(x),v(y))$, where $F$ is strongly-convex–strongly-concave and $u,v$ are smooth
  bi-Lipschitz reparametrisations.

A concrete interacting instance used in our numerical check is in $\mathbb R^2\times\mathbb R^2$:
- $u_i(x)=x_i+0.3\sin x_i$ and $v_j(y)=y_j+0.3\sin y_j$;
- $F(u,v)=\tfrac12u^\top Au+u^\top Bv-\tfrac12v^\top Cv$, with non-diagonal $A\succ0$, $C\succ0$ and a full $B$.

It is nonconvex in $x$ and nonconcave in $y$, has interacting coordinates, and its estimated constants are $L\approx5.3$,
$\kappa_x\approx29$, $\kappa_y\approx21$.

## Oracle and accuracy criterion

There are two kinds of query, and each returns a stochastic partial gradient:
- query $(x,y)$ in the x-branch returns $G_x((x,y),\xi)$;
- query $(x,y)$ in the y-branch returns $G_y((x,y),\xi)$.

The samples $\xi_0,\xi_1,\dots$ are IID with law $p$; the Lean oracle law is `Measure.infinitePi`. Each call consumes a
fresh sample. For every point, $G_x$ and $G_y$ are integrable and unbiased, with
$\mathbb E\|G-\nabla\|^2\le\sigma^2$, and they are jointly measurable (`IsUnbiasedOracle`). This is Yang–Kiyavash–He's
Assumption 3, with independent samples for the two blocks.

The accuracy criterion is Yang–Kiyavash–He's $a+\lambda b$ with $\lambda=1$. Their own analysis uses $a+b/10$, which
differs from ours by at most a factor 10.

$$\mathbb E\big[(\Phi(\hat x)-\Phi^*)+(\Phi(\hat x)-f(\hat x,\hat y))\big]\le\varepsilon,$$

The expectation is over all oracle samples and the algorithm's output index. In Lean it is an explicit Bochner integral
over the product probability space, together with integrability and measurability of the output.

## Algorithm

The algorithm is stochastic smoothed AGDA: Yang, Orvieto, Lucchi and He, AISTATS 2022
([arXiv:2112.05604](https://arxiv.org/abs/2112.05604)), Algorithm 2, with smoothing $p=2L$. Start from $z_0=x_0$. Each
iteration $t$ makes 2 oracle calls:

$$x_{t+1}=x_t-\tau\big(G_x(x_t,y_t;\xi_{2t})+2L(x_t-z_t)\big),\quad
y_{t+1}=y_t+\tfrac{\tau}{32}G_y(x_{t+1},y_t;\xi_{2t+1}),\quad z_{t+1}=z_t+\tfrac{\tau\mu_y}{6144}(x_{t+1}-z_t).$$

The parameters are:
- step size $\tau=1/\big(L(3+2^{24}L\sigma^2/(\mu_x\mu_y\varepsilon))\big)$;
- window length $n=\lceil 2^{18}\tfrac{L^2}{\mu_x\mu_y}(3+2^{24}\tfrac{L\sigma^2}{\mu_x\mu_y\varepsilon})(2+\log(1+\Delta/\varepsilon))\rceil$.

The method runs $2n+1$ iterations and returns $(x_s,y_s)$, with $s$ uniform on $\{n,\dots,2n\}$. The index is drawn from
the algorithm's own seed, independent of the oracle samples.

The parameters use only $L,\mu_x,\mu_y,\sigma,\varepsilon$ and $\Delta$. They never use $\Phi^*$, a saddle point, or a
minimiser. The setup's `allowedAlgorithm` restricts to `stochasticSmoothedAgda r τx τy β n x0 y0`. The proof shows that
the actual execution makes exactly $4n+2$ alternating calls and returns iterate $n+j$ (`execute_agda`).

## Guarantee

**Theorem (`result`).** Assume $\Delta\ge 2\Phi(x_0)-\Phi^*-f(x_0,y_0)+\|g_x(x_0,y_0)\|^2/L$, that is, $\Delta\ge a_0+b_0+\|\nabla_xf(x_0,y_0)\|^2/L$.
Then with
$$\texttt{budget}=4\Big\lceil 2^{18}\frac{L^2}{\mu_x\mu_y}\Big(3+2^{24}\frac{L\sigma^2}{\mu_x\mu_y\varepsilon}\Big)\Big(2+\log\big(1+\tfrac{\Delta}{\varepsilon}\big)\Big)\Big\rceil+2$$
oracle calls, the output satisfies $\mathbb E[(\Phi(\hat x)-\Phi^*)+(\Phi(\hat x)-f(\hat x,\hat y))]\le\varepsilon$. That is,
$$O\Big(\Big(\kappa_x\kappa_y+\kappa_x^2\kappa_y^2\frac{\sigma^2}{L\varepsilon}\Big)\log\frac{\Delta}{\varepsilon}\Big)\ \text{stochastic gradients.}$$

## Comparison with prior work

All rates are stochastic-gradient complexities for $\mathbb E[a]+\mathbb E[b]\lesssim\varepsilon$ under bounded variance,
in the regime where the $\sigma^2/\varepsilon$ term dominates.

| Method / paper | Assumptions | Output | Complexity |
|---|---|---|---|
| Stoc-AGDA, Yang–Kiyavash–He NeurIPS 2020, Thm 3.3 / Remark 3 | two-sided PL, as here | last iterate | $\kappa_x^2\kappa_y^4\,\sigma^2/(L\varepsilon)$ (their $l^5\sigma^2/(\mu_1^2\mu_2^4\varepsilon)$), diminishing steps, no log |
| Guo–Yan–Yuan–Yang JMLR 2023 ([arXiv:2006.06889](https://arxiv.org/abs/2006.06889)), Table 1 (PES-SGDA) | PL in $x$, **strongly concave** in $y$ | last stage | $\tilde O(\kappa_x^2\kappa_y^3\,\sigma^2/(L\varepsilon))$ |
| FESS-GDA, Shen et al. AISTATS 2024 ([arXiv:2311.00944](https://arxiv.org/abs/2311.00944)), Thm 3.5 with one client | two-sided PL | distance criterion | recovers Yang et al. 2020 (polynomially worse $\kappa$-power) |
| Smoothed-AGDA, Yang–Orvieto–Lucchi–He AISTATS 2022, Thm 4.1 / Thm A.1 | NC-PL (stationarity) / two-sided PL **deterministic** | — | no stochastic two-sided-PL rate |
| Chen–Yao–Luo NeurIPS 2022 | finite sums ($n$ components) | — | not the online setting |
| **This result** | two-sided PL, as Yang et al. 2020 | uniform second-half iterate | $\kappa_x^2\kappa_y^2\,\tfrac{\sigma^2}{L\varepsilon}\log\tfrac{\Delta}{\varepsilon}$ |

**Improvement.**
- Under the same assumptions and oracle as Stoc-AGDA, the sample complexity improves by a factor $\kappa_y^2/\log(\Delta/\varepsilon)$.
- It also beats, by a factor $\kappa_y$ up to logarithms, the rate Guo et al. obtain under the stronger assumption of
  strong concavity in $y$.

**Reduction check.** The obvious double-loop reduction is outer SGD on the $\mu_x$-PL, $L(1+\kappa_y)$-smooth function
$\Phi$, with inner stochastic ascent on $y$. Each outer gradient then needs inner accuracy
$b\lesssim\mu_x\mu_y\varepsilon/L^2$, which costs $\tilde O(\kappa_x^2\kappa_y^4\sigma^2/(L\varepsilon))$ samples overall.
So the reduction is no better than Stoc-AGDA, and the improvement here is not a corollary of existing theorems.

**Technical mechanism.**
1. The potential is $V=\hat f-2\Psi+2P$ (Zhang et al. 2020; Yang et al. 2022), where
   $\hat f=f+L\|x-z\|^2$, $\Psi(y;z)=\min_x\hat f$ and $P(z)=\min_x\Phi+L\|x-z\|^2$. It decreases by a sufficient amount
   $D_t$ per step, up to noise. Our proof is pathwise, and the noise enters only through zero-mean cross terms and
   $\|e\|^2$ terms.
2. **New:** a PL inequality for the potential. For every $y$,
   $$P(z)-\Phi^*\le(P(z)-\Psi(y;z))+(L+2L^2/\mu_x)\|\hat x(y,z)-z\|^2.$$
   This envelope-gap lemma uses PL in $x$ at $(\hat x,y)$ and $\inf_x f(x,y)\le\Phi^*$. It needs no Danskin theorem, no
   saddle point and no quadratic growth. It gives $V-\Phi^*\le C D_t+O(\kappa_xL\tau^2\|e_1\|^2)$ with $C=O(\kappa_x\kappa_y/(L\tau))$,
   hence linear convergence of $\mathbb EV$ up to an $O(\kappa_x\kappa_y\tau\sigma^2)$ floor.
3. **New:** the criterion is bounded directly by gradient norms at the iterate,
   $b\le\|g_y\|^2/(2\mu_y)$ and $a\le b+\|g_x\|^2/(2\mu_x)$. These in turn are bounded by $C D_t$, so averaging over a
   window converts the potential decrease into the criterion with no extra $\kappa_y$ loss.
4. The value functions $\hat x,\Psi,\bar x,P$ are constructed in Lean from minimiser existence: strong convexity of the
   regularised problems, lower semicontinuity of $\Phi$, and properness of $E$. They are not postulated.

The constants ($2^{18}$, $2^{24}$) are not optimised.

## Limitations and open questions

- **Output.** The bound is for a uniformly random iterate from the second half, not the last iterate. Our own
  conversion to the last iterate loses extra powers of $\kappa_y$. Stoc-AGDA's bound is a last-iterate bound.
- **Log factor.** Constant steps cost a $\log(\Delta/\varepsilon)$ factor that Stoc-AGDA does not have. In the
  deterministic regime ($\sigma=0$) the bound is $O(\kappa_x\kappa_y\log(\Delta/\varepsilon))$ iterations, comparable to the
  double-loop deterministic bound $O(\kappa_x\kappa_y\log^2)$ of Chen–Yao–Luo (NeurIPS 2022); we make no novelty claim for it.
- **Optimality.** No lower bound is claimed. The heuristic "SGD on $\Phi$ with an exact inner maximisation" costs
  $\kappa_x^2\kappa_y\sigma^2/(L\varepsilon)$, so a gap of one $\kappa_y$ factor may remain. Whether $\kappa_x^2\kappa_y$ is
  achievable by a single-loop method is open.
- **Finite dimension.** $E$ is finite-dimensional, which is used for minimiser existence. $F$ is arbitrary.
- **Mourrat.** Mourrat ([arXiv:2602.16517](https://arxiv.org/abs/2602.16517), v3, Sep 2026) shows that two-sided PL does
  not guarantee convergence of the gradient descent–ascent *flow*. This does not conflict with our result:
  - our method is a discrete, proximally anchored dynamics in which $x$ moves on a faster timescale than $y$ and $z$;
  - the proof uses no flow or ODE argument.
- **Literature status.** The Yang et al. 2020 and 2022 papers and Guo et al. are published versions.
  - Conference status was checked through the proceedings listings.
  - OpenReview discussions were not consulted.
  - No stochastic two-sided-PL result for smoothed AGDA was found in ICML/ICLR/NeurIPS 2024–2026 or recent arXiv
    searches. The search is necessarily incomplete.
