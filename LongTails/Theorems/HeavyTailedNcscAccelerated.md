# Accelerated nonconvex–strongly-concave minimax optimization with heavy-tailed gradients

The [main theorem](HeavyTailedNcscAccelerated.lean) constructs the algorithm in [HeavyTailSaddleEstimator](../Algorithms/HeavyTailSaddleEstimator.lean) for the [HeavyTailedNcsc specification](../Setups/HeavyTailedNcsc.lean). It gives one computable output with a tunable high-probability bound on the true gradient of the maximized objective, and an explicit deterministic budget for every original joint-gradient oracle call. The proposed research contribution is the simultaneous accelerated deterministic term and improved heavy-tail condition-number dependence for general nonlinear objectives when $1<p<2$. The accuracy exponent, clipping, and the finite-variance specialization are not claimed as new.

## Problem and information model

Let $f:E\times F\to\mathbb R$, where $E,F$ are arbitrary finite-dimensional real inner-product spaces. Its joint gradient is globally $L$-Lipschitz in the Euclidean product norm, and $f(x,\cdot)$ is globally $\mu$-strongly concave, with $0<\mu\le L$. Write

$$
\Phi(x)=\max_y f(x,y),\qquad \kappa=L/\mu.
$$

There is no convexity assumption in $x$, bounded-domain assumption, samplewise smoothness, bounded-gradient assumption, Hessian oracle, or finite-sample-space restriction. Strong concavity and finite-dimensionality yield attainment of the inner maximum; the proof derives the differentiability and geometry of $\Phi$.

The public initial bounds are $\Phi(x_0)-\inf_x\Phi(x)\le\Delta$ and $\|\nabla_y f(x_0,y_0)\|\le G$. The specification expresses the first bound without assuming a primal minimizer: for every $x,y$, some $y'$ satisfies $f(x_0,y)-f(x,y')\le\Delta$. Given the derived inner attainment, this is the same value-gap condition.

One oracle call returns both partial gradients at a queried pair. The jointly measurable oracle is unbiased and has central joint Euclidean $p$-moment at most $\sigma^p$, uniformly over query points, for $1<p\le2$. Integrability is explicit. Samples form an abstract IID stream with the stated marginal law; the product-measure representation is derived internally. The algorithm's independent randomization is included in the execution probability. IID sampling is narrower than a general conditionally unbiased adaptive oracle model.

The algorithm knows $L,\mu,p,\sigma,\Delta,G,\varepsilon,\delta,x_0,y_0$. It does not know the objective, an inner optimizer, a primal optimizer, or function values. The target is $\varepsilon>0$, $0<\delta<1/2$. No restriction to an artificially fixed algorithm family is imposed on the setup.

These assumptions are the conventional smooth NC–SC and central-moment assumptions used in the primary minimax and heavy-tail papers compared below. The precise joint-moment and IID formulation, and the public localization bounds, are part of this theorem's scope. They are not inferred from a stronger samplewise oracle assumption.

## Algorithm, output, and proved budget

The algorithm makes

$$
T=1+\left\lceil4096L\Delta/\varepsilon^2\right\rceil
$$

coarse proximal saddle solves, with primal regularizer $L\|x-c\|^2$, target joint gap $\zeta_c=\varepsilon^2/(2^{20}L)$, and per-call failure allocation $\delta/(T+2)$. It retains the old center and returned pair with the smallest observed primal movement. A fresh fine solve at that retained center, initialized by the matching retained pair, uses $\zeta_f=\mu\varepsilon^2/(2^{20}L^2)$. The output is the fine solve's primal component. Selection uses observed iterates, not an unavailable true gradient. The fine solve uses fresh samples and independent internal randomness.

Each saddle solve uses accelerated dual epochs with batched, clipped multilevel gradient estimates, a robust primal refresh, and recursively increasing dual regularization. Epochs halve their public energy envelope. Random multilevel execution is capped using proved mean-work and maximum-single-reply bounds; padding and fallback branches are included in the deterministic call budget. The confidence allocation and public schedules remain fixed even on failed paths.

For a readable statement of the exact public budget, define

$$
r=\frac p{p-1},\quad A=\frac{L\Delta}{\varepsilon^2},\quad u=\frac\sigma\varepsilon,
\quad Q=\log\!\left(2+\kappa^3\frac{L(\Delta+G^2/\mu)}{\varepsilon^2}\right),
$$
$$
\Lambda=1+\log\!\left(2+\kappa+\delta^{-1}+A+(\kappa u)^r+Q\right).
$$

The theorem's budget is the nonnegative natural ceiling

$$
\boxed{\left\lceil(2^{80}r)^{r+2}\Lambda^{2r+3}
\left[\sqrt\kappa(1+A+Q)
+\left(A\kappa^{r/2}+\kappa^r\right)u^r\right]\right\rceil.}
$$

The Lean `budget` definition expands every abbreviation in one explicit line of setup parameters. The proof establishes that this budget dominates `saddleCalls` for the actual execution, including all batching, refreshes, random-length caps, fine refinement, and padding. No expected running-time bound is substituted for this deterministic budget.

Under the execution measure $P_{\rm exec}$, the returned point $X$ satisfies

$$
P_{\rm exec}\{\|\nabla\Phi(X)\|>\varepsilon\}\le\delta.
$$

The specification also requires measurability of the output and states the same guarantee for every maximizing selector. This is a selected-point high-probability guarantee. It is not an expected-gradient guarantee: the theorem does not bound the gradient on failed paths.

For fixed $p\in(1,2)$, suppressing the displayed logarithms and $p$-dependent constant gives

$$
\widetilde O_p\!\left(
\sqrt\kappa\left(1+\frac{L\Delta}{\varepsilon^2}\right)
+\frac{\kappa^{r/2}L\Delta\sigma^r}{\varepsilon^{r+2}}
+\frac{\kappa^r\sigma^r}{\varepsilon^r}
+\sqrt\kappa\,Q\right).
$$

The baseline term remains when both noise and initial gap vanish. The fine-refinement term can dominate for small initial gap. Initialization also enters the noise work through $\Lambda$, producing a log-log dependence on large $G$; strictly additive initialization dependence is not claimed. Constants are deliberately conservative and very large, and both their $p$-dependence and the logarithmic exponent deteriorate as $p\downarrow1$.

## Technical contribution and the standard-reduction check

The proof's central task is an additive accelerated saddle solver under the primitive heavy-tail gradient oracle. A uniformly accurate robust estimate at every accelerated gradient evaluation generally pays the statistical estimation cost at every deterministic accelerated step. Merely replacing the variance parameter in a finite-variance saddle theorem does not justify the desired additive rate.

The multilevel construction compares stochastic fast solves to the same deterministic nonlinear orbit. It derives a finite-depth bias and central $p$-moment from the original oracle without assuming samplewise smoothness or an unbiased exact dual-gradient oracle. Batching precedes clipping. The accelerated energy proof separately tracks predictable bias, conditional second moment after clipping, and bounded increments on a stopped localization event. Keeping these quantities separate avoids paying the clipping range as a variance proxy. A direct primal-refresh distance certificate and recursive regularization turn the dual energy guarantee into the joint saddle gap required by warm starts and the final residual bound.

The cost proof preserves two different sums: geometric halving of noise requirements avoids multiplying the final statistical cost by the number of cold epochs, while geometric regularization gives the accelerated sum of stage condition numbers. A single-reply maximum controls cap overflow. Replacing any of these by a worst-case full-stage cost would lose part of the claimed rate.

A useful standard-reduction benchmark is an inner saddle solve with normalized statistical difficulty $S=(\sigma/\sqrt{\mu\zeta})^r$. Even granting a nonaccelerated solver costing $\widetilde O_p(\kappa+S)$, and a robust implementation of deterministic acceleration costing $\widetilde O_p(\sqrt\kappa(1+S))$, their minimum can be order $\kappa$ at $S=\sqrt\kappa$. The present proof gives the additive $\widetilde O_p(\sqrt\kappa+S)$ behavior, with the displayed localization and confidence costs. This comparison identifies the obstruction to those simple reductions; it is not a lower bound against every possible robust Catalyst construction.

Existing Catalyst analyses need a stronger inner certificate than an ordinary distance-error bound. In particular, [Lan–Li, arXiv v2, Section 5 and Eq. (5.1)](https://arxiv.org/html/2311.02814v2) allow a dual comparison point chosen after the inner randomness and use an auxiliary sequence to control that correlation. Theorem 5.2 gives expected primal gap plus dual tracking distance, not an immediately interchangeable joint saddle-gap certificate. Clipping also destroys the unbiasedness assumed in that analysis. These contracts must be reproved before invoking it here.

Likewise, [Gürbüzbalaban–Syed–Aybat, v3, Assumption 3.1 and Section 5](https://arxiv.org/html/2509.13628v3) assume a conditional sub-Gaussian bound on the total error. Applying that proxy to the full clipping range discards the separate small-bias and second-moment bounds used here. [SAAS, v2](https://arxiv.org/abs/2604.15526) permits biased finite-moment gradients but also requires function-value oracles, which this setup does not supply. None of these observations excludes a different, simpler future proof of the same rate.

## Closest results, regimes, and tradeoffs

| Primary result | Relevant guarantee and scope | Difference from this theorem |
|---|---|---|
| [Wu et al., 2610.00229v2, Theorem 4.1 and F1–F5](https://arxiv.org/html/2610.00229v2), revised 19 October 2026 | Smooth NC–SC, fresh conditional finite-variance gradients; four-term polynomial rate matching this theorem at $p=2$, with success probability $2/3$ | The new claim concerns $p<2$, not the finite-variance polynomial rate. Our tunable confidence costs explicit logarithms, our oracle is IID, and our stochastic work has additional log-log initialization dependence. This source is a preprint, not a verified accepted conference paper. |
| [Zhu–Xu–Ji, 2609.06064v1, Theorem 4.3 / Eq. (4.9)](https://arxiv.org/html/2609.06064v1), 5 September 2026 | Heavy-tail expected-norm result; leading noise term $A\kappa^{r+1}u^r$, deterministic term $A\kappa^{1+r/2}$, with composite extensions | We improve the polynomial conditioning terms in the smooth class, but give tunable-confidence selected-point accuracy rather than expected accuracy. We do not cover its composite scope. The accuracy exponent is already known. |
| [Liu–Luo, JMLR 27(233), Theorem 11 and Appendix C](https://jmlr.org/papers/v27/25-3100.html), 2026 | High-probability trajectory-average gradient **norm**, with leading terms $A\kappa^{r+1}u^r+A\kappa^2$, plus initialization and logarithms | Our output is one computably selected point and has different conditioning. Their norm is not a squared-norm criterion; selection and any guarantee conversion must be charged rather than silently assumed. |
| [Sadiev et al., ICML 2023, Theorem 4.1 / G.4](https://proceedings.mlr.press/v202/sadiev23a.html) | Heavy-tail monotone VI and accelerated convex minimization; the strongly monotone VI distance-squared complexity has form $\widetilde O_p(L/\mu+(\sigma^2/(\mu^2 e))^{r/2})$ | Heavy-tail clipping, localization and convex acceleration are already known. The missing component here is the accelerated asymmetric saddle certificate and its nonlinear NC–SC composition, not those tools individually. |

When $A\ge\kappa^{r/2}$, the fine noise term is no larger than the leading $A\kappa^{r/2}u^r$ term. In that regime, the displayed heavy-tail leading term improves the $\kappa^{r+1}$ dependence above by $\kappa^{r/2+1}$, before the explicit logarithms and constants. This is a conditioning comparison, with the output and expectation/confidence differences in the table retained.

A regime testing the simultaneous improvement is $\kappa^{r/2}u^r\asymp\sqrt\kappa$ and $A$ larger than $\kappa^{r/2}$. The new polynomial leading cost is $A\sqrt\kappa$; the simple nonaccelerated-versus-uniformly-robust-accelerated envelope discussed above can be $A\kappa$. For fixed $p$, sufficiently large condition numbers can separate these polynomial rates despite logarithmic overhead. No universal finite-parameter superiority is asserted, particularly with the conservative explicit constants. The theorem is not a claim of optimal heavy-tail dependence on $\kappa$.

## Nonlinear scope and limitations

The setup includes dense, nonseparable families such as

$$
f(x,y)=\tfrac a2\|x\|^2+b\sum_i\cos((Bx)_i)
+c\sum_i\sin((Cx)_i)\sin((Dy)_i)
-\tfrac\nu2\|y\|^2+x^\top Ay.
$$

For compatible dense matrices of bounded operator norm, $a>0$ and $\nu\ge\mu+|c|\|D\|^2$ ensure a bounded-below maximized objective and dual strong concavity. The joint Hessian is globally bounded by a constant depending on these coefficients and operator norms; choosing the oscillatory curvature sufficiently large retains primal nonconvexity. The nonlinear dual solution and interactions across coordinates are not reducible to the scalar or quadratic diagnostics used in proof development. This family illustrates the standard class; it is not an additional assumption or the motivation for an artificial restriction.

Additive IID joint noise with a finite $p$-moment fits the model, including infinite-variance noise for $p<2$. Dimension enters through the actual smoothness, initial bounds and joint moment scale $\sigma$; the theorem does not equate that joint scale with a dimension-free per-coordinate noise bound. No additional explicit dimension factor appears in the budget.

The main novelty risk is that the result may be viewed as a technically elaborate heavy-tail extension of the finite-variance construction. Its substantive claim is therefore the full simultaneous conditioning improvement under primitive fresh gradients, together with the derived nonlinear oracle and saddle-gap certificates. Formalization supports correctness but is not the novelty claim. The proof does not establish matching heavy-tail lower bounds, adaptive parameter tuning, composite or constrained extensions, general conditional-oracle dependence, or expected-gradient accuracy.

The closest versions above were checked through 7 November 2026, following independent surveys of the two most recent publicly available ICML, ICLR and NeurIPS editions and approximately two years of arXiv submissions/revisions, with older foundational results followed through citations. [Lan–Li's publication metadata](https://link.springer.com/article/10.1007/s10107-025-02309-x) confirms publication on 12 January 2026, but the published full text was inaccessible; the detailed comparison uses arXiv v2, dated 8 November 2023. This access limitation leaves uncertainty about changes appearing only in the published version.

## Formal proof organization

[Geometry](../Proofs/HeavyTailSaddleGeometry.lean) derives the minimax geometry and attainment. [Multilevel](../Proofs/HeavyTailSaddleMultilevel.lean), [energy](../Proofs/HeavyTailSaddleEnergy.lean), [refresh](../Proofs/HeavyTailSaddleRefresh.lean) and [epoch](../Proofs/HeavyTailSaddleEpoch.lean) derive the stochastic estimator, localization and refinement guarantees. [Recovery](../Proofs/HeavyTailSaddleRecovery.lean) supplies the recursive saddle certificate. [Execution](../Proofs/HeavyTailSaddleExecution.lean) and [outer accuracy](../Proofs/HeavyTailSaddleOuter.lean) connect the actual plans, fresh sampling, output selection and `Template.execute` to the specification. [Recovery cost](../Proofs/HeavyTailSaddleCost.lean) and [outer cost](../Proofs/HeavyTailSaddleOuterCost.lean) prove the explicit oracle budget.
