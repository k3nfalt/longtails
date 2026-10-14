# Adaptive accelerated optimization with heavy-tailed simplex gradients

The [main Lean theorem](AdaptiveEntropicHeavyTailConvex.lean) proves `Convergence spec budget` for the [simplex setup](../Setups/AdaptiveHeavyTailSimplex.lean) and the [adaptive entropic algorithm](../Algorithms/AdaptiveEntropic.lean). Its mathematical proof and execution guarantee are complete supporting derivations. The novelty comparison in this note is restricted to the checked literature excluding NeurIPS 2026 papers.

## Setup and available information

Minimize a convex objective over the probability simplex in any finite dimension $d\ge2$. The objective has an ambient gradient at every simplex point, including boundary points, and satisfies

\[
\|\nabla f(x)-\nabla f(y)\|_\infty\le L\|x-y\|_1.
\]

No global convexity or smoothness outside the simplex is required. Ambient differentiability is stronger than differentiability only along its affine hull and is an explicit restriction. A constrained minimizer exists. Neither its gradient nor the absolute gradient magnitude is bounded, and the minimizer may lie on the boundary.

The oracle is a jointly measurable stationary function $g(x,\omega)$ with fresh IID seeds, vector-valued unbiasedness, raw-gradient integrability, and an integrable central moment

\[
\mathbb E\|g(x,\omega)-\nabla f(x)\|_\infty^p\le\sigma^p,
\qquad 1<p\le2.
\]

The seed spaces are arbitrary measurable spaces. The admissible sequence law is specified by IID coordinates and marginal law, rather than prescribed as a product measure; the proof derives the product representation internally. Point-dependent, asymmetric, correlated-coordinate and unbounded noise is allowed. Arbitrary time-varying or adversarial conditional-moment kernels are outside this specification.

Only $d,L,\delta$ are public algorithm inputs. The updates do not receive $p,\sigma,\varepsilon$, the minimizer, function values, or a horizon. The accuracy-dependent budget below is an analytical execution limit, not a parameter-free stopping certificate.

## Algorithm and returned point

Set $H=\log(100/\delta)$, $D=\max\{1,\log d\}$, $K=\max\{1,\lceil64(D+H)\rceil\}$, $k_t=\lceil16(H+\log(t+1))\rceil$, and $m_0=\lceil64H\rceil$. After $m_0$ one-query warmup samples at the uniform point, each completed iteration uses two independent replies at the same accelerated query point.

A coordinatewise median of the last $k_t$ primary/warmup replies predicts the gradient. A predictable threshold combines the drift allowance $24Lk_t/t$ with the minimum of a zero-padded top-$K$ buffer of past weighted excess norms. The primary reply is clipped radially around that median. A second reply, clipped with the same center and threshold, supplies an observed squared difference for the regularization scale.

Entropic dual averaging uses cumulative weighted primary estimates. Its scale incorporates smoothness, the empirical quantile, and accumulated paired variation. The pre-query prox point is recomputed at the current scale; the post-query prox uses that same scale. This accommodates arbitrary scale jumps without restarting the trajectory. The returned $y_T$ is the final accelerated aggregate of post-prox points, not the last query point. Full history is retained: memory is $O((m_0+T)d+K)$.

## Proved rate and oracle cost

The supporting [fixed-horizon guarantee](../Proofs/AdaptiveEntropicGuarantee.lean) proves, with probability at least $1-\delta$,

\[
f(y_T)-f(x^\star)\le2^{24}\left[
\frac{LKk_T}{T^2}+\sigma\left(\frac KT\right)^{(p-1)/p}\right],\qquad T\ge1.
\]

It holds for each deterministic horizon; it does not assert a single event for all horizons or arbitrary data-dependent stopping times.

Writing $J=\log(2d)+H$ and $q=p/(p-1)$ solely to display the formula, the public theorem uses

\[
N=\left\lceil256H+2^{26}\sqrt{\frac{LJ}{\varepsilon}
\left(H+\log\left(2+\frac{LJ}{\varepsilon}\right)\right)}
+4J\left(\frac{2^{38}\sigma}{\varepsilon}\right)^q\right\rceil.
\]

The Lean `budget` expands this as one explicit line in setup parameters. Every warmup, paired, and unmatched final query is counted. The [budget proof](../Proofs/AdaptiveEntropicBudget.lean) gives $T=\lfloor(N-m_0)/2\rfloor\ge1$ and accuracy at most $\varepsilon$. The [execution bridge](../Proofs/AdaptiveEntropicRun.lean) proves that the actual $N$-call output equals $y_T$, including when one final primary query remains unmatched. The [specification proof](../Proofs/AdaptiveEntropicConvergence.lean) establishes measurability and the epsilon guarantee under the admissible IID law and the framework's seed product measure. The zero-noise case is included. Constants inside the noise term are raised to $q$; no uniform bounded prefactor as $p\downarrow1$ is claimed.

## Mechanism and contribution

The contribution under this literature scope is simultaneous adaptation to unknown $p,\sigma$ with stochastic cost $J(C\sigma/\varepsilon)^q$, while retaining deterministic acceleration up to a logarithmic loss. Removing the stationary-optimum condition alone is not claimed as novel.

The analysis couples a capped top-$K$ excess identity to predictable bias concentration. An analysis-only cap yields an $O(KA)$ weighted bias bound without being supplied to the algorithm. Independently clipped paired replies control centered fluctuations; bias is charged linearly instead of squared. Entropic energy then accommodates the empirical scale's jumps by recomputing the pre-query prox. Predictable masks permit probability bounds without conditioning oracle laws on future successful events. The assembled energy bound is $170KU$. These ingredients and their separate precedents must be distinguished from novelty of the complete guarantee.

A nonlinear interacting family covered by the setup is

\[
f_M(x)=M(1-x_1)+\frac L4\log\sum_j\exp(2\langle a_j,x\rangle),
\quad\|a_j\|_\infty\le1,\quad M>L.
\]

Its Hessian is $L\operatorname{Cov}_{\rm softmax}(a_j)$, giving the stated smoothness. Generic $a_j$ produce interacting coordinates. The vertex $e_1$ minimizes because every feasible coordinate transfer from coordinate 1 has derivative at least $M-L$. Its gradient is nonzero and unbounded with $M$. Thus the scope is not restricted to scalar, quadratic, separable, or stationary-optimum examples.

The stochastic logarithmic orders also have an information-theoretic diagnostic, independently of the literal baseline comparison. Consider linear objectives $f_j(x)=-\theta x_j$, with $\sigma>0$, $\theta=4\varepsilon$, $d\ge4$, and $0<\delta\le1/4$. Let an oracle reply be zero with probability $1-\eta$; otherwise it is $bZ$, where $Z$ has independent sign coordinates, coordinate $j$ has mean $-1/2$, and the others have mean zero. Choose $b=\sigma/(4\eta^{1/p})$ and $\eta=(32\varepsilon/\sigma)^q\le1/2$. The mean is $-\theta e_j$. Its central moment is bounded by
\[
b^p\big[(\eta/2)^p+\eta(3/2)^p\big]\le3\eta b^p\le\sigma^p.
\]
An epsilon-accurate simplex output has $x_j\ge3/4$, identifying $j$. Relative to the reference with all coordinates unbiased, the one-reply KL divergence is at most $\eta$; Fano's inequality therefore requires $N\eta\ge c\log d$ (up to the usual constant-size adjustment). For two different indices, the event that all replies are zero has probability $(1-\eta)^N$ and gives identical transcripts. Their success sets are disjoint, so $2\delta\ge(1-\eta)^N$, requiring $N\eta\ge\frac12\log(1/(2\delta))$. Thus in this noise-dominated regime a necessary cost is
\[
\Omega\!\left((\log d+\log(1/\delta))
\left(\frac{\sigma}{32\varepsilon}\right)^q\right).
\]
This elementary diagnostic covers arbitrary adaptive gradient-only algorithms, even given the noise parameters. Linear objectives satisfy the setup's smoothness upper bound for any positive $L$. It supports the joint dimension/confidence *orders*, with constants depending on $p$ after inversion; it neither proves optimality of the deterministic logarithmic term nor removes the unresolved literature comparison. The lower-bound argument is explanatory mathematics, not an additional public Lean theorem.

## Closest results, reductions and limitations

Nguyen et al., [NeurIPS 2023, Appendix D, Theorem D.1](https://papers.nips.cc/paper_files/paper/2023/file/4c454d34f3a4c8d6b4ca85a918e5d7ba-Paper-Conference.pdf), impose $\nabla f(x^\star)=0$; the corresponding [arXiv v2 Theorem 4.1](https://arxiv.org/abs/2304.01119v2) has different numbering. Their tuned accelerated bound specializes to $LDH^2/T^2+\sigma\sqrt D(H/T)^{1/q}$, and its parameters use the tail/noise information. Their conditional oracle formulation is broader than the stationary IID model here. Literal stochastic inversion costs $HD^{q/2}(\sigma/\varepsilon)^q$, compared with $(D+H)(C\sigma/\varepsilon)^q$ here, ignoring universal constants and small-log floors. Diameter-bias retuning gives the sharper geometry/confidence form once the required clipping-center condition is valid; it does not alone remove the stationary-optimum restriction or pay for boundary centering. The intended advance concerns unavailable update parameters, as quantified by the reductions below. There is no universal deterministic improvement: the new bound retains a $\log T$ loss.

Two centering reductions delimit the contribution. A fresh pilot median at every query, using $m=\lceil c\log(T/\delta)\rceil$ replies followed by one independent clipped reply, extends the tuned accelerated energy to arbitrary boundary optima, but costs $(m+1)T$ calls. Its per-iteration geometry improvement must not be reported as an identical actual-call improvement.

A stronger reconstructed **known-parameter** reduction uses the rolling-median center and $O(H)$ warmup, one fresh reply per iteration, and deterministic tuning
\[
U=C\left[Lk_T+\sigma T^{(p+1)/p}K^{-1/p}\right],
\qquad \lambda_t=U/t,\qquad B=C'KU/D.
\]
The horizon, $p$, and $\sigma$ are supplied to these updates. Bounded query motion gives the center error $8\sigma+24Lk_T/t$ on the median event. For $T\ge K$, a sufficiently large $C$ makes this at most $\lambda_t/2$, and the weighted clipping bias is at most $C\sigma^pT^{p+1}/U^{p-1}\le CKU$. For $T<K$, the radial clipping Lipschitz bound instead gives bias at most $10\sigma$, so its weighted sum is also at most $CKU$. An independent copy used only in the analysis bounds centered fluctuation variance by $C\sigma^pU^{2-p}T^{p+1}\le CKU^2$; it adds no actual oracle call. Bounded-martingale concentration and the tuned entropic energy yield $O(KU/T^2)$, the same deterministic and stochastic parameter orders, with $T+O(H)$ calls. This is a complete standard-reduction calculation using lagged centering, not a quoted independently published theorem or a consequence of diameter retuning alone. It retains the deterministic lag logarithm. The new algorithm replaces this unavailable deterministic scale by empirical thresholds and paired variation without losing the stochastic order.

Unknown-tail adaptation of a single mean is already available through coordinatewise median-of-means. With $m\ge c(\log d+H)$ fresh replies, its error is $O(\sigma[(\log d+H)/m]^{1/q})$ without supplying $p$ or $\sigma$ to the estimator. At an adaptive query, conditioning on the past and keeping the query fixed throughout the fresh batch preserves the pointwise moment assumption. A direct fresh-batch plug-in with $m\asymp N/T$ replies at each of $T$ accelerated steps permits a bias contribution of order $\sigma[(\log d+H)T/N]^{1/q}$, as obtained by integrating the estimator's conditional tails. It therefore does not establish the target stochastic order. A simultaneous error event for all batches ordinarily adds $\log T$ to $H$, making this displayed comparison optimistic. This is a limitation of the direct reduction, not an impossibility claim for sophisticated median-of-means compositions. The new claim concerns streaming weighted-bias and variance control, rather than adaptation of a static estimator.

Top-$K$ filtering is established: [van Erven et al., COLT 2021, Algorithm 1 and Theorem 1](https://proceedings.mlr.press/v134/vanerven21a/vanerven21a.pdf) give robust inlier regret with a raw-gradient magnitude term. That statement does not itself provide the central-noise, accelerated, empirical-threshold guarantee above. Its mechanism is credited rather than claimed as new.

A standard-reduction check combines [proxBoost, JMLR 2021](https://jmlr.org/papers/volume22/20-821/20-821.pdf) with [UniXGrad, NeurIPS 2019](https://arxiv.org/abs/1910.13857) and norm-median gradient estimation. The independent review reconstructed an elementary composite Banach extension. Put $D=\max\{1,\log d\}$, let $s=O(\log(2+LD/\varepsilon))$ be the number of doubling regularization stages, and let $m=O(\log((s+1)/\delta))$ be the number of independent confidence repetitions per stage. With base accuracy $\tau=c\varepsilon/[D(s+1)]$, each base solve uses $2n$ calls and the final gradient cleanup uses $mn$ calls, where $n=C[1+\sqrt{LD/\tau}+(\sigma\sqrt D/\tau)^q]$. The total cost is
\[
O\!\left((s+1)m\left[1+D\sqrt{\frac{L(s+1)}{\varepsilon}}
+\left(\frac{\sigma D^{3/2}(s+1)}{\varepsilon}\right)^q\right]\right).
\]
The extension treats the added regularizers as composite terms in both UniXGrad prox steps and uses norm-median gradient cleanup. It preserves simplex-only smoothness and unknown-tail updates; the base call count above is an analytical bound. These composite and heavy-tail substitutions are reconstructed proof modifications, not a theorem quoted verbatim from either paper. Thus unknown-tail adaptation, an accelerated polynomial exponent, non-Euclidean geometry, or absence of restarts alone is insufficient novelty. The quantitative joint logarithmic dependence and unavailable update parameters delimit the claimed advance. This reconstructed extension is a reduction calculation, not a quoted published theorem.

For fixed $p<2$, fixed confidence, and growing dimension, $(D+H)$ improves over the literal tuned baseline's $HD^{q/2}$. For fixed dimension and growing confidence, the two stochastic costs have the same confidence order. Relative to the reconstructed known-parameter rolling-median guarantee, the claimed benefit concerns unavailable update parameters, not a superior exponent or universally smaller cost. The deterministic/noise crossover and differing oracle models prevent a universal superiority claim.

The literature assessment covers primary ICML 2025–2026, ICLR 2025–2026, NeurIPS 2024–2025 sources, approximately the preceding two years of checked arXiv submissions/revisions through October 1, 2026, and older foundational reductions. **NeurIPS 2026 papers are excluded from the novelty assessment.** Searches located the accepted titles **“Median-of-Means under Structured Heavy-Tailed Noise: High-Probability Bounds for Clipped Stochastic Optimization”** and **“AcceleGrad#: Adaptive Geometry-Aware Acceleration”** in the [official listing](https://neurips.cc/Downloads/2026) and author pages, but their complete theorem statements and proofs were not recovered. No assumptions or scope are inferred from those titles. The contribution claim is relative to the checked literature within the stated exclusion; overlap with excluded papers remains unassessed.
