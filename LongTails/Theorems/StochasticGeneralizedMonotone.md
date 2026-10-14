# Finite-variance generalized-smooth monotone root finding

This result concerns an unconstrained monotone operator in an arbitrary finite-dimensional real Hilbert space. It gives a high-probability residual guarantee with polynomial generalized-smoothness dependence and an additive variance cost. The contribution is the stochastic localized extragradient contraction supporting that guarantee; accumulative regularization and robust confidence amplification are established tools.

The formal entry points are the [setup](../Setups/StochasticGeneralizedMonotone.lean), [algorithm and tuning](../Algorithms/LocalizedClippedExtragradient.lean), and [main theorem](StochasticGeneralizedMonotone.lean). The theorem returns the final confidence-selected point, not a minimum over inaccessible true residuals.

## Setup and guarantee

Let \(F:E\to E\) be continuous and monotone, with a root \(x_\star\) satisfying \(\|x_0-x_\star\|\le R\). Assume the standard 1-symmetric generalized Lipschitz condition:

\[
\|F(x)-F(y)\|\le
\left(L_0+L_1\max_{z\in[x,y]}\|F(z)\|\right)\|x-y\|.
\]

Lean expresses the maximum equivalently by quantifying over every upper bound on the segment. The oracle \(g(x,\omega)\) is jointly measurable, integrable, unbiased as a vector, and has an integrable centered squared norm with expectation at most \(\sigma^2\), uniformly in \(x\). Samples have an abstract IID path law. No samplewise continuity, Lipschitzness, monotonicity, noise symmetry, bounded sample error, quasi-sharpness, or initial residual certificate is assumed. Parameters satisfy \(L_0,L_1,R,\sigma\ge0\), \(\varepsilon>0\), and \(0<\delta<1\).

Write \(A=L_0R/\varepsilon\), \(q=L_1R\), and \(V=\sigma^2/\varepsilon^2\). The explicit public budget is

\[
K=\left\lceil 2^{60}(1+A+q^2+V)
 (1+\log(2+A+q))^3
 (1+\log((2+A+q)/\delta))\right\rceil.
\]

The returned point \(X\) satisfies \(\Pr(\|F(X)\|>\varepsilon)\le\delta\). Every raw oracle evaluation is counted. Execution at budget \(K\) makes exactly \(K\) calls: after the useful query plan finishes, fallback queries leave its output unchanged. For \(R=0\), the useful plan immediately returns \(x_0=x_\star\); the formal budgeted execution still counts its padding calls. The constants are deliberately conservative. There is no separate dimension factor beyond any dimension dependence already present in the setup parameters.

## Algorithm and new proof mechanism

For \(R>0\), set

\[
T=\lceil\log_2(1+32(A+q))\rceil+1,\quad
r_s=\frac{2^s\varepsilon}{8TR},\quad d_s=R2^{-s},\quad
B=\lceil\log_2(T/\delta)\rceil+1.
\]

Starting with anchor and center both \(x_0\), stage \(s\) solves the regularized equation \(H_s(x)=F(x)+r_s(x-a_s)=0\) approximately. Put

\[
b_s=L_1+d_s^{-1},\qquad
S_s=L_0+L_1\varepsilon+r_s(2+6L_1d_s+(L_1d_s)^2).
\]

Each trial uses \(N_s=\lceil2^{16}S_s/r_s\rceil\) extragradient steps, with two independent batches of
\(m_s=\max\{1,\lceil2^{20}\sigma^2/(r_sS_sd_s^2)\rceil\}\) samples per step. If \(G_1\) is the first regularized batch mean, use

\[
\gamma=\frac1{16\max\{S_s,b_s\|G_1\|\}},\qquad
 y=x-\gamma G_1,\qquad
 x^+=\Pi_{\mathbb B(c_s,2d_s)}(x-\gamma G_2(y)).
\]

The first half-step is unprojected. Repeat the trial independently \(B\) times, select a metric majority center, and project that selection onto the same ball. Set \(c_{s+1}\) to this output and \(a_{s+1}=(a_s+c_{s+1})/2\). All parameters and selection operations use public information and observed replies. Regularized roots occur only in the analysis. This is a nonaccelerated extragradient subsolver inside regularization continuation, not a restarted accelerated method.

The critical [stability](../Proofs/ClippedExtragradientStability.lean) and [moment](../Proofs/ClippedExtragradientMoments.lean) lemmas retain the negative half-step displacement. When clipping saturates, the displacement has fixed norm \(1/(16b_s)\); otherwise the step is \(1/(16S_s)\) and strong monotonicity supplies the drift. Combining these alternatives gives

\[
\mathbb E[\|x^+-p_s\|^2\mid x]
\le\left(1-\frac{r_s}{4608S_s}\right)\|x-p_s\|^2
 +\frac{\sigma^2/m_s}{64S_s^2}.
\]

Fresh second-batch unbiasedness cancels the correlated inner-product error after conditioning on the first batch. The stage therefore costs
\(O(S_s/r_s+\sigma^2/(r_s^2d_s^2))\), before confidence logarithms. Keeping variance additive is essential. Projection supplies integrability even on failed trials. Root transport, confidence amplification, and the internally derived IID block laws complete the argument. The [budget proof](../Proofs/ClippedExtragradientBudget.lean) bounds all stages, rounding, batches, and repetitions together.

## Closest results and scope of the improvement

- [Vankov, Nedić, and Sankar, arXiv:2410.12334v2](https://arxiv.org/html/2410.12334v2), accepted in [TMLR](https://openreview.net/forum?id=EjqSpbUBWU): Assumptions 2.1, 2.4, and 2.5 and Theorem 4.4 use generalized smoothness and finite variance, but also quasi-sharpness; the expectation-rate analysis requires \(\alpha\le1/2\). Appendix C's local extragradient estimates extend to \(\alpha=1\), but equations 163–164 and 176 use global operator-moment bounds. The present result handles general monotone roots at \(\alpha=1\), without quasi-sharpness, through the saturation drift above. This changes both the applicability and the treatment of stochastic normalization. Their full framework also covers constrained and structured non-monotone variational inequalities, which this theorem does not. The full instance classes are incomparable; the assumption comparison here concerns their monotone, unconstrained root-finding specialization.
- [Ji, Lan, and Zhu, arXiv:2609.04188v2](https://arxiv.org/html/2609.04188v2), preprint revised 17 September 2026: Proposition 1 and Theorems 2.1–2.2 supply the accumulative-regularization framework and the globally Lipschitz stochastic residual baseline \(\widetilde O(LR/\varepsilon+V)\). Theorem 4.2 also gives high-probability residual complexity under the exponential-square light-tail assumption (4.23), still with global Lipschitzness (1.2). High-probability amplification alone is not a novelty claim here. Applying these baselines after global localization can require \(L=L_0e^{O(q)}\). The new local stochastic stage replaces this exponential curvature dependence by polynomial \(q^2\). The outer regularization device itself is not claimed as novel.
- [Yoon and Loizou, arXiv:2609.36033v1](https://arxiv.org/html/2609.36033v1), September 2026 preprint: Assumption 3.4 and Corollary 3.3 give strong dual-anchor guarantees under samplewise monotonicity and uniform Lipschitzness, with repeated same-sample queries. Those conditions are absent here; their guarantee cannot simply be substituted into this oracle model.
- [Choudhury and Loizou, arXiv:2510.22421v1](https://arxiv.org/html/2510.22421v1), NeurIPS 2025: Theorem 3.6 gives deterministic generalized-smooth extragradient residual bounds. The repository's existing [anchored exact-oracle result](AnchoredGeneralizedMonotone.lean) is also a stronger deterministic comparator in applicable regimes. This contribution does not claim an improved exact-oracle rate.

The comparison is against applicable guarantees and reductions, not merely another analysis of the same algorithm. Direct robust bounded-error simulation of a deterministic local solver requires error tolerance proportional to \(r_sd_s\). It costs, up to confidence factors,
\((S_s/r_s)(1+\sigma^2/(r_s^2d_s^2))\), multiplying curvature and noise. The new stage separates these terms. Thus the improvement matters when generalized curvature is large relative to global localization, or when both deterministic work and variance are substantial. These are limitations of the specified reductions, not lower bounds on every possible method. At \(L_1=0\), the result recovers an established smooth stochastic order up to logarithms. Optimal dependence on \(q\), optimal logarithmic factors, and minimax optimality for the full class remain unresolved.

## Motivation, examples, and assumption audit

Population-monotone stochastic root finding is a standard model for equilibrium and saddle-point computation. Generalized Lipschitzness allows curvature growing with operator magnitude, including nonlinear penalties excluded by a global Lipschitz assumption. The uniform finite-variance oracle and joint measurability are inherited from the cited stochastic setting; no proof-specific structural restriction is added. Finite dimension is used for existence of regularized roots, not to restrict the nonlinear argument to scalar or quadratic models.

For a concrete interacting family in every even dimension, let \(B\) be any invertible skew-symmetric matrix and

\[
F(x)=h(\|x\|)\frac{x}{\|x\|}+Bx,
\qquad h(r)=\sinh((r-1)_+)^3,
\]

with the radial term zero at the origin. This combines a convex radial penalty with a skew equilibrium interaction. It is monotone, has the unique root zero, and its Jacobian is bounded by \(5+\|B\|+5\|F(x)\|\), giving dimension-independent generalized-smoothness parameters for fixed \(\|B\|\). On the unit ball, \(\langle F(x),x\rangle=0\) although \(F(x)\ne0\) for nonzero \(x\); hence it violates every positive quasi-sharpness bound. Dense \(B\) and the radial penalty couple coordinates. Independent additive mean-zero finite-variance noise supplies the required oracle, including unbounded noise. This example illustrates scope; the formal theorem treats every operator satisfying the specification.

The method still needs public radius, variance, and generalized-smoothness bounds. Neither parameter-free adaptation nor infinite-dimensional regularized-root existence is established. The large universal constants make the explicit implementation a theoretical guarantee, not a practical tuning recommendation.

## Literature coverage

The Researcher and Reviewer searched independently as of 7 October 2026, beginning with publicly available 2025/2026 ICML, ICLR, and NeurIPS catalogues and approximately October 2024–October 2026 arXiv submissions and revisions, then following older foundations and stronger reductions. Conference status was checked separately from arXiv availability. The comparison includes Ji–Lan–Zhu v2, revised 17 September 2026, including its high-probability Section 4.2. The independently checked ICML 2026 [GOMA paper](https://proceedings.mlr.press/v306/sohrabi26a.html), arXiv:2606.21528v2, also assumes global Lipschitzness and its Theorem 4 gives a weaker squared-residual order. Follow-up checks included [PolyakEG, v1](https://arxiv.org/abs/2609.26581v1), [Li, v1](https://arxiv.org/abs/2610.05138v1), and [relative-smoothness methods, v3](https://arxiv.org/abs/2207.09544v3); their deterministic, samplewise, or relative-geometry assumptions do not supply this guarantee.

Some virtual conference pages were robots-blocked; official proceedings and download catalogues were used instead. An unrelated acceleration OpenReview submission and an AcceleGrad# full text were inaccessible during initial screening; neither is used to certify this monotone result. Search coverage is evidence, not a claim that absence of a search hit proves novelty. The comparison above identifies the specific missing contraction and checks the standard localization and robust-simulation reductions explicitly.
