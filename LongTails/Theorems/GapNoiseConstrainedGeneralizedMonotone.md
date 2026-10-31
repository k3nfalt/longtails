# Strong residual guarantees under generalized smoothness and gap-dependent noise

The [main theorem](GapNoiseConstrainedGeneralizedMonotone.lean) proves a high-probability strong tangent-residual guarantee for a constrained monotone variational inequality with generalized smoothness and finite second moments. The contribution is preserving the interpolation term proportional to `v R / ε` while replacing a uniform Lipschitz constant by polynomial dependence on generalized-smoothness parameters. It is not a new noise model, a confidence-amplification result alone, or a claim that past extragradient is the best admissible algorithm.

## Specification and scope

The [setup](../Setups/GapNoiseConstrainedGeneralizedMonotone.lean) uses an arbitrary finite-dimensional real Hilbert space, a convex feasible set `X`, a feasible initial point `x0`, and exact Euclidean projection onto `X`. Projection is an oracle channel and is charged. The supplied projection inequality implies the usual projection characterization; the algorithm does not receive projection onto an intersection with a ball.

The operator `F` is continuous and monotone on the entire ambient space. Its segment regularity assumption is

\[
 \|F(x)-F(y)\|\le (L_0+L_1 M)\|x-y\|
 \quad\text{whenever}\quad
 \|F(x+\theta(y-x))\|\le M\quad(0\le\theta\le1).
\]

Here `L0 > 0` and `L1 ≥ 0`. A single solution `xstar ∈ X` satisfies the VI, `‖x0-xstar‖ ≤ R`, and `‖F xstar‖ ≤ G`. The bounds `R > 0` and `G ≥ 0` are supplied; neither the solution nor its operator value is available to the algorithm. No strong monotonicity, bounded feasible diameter, finite-sum representation, or quasi-sharpness is assumed.

**The ambient-global domain requirement is a real restriction.** The Lipschitz baseline below assumes monotonicity and regularity only on `X`. This theorem is not a strict extension of that full class, even at `L1 = 0`. The present proof uses off-domain points in deterministic regularity arguments. All actual stochastic queries are feasible, and oracle moment assumptions are required only on `X`. Domain-only operators without a suitable ambient extension, including some barrier-type problems, are not covered; no extension theorem or necessity result for this restriction is proved.

For feasible `x`, a jointly measurable oracle `g(x,ω)` satisfies explicit integrability, unbiasedness, integrability of squared error, and

\[
 \int\|g(x,\omega)-F(x)\|^2\,dp(\omega)
 \le \sigma^2+v\langle F(x)-F(x_\star),x-x_\star\rangle.
\]

The same `xstar` occurs in the distance, operator-bound, and noise assumptions. Samples are IID under an abstract probability measure `P`, with marginal `p`; the specification does not prescribe a product measure or a finite sample space. Only second moments are assumed, not exponential tails or a samplewise bound. All parameters, including the noise bounds, accuracy `ε > 0`, and confidence `0 < δ < 1`, are available for tuning.

## Algorithm, output, and exact cost

The [algorithm](../Algorithms/GapNoisePastExtragradient.lean) performs successive regularized stages. Each trial uses projected past extragradient with a clipped batch estimate. An independent robust pilot controls the next step size; the current stochastic update does not choose its own step size. A feasibility-preserving distance guard freezes failed trials. The returned stage point is a medoid of independent trial averages. A final robust operator estimate and one projection produce the returned `output`. This is neither a last-iterate guarantee for ordinary PEG nor an accuracy claim about an inaccessible regularized solution.

The algorithm uses working radius `2R`. Every trial initialization, pilot batch, update batch, projection, repetition, final validation batch, and padding call is counted. The public definition assigns the same explicit allowance `K` to each of two channels. Thus the aggregate execution allowance is `2K`, not `K`.

For readability write

\[
 Q=1+L_1R,\qquad
 D=\frac{(L_0+L_1G)RQ^2}{\varepsilon}+Q^4,\qquad
 W=\frac{vRQ^2}{\varepsilon}+\frac{\sigma^2Q}{\varepsilon^2},\qquad
 H=1+\log\frac{2+D}{\delta}.
\]

The public budget is exactly `K = ⌈2^350 (D+W) H^5⌉`. Its Lean definition expands these quantities into one line in setup parameters. The [budget proof](../Proofs/GapNoiseBudget.lean) proves sufficiency for the actual recursive execution; `K` is not a count of idealized iterations. The huge universal constant is conservative. No claim of practical efficiency or optimized logarithmic factors is made.

Under the stated IID law, the measurable returned point `xout` satisfies

\[
 P\{x_{\rm out}\notin X\ \text{or there is no }\eta\in N_X(x_{\rm out})
       \text{ with }\|F(x_{\rm out})+\eta\|\le\varepsilon\}\le\delta.
\]

Here the normal cone uses `⟨η,w-xout⟩ ≤ 0` for all feasible `w`. The algorithm does not return or evaluate the existential normal certificate. There is no explicit dimension factor, although the supplied regularity and noise parameters can depend on dimension.

## Closest results, gains, and limitations

[Ji, Lan, and Zhu, arXiv:2609.04188v2, 17 September 2026](https://arxiv.org/html/2609.04188v2), equation (1.12), supplies the gap-dependent variance model. Their Theorem 3.1, equation (3.13), gives an expected strong-residual complexity of order `((L+v)R/ε + σ²/ε²)` up to logarithms for Lipschitz monotone VIs; Theorem 4.1 uses the exponential-tail condition (4.1) for high probability. Their assumptions are on `X`. This is the strongest directly comparable noise baseline, not an inferior uniform-variance surrogate. Accumulative regularization and robust repetition are inherited ideas; confidence amplification alone is not the novelty claimed here.

[Greenberg and Loizou, arXiv:2610.16886v1, 12 October 2026](https://arxiv.org/html/2610.16886v1), Section 2 and Theorems 3.1–3.2, analyze deterministic EG/PEG for generalized-smooth monotone VIs with restricted-gap guarantees for averages. Their constrained step-size analysis and Lemma 2.4 do not provide the finite-second-moment strong-residual guarantee above. [Chu, Liu, and Huang, arXiv:2610.14839v1, 10 October 2026](https://arxiv.org/html/2610.14839v1), Assumption 4 and Theorems 4.4/4.6, treat a finite-sum variance-reduced method with componentwise regularity and quasi-sharpness. Those assumptions and distance criteria differ from the present arbitrary stochastic oracle and merely monotone VI. These references are preprints; no conference acceptance is asserted.

[Novoselov, Dorn, Dvinskikh, and Gasnikov, arXiv:2610.12641v1, 8 October 2026](https://arxiv.org/html/2610.12641v1), Corollary 4.5, Lemma K.4, and Theorem K.6, already combine robust operator pilots, adaptive generalized steps, shrinking-ball stages, and amplification. Those components are not new here. Their generalized-smooth result assumes ambient differentiability, strong monotonicity, an unconstrained zero of the operator, and operator-relative mixed noise. Even granting compatible regularized roots, the standard conversion of a gap bound to relative noise uses `gap_H(x) ≤ ‖H(x)‖²/r`. It produces relative coefficient of order `v/r`; multiplying by the subsolver's condition-number work gives order `v L/r²`, instead of the desired inverse-linear regularization dependence. Boundary normals and access only to projection onto `X` are additional mismatches. This calculation blocks that direct substitution, not every possible improvement of their method.

On the ambient-global overlap at `L1 = 0`, the rate has the established parameter orders, with logarithmic confidence dependence under second moments. That specialization is not claimed as an independent complexity breakthrough. For nonzero `L1`, the substantive extension is polynomial generalized geometry together with the `vR/ε` interpolation dependence. The price is `Q²` on the variance-growth term and `Q` on additive noise. In the low-noise regime `σ² ≤ Q v R ε`, additive noise is no larger than the variance-growth term; at `σ = 0`, the stochastic cost has inverse-linear rather than inverse-quadratic accuracy dependence. These statements concern the displayed upper bound, not a lower bound or an optimality assertion. There is no universal superiority over Lipschitz algorithms when a useful global `L` is independently available.

Two standard reductions explain the remaining contribution. Bounding the original gap uniformly over a radius-`R` region using a local Lipschitz constant `Lloc` gives a variance term of order `v Lloc R²`; a uniform-variance residual solver then pays order `v Lloc R²/ε²`, losing the interpolation exponent. Conversely, a generalized-smooth Grönwall bound yields a ballwise constant of order `(L0+L1G) exp(O(L1R))`; applying a Lipschitz gap-noise solver that way can preserve inverse-linear accuracy but introduces exponential geometry dependence. Such an argument must also account for access to projection onto a truncated domain. Neither calculation proves that all reductions are impossible. The result supplies a polynomial bound using only the original projection oracle, without replacing the original gap noise by either surrogate.

## Technical mechanism

The proof keeps the noise gap centered at the original solution. It does not assume that a regularized root inherits the same oracle model. At a stage with regularized root `p`, original solution `s`, and regularization `r`, a shifted comparison point `z=p+τ(s-p)` yields a drift containing both a coercive distance term and a positive multiple of the original monotonicity gap. The latter absorbs the same-query variance-growth contribution. A small explicitly bounded shift error is retained.

The [two-center estimates](../Proofs/GapNoiseTwoCenter.lean), [stage energy proof](../Proofs/GapNoiseStageEnergy.lean), and [stage drift proof](../Proofs/GapNoiseStageDrift.lean) combine this shift with an optimistic potential carrying the previous estimator error. Clipping bias is bounded explicitly; clipped estimates are not assumed unbiased. A robust pilot controls future steps, and an ideal clamped process is coupled to the actual algorithm without giving it exact operator values. Failed guarded paths freeze with their energy accounted for, rather than conditioning the drift on survival.

Independent trial medoids convert contraction into stage confidence. The outer proof maintains distance to the original solution and bounds the original gap at the final validation point by a constant times `εR`. This is what makes final estimation cost proportional to `σ²/ε² + vR/ε`. The [execution proof](../Proofs/GapNoiseExecution.lean) and [probability proof](../Proofs/GapNoisePublic.lean) connect finite sample blocks, adaptive states, and the actual `execute` output under the abstract IID law. No convergence conclusion is included as a setup assumption.

## Nonlinear instances and remaining scope

A concrete family uses a dense, nonorthogonal full-row-rank matrix `A ∈ ℝ^{m×n}`, `1 ≤ m ≤ n`, feature residual `u=Ax-c`, and

\[
 F(x)=A^\top(u^{\odot3}+d),\qquad X=\{x:Ax\ge c\},\qquad d\ge0.
\]

Powers are coordinatewise. This is the gradient of a quartic feature-residual objective plus a linear term. Choose `xstar` with `Axstar=c`. Positivity of `d` gives the VI condition, the original monotonicity gap is exactly `Σᵢ uᵢ⁴`, and the boundary normal is nonzero when `d≠0`. The Jacobian `3Aᵀ diag(u²) A` is positive semidefinite globally and obeys

\[
 \|DF(x)\|\le3\|A\|^2\left(1+\|d\|+\frac{\|F(x)\|}{s_{\min}(A)}\right).
\]

Indeed, `maxᵢ uᵢ² ≤ 1+‖u³‖` and injectivity of `Aᵀ` gives `‖u³‖ ≤ ‖d‖+‖F(x)‖/smin(A)`. Thus `L0=3‖A‖²(1+‖d‖)` and `L1=3‖A‖²/smin(A)` suffice. Dense features produce interacting nonlinear coordinates; if `m<n`, null directions permit nonunique solutions. Unlike a strongly convex quotient example, this operator has vanishing derivative at the solution even on the feature quotient, so there is no positive strong-monotonicity modulus near it.

A zero-mean scalar `Z` with finite variance and a fixed compatible matrix `B` give the perturbation `Z AᵀB(u²)`. Its variance is at most `E[Z²]‖AᵀB‖² Σᵢuᵢ⁴`, so the exact gap model holds with `v=E[Z²]‖AᵀB‖²`; independent additive zero-mean noise supplies `σ²`. This describes noisy squared feature residuals, not cancellation of oracle errors over time. Constants depend explicitly on matrix norms and conditioning.

The unconstrained `d=0` variant also illustrates why gap noise is not uniformly operator-relative interpolation noise: along `u=t w`, with `AᵀB(w²)≠0` and nonzero variance of `Z`, the ratio of oracle variance to `‖F(x)‖²` grows as `t⁻²` near zero. No finite global relative-noise coefficient covers that zero-additive-noise oracle. This is a scope separation, not an oracle lower bound or proof that every regularization reduction fails. The theorem itself does not assume feature structure.

The guarantee does not establish optimal dependence on `Q`, remove the ambient extension requirement, adapt to unknown parameters, or cover Markov samples, biased oracles, and infinite-dimensional spaces. The literature refresh on 30 October 2026 found the versions listed above unchanged. The initial search covered ICML and ICLR 2025–2026, NeurIPS 2024–2025, recent arXiv work, and older operator-extrapolation and expected-cocoercivity analyses. This search is evidence for the comparison, not a proof that no unindexed or inaccessible competing result exists.

The final refresh screened the [official NeurIPS 2026 index](https://neurips.cc/Downloads/2026), supplementing the initial 2024–2025 search, and identified the listings [Median-of-Means under Structured Heavy-Tailed Noise](https://neurips.cc/virtual/2026/poster/148757) and [Normalized SGD in the Convex Regime](https://neurips.cc/virtual/2026/poster/150821). The index also lists [Dual-Space Preconditioning for Variational Inequalities and Root-Finding Problems](https://neurips.cc/virtual/2026/poster/150002). These three linked official pages were inaccessible through the browsing tool, and full-paper comparisons could not be completed despite exact-title and author-page searches. The titles alone do not establish a competing VI result. In particular, this note makes no novelty claim for robust means or confidence amplification. This access limitation remains part of the literature assessment.
