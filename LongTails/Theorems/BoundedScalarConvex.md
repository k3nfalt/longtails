# Constant-step scalar SGD: contribution and scope

This note explains the contribution formalized in
[BoundedScalarConvex.lean](BoundedScalarConvex.lean), with the
[setup](../Setups/BoundedScalarConvex.lean) and
[algorithm](../Algorithms/ScalarSgd.lean).

For a convex, H-Lipschitz objective on a nonempty bounded closed interval C,
let x₀ belong to C and satisfy |x₀ − x⋆| ≤ R for some minimizer x⋆ in C.
Here H > 0 and R ≥ 0 are supplied bounds. Oracle responses Yₜ satisfy
|Yₜ| ≤ H almost surely, and their conditional means are valid relative
subgradients at the queried point. The setup requires joint measurability
and states this contract for every feasible predictable query process,
conditioning on the revealed-seed filtration `past O t`. State, time, and
history dependence are permitted subject to this explicit contract; IID
sampling, time homogeneity, and a fixed subgradient selection are unnecessary.

The algorithm is ordinary projected SGD with one constant step size:

$$
X_{t+1}=\Pi_C(X_t-\eta Y_t).
$$

It returns the actual last iterate, with one oracle call per iteration. For
every η > 0 and integer T ≥ 1, the supporting proofs establish

$$
\mathbb E[f(X_T)-f(x_\star)]
\le \frac{R^2}{2\eta T}+\frac{25}{2}\eta H^2.
$$

For ε > 0, the public theorem chooses

$$
\eta=\frac{\varepsilon}{25H^2},\qquad
K=\max\!\left\{1,\left\lceil\frac{25H^2R^2}{\varepsilon^2}\right\rceil\right\},
$$

and proves expected error at most ε after exactly K oracle calls. For R > 0,
the horizon-based choice η = R/(5H√T) gives 5HR/√T. The algorithm does not
require objective values, the minimizer, or conditional means. Scalar median
and quantile estimation with bounded subgradient responses provide natural
examples, including nonsmooth objectives with flat or nonuniform slope profiles.

The specific novelty claim concerns the finite-time last iterate of this
constant-step algorithm under general convexity and adapted bounded responses:

- [Liu and Lu, §4.1 and Theorem 4.10](https://arxiv.org/pdf/2106.14588)
  obtain an optimal-order finite-time scalar bound with an additional
  near-linearity assumption. The present result removes that objective
  restriction. Their Theorem 4.12 treats general convex objectives through
  an asymptotic stationary result for a specific lattice oracle, rather than
  this finite-time adapted-oracle guarantee.
- [Beretta et al., Theorem 2 and §7](https://arxiv.org/html/2606.24879)
  give a scalar result with additive, state-independent, time-homogeneous
  finite-variance noise and explicitly leave the uniformly bounded-gradient
  case unsettled. The present result addresses that case on bounded intervals.
  Its almost-sure response bound is stronger than a finite-variance assumption,
  while its permitted dependence is broader; neither oracle class contains the
  other in general.
- [Koren and Segal, Open Problem 1 and §3](https://proceedings.mlr.press/v125/koren20a/koren20a.pdf)
  identify the fixed-dimensional constant-step last-iterate question and
  analyze a special scalar objective and oracle.

The new proof mechanism uses a finite family of threshold-specific stop-loss
(positive-part hinge) supersolutions built from local convex secants.
Objective-weighted telescoping controls arbitrary variation in slope scale.
Together these yield uniform terminal objective-excursion control under adapted
bounded responses, without an invariant law or an order-preserving transition.
Conditional restart arguments, reflection, and the usual regret bound then
give the stated rate. The classical hinge representation and regret argument
are not themselves claimed as new.

Averaging and suitable decreasing-step schedules already attain O(HR/√T).
The contribution is therefore an optimal-order guarantee for the actual last
iterate of unmodified constant-step scalar SGD, not a new minimax complexity
for optimization algorithms generally. Relative to a generic bound of order
R²/(ηT) + ηH² log T, the result removes the horizon logarithm from the second
term. After optimizing each bound over η, the comparison is O(HR/√T) versus
O(HR√(log T/T)), with a meaningful asymptotic improvement for positive H and R.
The constants are not claimed sharp.

The scope is one dimension, bounded intervals, almost-sure bounded responses,
and accuracy in expectation with a horizon- or accuracy-tuned constant step.
There is no higher-dimensional, unbounded-domain, general finite-variance,
high-probability, or anytime guarantee. The K ≥ 1 safeguard covers R = 0 and
other degenerate cases conservatively; no zero-noise optimality is claimed.
The revealed-seed contract is explicit and does not assert a representation
theorem for every abstract history-dependent oracle. These comparisons record
the independent literature review supporting the result; they do not guarantee
the absence of unknown prior work or actual conference acceptance.
