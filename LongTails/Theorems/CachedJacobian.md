# Cached Jacobians for a tangent-residual guarantee

The [Lean theorem](CachedJacobian.lean) constructs [CachedJacobian.output](../Algorithms/CachedJacobian.lean) for the [LipschitzJacobianMonotone specification](../Setups/LipschitzJacobianMonotone.lean). It bounds operator-value and full-Jacobian queries separately for a general nonlinear monotone variational inequality. Its contribution is a mixed information-oracle tradeoff, not an arithmetic or wall-clock speedup.

## Problem, information, and guarantee

Let X be a known nonempty compact convex subset of an arbitrary finite-dimensional real inner-product space, with diameter at most D and a known anchor x₀∈X. The operator F is differentiable at every point of X, monotone on X, and has L-Lipschitz Jacobian on X in operator norm. L,D,ε>0 and an integer relative Jacobian price m≥1 are supplied to the algorithm. There is no bound on the magnitude of F or its Jacobian, no strong monotonicity, no potential-function assumption, and no interior or full-dimensionality requirement on X. An affine operator is covered by any positive Lipschitz upper bound L; the theorem does not optimize a separate L=0 case.

The two exact oracle channels return F(x) and J(x), respectively. All value calls cost one unit and each Jacobian call costs m units when forming the weighted comparison. The formal budget is the pair of channel counts. The setup imposes no method-family restriction. Known-domain operations and solves of known affine strongly monotone VIs are free in this information model. The algorithm does not query the unknown nonlinear resolvent, a solution, or a normal-cone oracle.

Writing Q=LD²/ε and A=mQ, the explicit public budgets are

- G ≤ ⌈100000(1+√A)(1+log(2+A))⌉ value calls;
- H ≤ ⌈20000(1+√(Q/m))(1+log(2+A))⌉ Jacobian calls.

The returned **last inner iterate** u belongs to X and satisfies

    ∃ n∈N_X(u), ‖F(u)+n‖≤ε,

where N_X(u)={n: ⟨n,z−u⟩≤0 for every z∈X}. The public output is the point u; the proof constructs its normal witness from the final affine solve. It does not expose a normal certificate as a second output. The guarantee holds for every oracle seed and hence almost surely under the framework's execution distribution. The algorithm itself is deterministic. Thus G+mH=Õ(m+√(mQ)); the displayed formulas retain startup, logarithms, rounding, and all padding calls. These conservative constants are not a practical performance claim.

## Algorithm and proof mechanism

Set a=1/(16384mLD), T=⌈1024√(mQ)⌉+1, and ℓ=2⌊log₂(T+1)⌋+4. At outer index t=0,…,T−1, use ηₜ=a(t+3)/3 and anchor weight βₜ=2/(t+2). With previous output u, form c=(1−βₜ)u+βₜx₀. Starting at u, take exactly ℓ affine-resolvent steps. A cached pair (s,J(s)) is refreshed before a step at w precisely when ‖w−s‖ exceeds the fixed radius R=1/(16Lη_{T−1}). The next point v solves

    0 ∈ F(w)+J(s)(v−w)+(v−c)/ηₜ+N_X(v).

The new normal is the negative of the displayed affine expression, and F(v) is queried. There are two queries per inner step: a Jacobian query when refreshing, otherwise a charged dummy value query, followed by the value query at v. There is one initial value query and one initial Jacobian query. The total plan length is exactly 2+2Tℓ. The implementation uses `execute` with the separately proved channel budgets.

The local chord contraction and Halpern energy algebra are established ingredients. The additional mechanism is their globally certified coupling across successive proximal subproblems. A finite-prefix energy estimate gives ‖F(uₜ)+nₜ‖≤40D/[a(t+1)²] whenever the already completed inner certificates have error at most D/T². That estimate implies a distance at most 56D/t from the previous output to the next exact proximal root. Consequently ηₜL times the warm-start distance is uniformly small **from initialization**, despite ηₜ increasing. The cache condition then gives quarter contraction and a computed certificate after ℓ steps. Strong induction establishes the certificate at every index without assuming future solver success or access to the root.

The refresh proof counts movement of the **computed inner iterates**. A cache-distance potential pays for each actual refresh, and contraction bounds each inner solve's travel by 5/3 of its initial root distance. Summation yields

    H ≤ 1+3200LDη_{T−1}(1+log T).

The normal-cone argument and affine-VI existence work even on lower-dimensional domains. In particular, positive semidefiniteness of the Jacobian on feasible differences is derived at boundary points from two feasible approaching rays; it is not added as an assumption. Supporting modules separate [energy algebra](../Proofs/CachedJacobianHalpern.lean), [geometry](../Proofs/CachedJacobianGeometry.lean), [prefix convergence](../Proofs/CachedJacobianOuter.lean), [tuning](../Proofs/CachedJacobianTuning.lean), [inner execution](../Proofs/CachedJacobianExecution.lean), [actual trajectory convergence](../Proofs/CachedJacobianConvergence.lean), [query accounting](../Proofs/CachedJacobianCounts.lean), and [budget simplification](../Proofs/CachedJacobianBudget.lean).

## Closest results and scope of improvement

The assumptions are the standard compact monotone Lipschitz-Jacobian class studied in high-order VI complexity. They are not an invented stability restriction or a restriction to a particular implementation. The closest exact-derivative residual baselines are:

- Xinliang Zhang et al., [*Optimal High-Order Methods for Solving Monotone Variational Inequalities*, arXiv2609.23557v1, September 20, 2026](https://arxiv.org/html/2609.23557v1), Theorem 3.1 and Sections 4–5: O(Q^(2/5)) second-order calls for tangent residual. Section 4 supplies the general anchored energy framework; Section 6 discusses lazy/inexact extensions. This is a preprint, not a verified conference acceptance.
- Haihan Zhang et al., [arXiv2609.13462v2, October 19, 2026](https://arxiv.org/html/2609.13462v2), Theorem 3.3: Õ(Q^(2/5)) via extrapolated Halpern and strong-subproblem solvers. This is also a preprint. The comparison uses its upper-bound construction, not an endorsement of its lower-bound claims.
- Chen et al., [*Second-Order Min-Max Optimization with Lazy Hessians*, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/f71fe50bece9e9532203e3eb2223b152-Paper-Conference.pdf), [arXiv2410.09568v2](https://arxiv.org/html/2410.09568v2): lazy extragradient and restarted strongly monotone solves. Its weak-gap bound is not directly a tangent-residual guarantee.

A stronger baseline than merely charging m for every fresh high-order call is the **derived composition** of the latest residual framework with the lazy strongly monotone solver. For N outer calls its weighted cost is, up to logarithms and constants,

    mN + m^(2/3)Q^(2/3)N^(−2/3).

This follows by substituting the restarted lazy solver and using the weighted root-distance energy bound in Lemma 5.1 of arXiv2609.23557v1. Optimizing N gives Õ(m+m^(4/5)Q^(2/5)). This is a reconstructed baseline, not a claim that a paper states this exact formula. Comparing only with the fresh bound Õ(mQ^(2/5)) would overstate the gain.

The new bound improves that lazy-composition upper envelope when m is polynomially larger than Q^(1/3), while m is polynomially smaller than Q so that startup does not dominate. It sacrifices exact-jet-optimal dependence when Jacobians are cheap. For example, Q=m² gives new weighted exponent m^(3/2), compared with m^(8/5) for the optimized lazy composition. Logarithmic factors must also be accounted for near regime boundaries. These are comparisons of upper bounds, not oracle lower bounds or an optimality theorem.

Dimension-dependent methods are another essential comparison. Standard cutting-plane VI methods (see [Nemirovski's lectures, Lecture 6, Propositions 6.2.1–6.2.2](https://people.orie.cornell.edu/miketodd/Lect_EMCO.pdf)) combined with regularization and a projected residual-recovery step yield a competing Õ(m+d) information bound on well-conditioned known domains. One initial Jacobian controls a Lipschitz bound; derivative magnitude and domain geometry enter logarithmically. Thus a meaningful simultaneous improvement requires d polynomially larger than √(mQ), as well as Q^(1/3)≪m≪Q. The example Q=m², d=m² satisfies both comparisons on balls or boxes. No universal advantage over cutting planes is claimed for arbitrary geometry.

The distinction from ordinary proximal-point tracking is substantive: its usual energy controls total movement only at a square-root-in-iteration scale, insufficient for this refresh count. Fixed-resolvent inexact Halpern analyses, including [Yang et al., arXiv2610.05742v1, October 5, 2026](https://arxiv.org/html/2610.05742v1), Theorem 4.2, do not supply a derivative-query implementation or this cross-subproblem reuse ledger. The new claim is the globally valid mixed-query upper bound obtained by the coupled schedule and computed-path accounting, not novelty of chord iteration, anchoring, or their individual inequalities.

## Natural instances and limitations

A genuinely nonlinear, nonseparable family is

    F(x)=Kx+Σⱼ aⱼ φⱼ′(aⱼᵀx)+b,

on a compact ball or box, with K skew-symmetric, dense interacting vectors aⱼ, and convex smooth φⱼ such as softplus. Monotonicity follows from the positive semidefinite symmetric part. One may take L=Σⱼ‖aⱼ‖³ sup|φⱼ'''| on the relevant intervals. Arbitrarily large skew K does not alter this L. The theorem does not require a separable operator, a quadratic, a fixed dimension, or a particular representation of this family. The example establishes concrete nonlinear scope; it is not by itself an efficient implementation theorem.

The improvement regime is intrinsically one of **separately priced derivative information**. If m is proportional to d, as in a common dense-Jacobian arithmetic estimate, the preceding simultaneous improvement regime disappears. Batched or parallel differentiation does not automatically fix this: both oracle prices must use the same resource normalization. Compact representations or separately priced derivative services motivate studying the mixed information frontier, but this theorem neither guarantees such representations nor bounds the arithmetic of its exact affine-VI solves. It therefore does not establish a universally cheap practical second-order method.

The result is deterministic and dimension-free in its displayed query bounds, but requires exact derivative replies, supplied L and D, known compact geometry, and the chosen relative price m. It gives no noisy-oracle extension, unknown-parameter adaptation, finite-precision guarantee, or matching lower bound. No assumptions on cumulative oracle errors, trajectory stability, or an unknown solution are imposed. The logarithmic overhead and large constants are retained explicitly.

The literature assessment used the current UTC date October 25, 2026: targeted screening of the two latest publicly available ICML, ICLR, and NeurIPS editions (including the public 2026 programs), approximately October 2024–October 2026 arXiv submissions/revisions, and cited older foundations. Official proceedings/programs were used to distinguish conference papers from preprints. Some virtual conference pages were robot-blocked; official downloads/proceedings and primary arXiv texts supplied alternatives. This is targeted coverage, not an exhaustive proof that no unlocated work exists. The novelty claim is limited to the precise mixed-query result and comparison above.
