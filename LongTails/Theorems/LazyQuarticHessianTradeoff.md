# Sparse Hessian snapshots under Lipschitz third derivatives

## Result and scope

[The Lean theorem](LazyQuarticHessianTradeoff.lean) gives a joint first-/second-order oracle bound for finding an **ε-first-order stationary point** of a general nonconvex function in any finite-dimensional real Hilbert space. It does not assert second-order stationarity or global minimization.

The [setup](../Setups/ThirdDerivativeSmoothNonconvex.lean) assumes that `f` is C³, its third derivative is globally L₃-Lipschitz in the nested operator norm, and `f(x₀) − f(x) ≤ Δ` for every x. It also receives an upper bound H₀ on the norm of the Hessian at x₀. The advertised L₃, Δ, ε are positive and H₀ is nonnegative. There is no global bound on the Hessian, gradient, third derivative, or iterates. Actual zero smoothness or zero initial gap is covered by positive advertised upper bounds; the formula is not defined at zero advertised L₃ or Δ.

Two exact oracle channels return (function value, gradient) and the full Hessian, respectively. The algorithm receives the listed parameter bounds, but neither a minimizer nor the infimum value. Compared with the pure-L₃ tensor baseline, H₀ is additional advertised local-curvature information used to choose a finite inner horizon. Every C³ instance has a finite initial Hessian norm; an adaptive horizon chosen from its observed norm is not formalized here. Define

S = Δ L₃^(1/3) / ε^(4/3),
Γ = 2 + H₀Δ/ε² + L₃Δ³/ε⁴.

The explicit budgets are

- G = ceil(2⁹⁰ (1 + S^(5/4)) log Γ) ordinary value/gradient calls;
- H = ceil(2⁶² (1 + S^(3/4))) full-Hessian calls.

The output of the [algorithm](../Algorithms/LazyQuarticMetric.lean), run through the repository's `execute`, satisfies ‖∇f(output)‖ ≤ ε. Exact oracle answers make the conclusion pointwise in the random seeds; the framework records the corresponding almost-sure guarantee. Every queried interpolation point, escape candidate, unsuccessful trial, refresh, initialization query, and padding call is charged. This is an oracle-complexity theorem: dense matrix factorizations and other arithmetic are not charged.

A familiar nonlinear family in the class is quartic least squares
`f(x) = Σᵢ ((aᵢᵀx)² − bᵢ)²`, with nonorthogonal measurement vectors. Its fourth derivative is constant and its Hessian is generally unbounded. This includes interacting coordinates in arbitrary dimension, not merely separable or quadratic instances. The theorem imposes no quartic, finite-sum, or phase-retrieval structure.

## Algorithm and proof mechanism

Set β = √(L₃Δ), α = min(β/2²⁴, (L₃ε²)^(1/3)), k = β/α, q = α²/(3072L₃), r = √Δ/256, and μ = α/(64β). The stage limit is ceil(3072k²)+1 and the inner iteration limit is ceil(2¹¹√k log Γ). These choices are explicit in the implementation.

At a snapshot s, form B = ∇²f(s)+8βI and whiten by an exact square root of B. A globally nonnegative quartic Taylor upper polynomial controls the third derivative relative to B. Polarization and Taylor's theorem then establish uniform relative Hessian control inside a B-ball of radius r. A Hessian is refreshed only when an active stage center has moved more than r/4 from the snapshot in that metric.

Each stage applies guarded accelerated estimate sequences to `F(x)=f(x)+α‖x−c‖²`. The regularizer is Euclidean even though acceleration uses B. Support checks either justify the estimate sequence or expose a pair with negative Euclidean curvature. Truncating a proposed gradient step before it exits the certified region yields sufficient decrease; the proof never assumes local smoothness beyond that region. Two interpolation queries control the witness endpoint values, and four symmetric escape queries provide progress. All selections use already queried values.

The proved local alternative is a faithful point with either gradient norm at most ε or decrease D≥q and movement `μ‖x_new−c‖²_B ≤ 256D`. The anisotropic regularizer, Euclidean witness conversion, guarded queries, and this movement estimate must hold together. A plain coordinate change in an isotropic accelerated theorem would require a transformed gradient tolerance ε/√Bmax and introduce unwanted polynomial curvature dependence.

For nonterminal stages, `√(μq)‖x_new−c‖_B ≤ 16D`. A distance potential pays for refreshes even when many small displacements align. The objective ledger freezes when a terminal output is produced, so no objective decrease is assumed at that output. This gives at most `1 + 64Δ/(r√(μq))` Hessian calls before rounding to the displayed budget. Prior progress bounds the path before each snapshot; Taylor expansion from x₀ then bounds the required metric curvature. H₀ enters the inner contraction requirement only through log Γ. The [trace proof](../Proofs/LazyQuarticTrace.lean), [ledger](../Proofs/LazyQuarticLedger.lean), and [budget proof](../Proofs/LazyQuarticBudget.lean) connect these facts to actual query execution.

Quartic coefficient inequalities, polarization, accelerated estimate sequences, and scalar interpolation are established ingredients. The claimed contribution is their integrated realization of the displayed joint oracle tradeoff for the pure-L₃ class, rather than any one of these ingredients or its formalization.

## Closest guarantees and the improvement regime

The comparison is between problem-class guarantees with their actual oracle access, not artificially restricted algorithm families. No `allowedAlgorithm` restriction is imposed.

| Prior result | Relevant assumptions and output | Comparable cost and distinction |
|---|---|---|
| Carmon, Duchi, Hinder, Sidford, [*Convex Until Proven Guilty*, ICML 2017](https://proceedings.mlr.press/v70/carmon17a.html), Theorem 2 and supplement Lemmas 3, 5–7 | Global L₁-Lipschitz gradient and L₃-Lipschitz third derivative; first-order stationarity | Ordinary calls of order Δ√L₁ L₃^(1/6) ε^(-5/3), up to logarithms. Our class removes global L₁ but adds counted Hessian access. On the common class their rate is S^(5/4)√(L₁/β); we do not improve it when L₁ is small. |
| Hinder, [*Cutting Plane Methods Can Be Extended into Nonconvex Optimization*, COLT 2018; arXiv v2](https://arxiv.org/html/1805.08370v2), Section 5 after Theorem 5 and Lemma 5 | Local gradient smoothness on queried balls, global third-derivative Lipschitzness; the first-order-only variant omits the Hessian test | Localizing the theorem using the initial Hessian and Taylor bounds gives approximately dS value/gradient calls, with curvature in logarithms. This is a standard reduction to our class, not a separately claimed new theorem. It is a stronger baseline than naive finite-difference simulation of a tensor method. |
| Doikov and Grapiglia, [arXiv:2510.07992v1, 9 October 2025](https://arxiv.org/abs/2510.07992v1), published in [Mathematical Programming, 8 July 2026](https://link.springer.com/article/10.1007/s10107-026-02386-6), published Theorem 2 and Corollary 1, equations (61)–(63), p=3 | Globally Lipschitz third derivative, initial gap; first-order stationarity | Approximately d^(1/3)S+d second-order oracle calls. The finite-difference tensor uses d shifted Hessians plus a base Hessian; the published accounting reuses the full oracle at the next point and charges at most 1+b calls per inner block, with reuse period b=2d+1. This b is distinct from our Hessian cost m. The +d initialization is retained. |

Let m≥1 be the cost of a full Hessian relative to a value/gradient query. Ignoring universal constants and displaying logarithms separately, our weighted cost is `S^(5/4) log Γ + m S^(3/4)`, plus initialization terms. The two pure-L₃ baselines above cost approximately `dS` and `m(d^(1/3)S+d)`. For S,d≥1, a polynomial joint improvement survives when

`d ≫ S^(1/4)` and `S^(1/4)/d^(1/3) ≪ m ≪ d S^(1/4)`,

with enough slack to absorb logarithms. For example, m=d and d≥S^(1/2) give an asymptotic factor of order S^(1/4) over the localized cutting-plane bound, up to logarithms. Taking H₀/β at most polynomial in S and d makes this logarithmic qualification explicit, since Γ=2+(H₀/β)S^(3/2)+S³. These are asymptotic regimes, not practical thresholds for the stated constants. On the globally L₁-smooth overlap, comparison with Carmon's bound additionally requires sufficiently large L₁/β and `m ≪ S^(1/2)√(L₁/β)`. There is no universal superiority claim.

Standard reductions were checked. Central gradient differences approximate each Hessian column with error at most L₃h²/6; 2d gradients therefore give operator error at most √d L₃h²/6. Thus Hessian information is not intrinsically unavailable to first-order algorithms, and no separation is claimed merely from exact Hessian access. A robust finite-difference version of the present algorithm is not formalized. Likewise, solving a quartic model is not treated as a free oracle operation: this implementation constructs progress through the explicitly counted first-order queries above.

## Limitations and literature coverage

This result advances a theoretical oracle tradeoff, not a practical second-order optimizer. Its conservative α cap forces an enormous worst-case stage count, the public constants are very large, and full dense Hessians are used rather than partial Hessian queries. The fixed-budget framework continues ordinary padding queries after a terminal point is found; early termination does not reduce the literal `execute` cost. No wall-clock, numerical stability, finite-precision, stochastic-oracle, second-order-stationarity, or optimality guarantee is proved.

The literature assessment was made on 17 October 2026 UTC. The initial independent surveys covered ICML 2025/2026, ICLR 2025/2026, NeurIPS 2024/2025, and approximately the preceding two years of arXiv work, then followed foundational citations. Both agents subsequently screened the public [NeurIPS 2026 listing](https://neurips.cc/Downloads/2026) and relevant official poster pages; this was supplementary coverage, not part of the initial survey. Candidate-specific checks included Doikov's recent lower-order/tensor implementations, quartically regularized methods, lazy Hessian methods, generalized-smoothness saddle escape, and lower bounds. Conference status was checked against official proceedings/OpenReview; arXiv-only work was not counted as accepted conference work. The comparison above retains the strongest applicable older baselines. The supplementary screen checked [lazy semismooth Newton](https://arxiv.org/abs/2602.08069v1), Assumption 1 and Theorem 3.2: its global result uses a Lipschitz gradient and uniformly bounded generalized Hessian, with an O(k^(-1/2)) residual rate. [AdaCubic](https://arxiv.org/abs/2604.09437v1), Section 3, uses stronger lower-derivative smoothness and local convergence analysis. The official [weak-AICN poster](https://neurips.cc/virtual/2026/poster/150741) explicitly treats convex weak-learner optimization under semi-strong self-concordance; its full OpenReview PDF was inaccessible in the Researcher’s recheck, so no detailed theorem comparison with that PDF is asserted. The supplementary [spectral-preconditioning paper](https://arxiv.org/html/2605.11850v1) uses global gradient smoothness in Assumption 4.2 and Theorems 4.3/4.5; its deterministic Theorem B.0.7 assumes anisotropic smoothness and proves sufficient decrease for its regularized gap. The official [target-noise curvature-recovery poster](https://neurips.cc/virtual/2026/poster/154444) was screened at abstract level only; it concerns model-specific access to perturbed targets and GGN/ReLU curvature recovery. Its full theorem statements were not verified. These checks did not supply a dominating guarantee for the general nonconvex pure-L₃ class.

Additional checks included [QQR, Mathematical Programming 2025](https://doi.org/10.1007/s10107-025-02235-y), Theorem 2.9; [CQR, Mathematical Programming 2024](https://doi.org/10.1007/s10107-024-02176-y); and [arXiv:2504.20259v2, 22 July 2026](https://arxiv.org/abs/2504.20259v2). Their quartic-model machinery does not by itself supply the displayed charged inner-stage/refresh tradeoff. Lower bounds assuming a Lipschitz Hessian or globally bounded third derivative do not automatically certify optimality for the pure-L₃ class here. No lower bound matching the joint frontier is asserted. Literature comparisons and significance remain distinct from the Lean correctness audit.
