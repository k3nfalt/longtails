# An O(1/K) last-iterate rate for cyclic full-step incremental gradient and cyclic projections

This note explains the contribution formalized in
[CyclicGradientInterpolation.lean](CyclicGradientInterpolation.lean).

The theorem is a guarantee for one classical method: incremental gradient descent that visits m components in a fixed cyclic order and takes the full step 1/L on each. The components are convex and L-smooth and share a minimizer. After K passes the last iterate satisfies

  (1/m) Σ_j (f_j(x_K) − f_j(x*)) ≤ m³ L ‖x_0 − x*‖² / K.

Exact cyclic projections onto m closed convex sets with a common point (POCS) are the special case f_i = ½ dist²(·, C_i). For three or more sets, the best universal bound we found in the literature for this method decays as K^(−1/2). The rate 1/K was known for two sets and, by spectral arguments, for linear subspaces.

The result is a guarantee for this specific method. It is not an improved oracle complexity for the problem class: plain gradient descent on the average reaches the same accuracy with far fewer gradient calls.

## Setup and proved guarantee

The [setup](../Setups/InterpolatedFiniteSum.lean) contains the following.

- **Space.** E is a real Hilbert space of any dimension.
- **Components.** f_1, …, f_m : E → ℝ with m ≥ 1. Each f_i is convex and differentiable, and ∇f_i is L-Lipschitz.
- **Interpolation.** There is a point x* that minimizes every f_i, with ‖x_0 − x*‖ ≤ R. Uniqueness is not assumed.
- **Oracle.** A query (i, x) returns ∇f_i(x) exactly. Each query is one call.
- **Public data.** E, m, L and x_0 are known to the algorithm. R and ε enter the budget only.
- **Success.** The returned point x satisfies (1/m) Σ_j (f_j(x) − f_j(x*)) ≤ ε for a common minimizer x*.
- **Admissible algorithm.** The setup's `allowedAlgorithm` admits exactly one algorithm, the cyclic method below. The theorem is therefore a statement about that method and not about the best method for the class.

There is no bounded domain, strong convexity, finite dimension or bound on the trajectory.

**Algorithm.** The [algorithm](../Algorithms/CyclicGradient.lean) keeps a point and a call counter t. Call t queries component (t mod m) at the current point y and moves to y − (1/L) ∇f_i(y). The output is the current point. After m·K calls this is x_K, the iterate after K full passes. No averaging is used.

**Guarantee.** The public budget is

  m · ⌈m³ L R² / ε⌉

gradient calls, and the Lean theorem states that the execution with this budget returns a point with average loss gap at most ε. When R = 0 the budget is zero and the output is x_0 = x*.

The proof module also contains the following bounds, for every K ≥ 1. Let y_0 = x_K, …, y_m = x_{K+1} be the points of the pass that starts at x_K, and write B = 1 + m(m − 1).

- `Hyp.online_bound`: (2/L) Σ_i (f_i(y_{i−1}) − f_i(x*)) ≤ B ‖x_0 − x*‖² / K. The left side is the loss of each component at the point where it is about to be processed.
- `Hyp.potential` is the invariant of the proof. Its other terms are nonnegative and ‖x_1 − x*‖ ≤ ‖x_0 − x*‖, so it gives K(K − 1) ‖x_K − x_{K+1}‖² ≤ B ‖x_0 − x*‖². The displacement over one pass is therefore O(m ‖x_0 − x*‖ / K).
- `Hyp.average_le_online`: Σ_j (f_j(x_K) − f_j(x*)) ≤ L·B·(2/L) Σ_i (f_i(y_{i−1}) − f_i(x*)).

The same argument on paper gives the constant 1 + m(m − 1)/2 in the first two bounds. The Lean proof uses the cruder B, which leaves the budget unchanged.

**Lean layout.**
- [CyclicGradientStep](../Proofs/CyclicGradientStep.lean): the telescoping identities, and the one-step inequalities for a single component.
- [CyclicGradientRun](../Proofs/CyclicGradientRun.lean): the run, the per-pass inequality, the potential, the accuracy bound, and the proof that the algorithm's execution equals the analysed recursion with every call counted.

## Consequence for cyclic projections

This instantiation is argued on paper and is not formalized.

Let C_1, …, C_m be closed convex sets in a Hilbert space with a common point x*. Take f_i = ½ dist²(·, C_i). Each f_i is convex and differentiable with ∇f_i = id − P_{C_i}, which is 1-Lipschitz, and f_i(x*) = 0. The method with L = 1 is exact cyclic projection, y ← P_{C_i}(y). The bounds above read as follows, with y_i the points of the pass starting at x_K.

- Σ_i ‖y_{i−1} − y_i‖² ≤ B ‖x_0 − x*‖² / K.
- max_i dist²(x_K, C_i) ≤ (m − 1) · B ‖x_0 − x*‖² / K. This holds because dist(x_K, C_i) ≤ ‖x_K − y_i‖, and ‖x_K − y_i‖² is at most i times the sum above.
- ‖x_K − x_{K+1}‖ ≤ √B ‖x_0 − x*‖ / √(K(K − 1)).

Through the reduction of Evron et al. (2023), these bound the forgetting of weakly regularized continual linear classification on jointly separable tasks under a cyclic task order.

## Mechanism

Write η = 1/L. Let n_i = η ∇f_i(y_{i−1}) be the steps of one pass, and let primes denote the next pass. Put Δ_i = n_i − n'_i. Let c and c' be the squared displacements of the two passes. Let Ẽ = 2η Σ_i (f_i(y_{i−1}) − f_i(x*)), and let S = Σ_i ‖Δ_i‖².

1. **Fejér.** ‖y_i − x*‖² ≤ ‖y_{i−1} − x*‖² − 2η (f_i(y_{i−1}) − f_i(x*)). Hence Σ_k Ẽ_k ≤ ‖x_0 − x*‖², and Σ_i ‖n_i‖² ≤ Ẽ.
2. **Firm nonexpansiveness.** Each map id − η∇f_i is firmly nonexpansive. Applied to the pairs (y_{i−1}, y'_{i−1}), this gives S ≤ c − c'.
3. **A pass inequality.** An algebraic identity for two consecutive passes, combined with convexity and smoothness of each component at the pair (y_{i−1}, y'_{i−1}), gives

    Ẽ' ≤ Ẽ − c − c' + 2 Σ_i ⟨Δ_i, y_i − y_m⟩.

4. **Weighted sum.** By Young's inequality, k times the last term is at most k² S_k + m(m − 1) Ẽ_k. With step 2, the quantity G_k = k Ẽ_k + k(k − 1) c_k satisfies G_{k+1} ≤ G_k + Ẽ_{k+1} + m(m − 1) Ẽ_k. The terms in c cancel exactly. Summing and using step 1 gives G_K ≤ B ‖x_0 − x*‖².
5. **Loss at the common point.** f_j(x_K) − f_j(x*) ≤ 2 (f_j(y_{j−1}) − f_j(x*)) + 2L ‖x_K − y_{j−1}‖².

Fejér monotonicity and averagedness of the pass map alone give only Σ_k c_k ≤ m ‖x_0 − x*‖², which is the source of the K^(−1/2) bounds. Averagedness alone is not known to give more. Step 3 uses that each factor is a gradient step of a convex function, and step 4 couples the decay of Ẽ to the decay of c. The bound c_K = O(1/K²) is the nonlinear counterpart of the estimate ‖T^K − T^(K+1)‖ = O(1/K) that the subspace results obtain from the numerical range of a product of projections.

## Relation to prior results

Rates are for the last iterate, in the number of passes K, with R = ‖x_0 − x*‖. One pass is m oracle calls, so k = mK.

| Result | Components | Order | Bound |
|---|---|---|---|
| Evron et al., ICML 2023, [arXiv:2306.03534](https://arxiv.org/abs/2306.03534), Proposition 4.13 | two closed convex sets | cyclic | max_i dist² ≤ R²/(k + 1) |
| same, Proposition 4.13 | T ≥ 3 closed convex sets | cyclic | max_i dist² ≤ 2T² R²/√k |
| same, Theorem 4.12 | separable classification tasks | cyclic | linear rate 4 exp(−k/(16 T² ‖w*‖² R²)), problem dependent |
| Evron et al., COLT 2022, [arXiv:2205.09588](https://arxiv.org/abs/2205.09588) | T subspaces | cyclic | T²/√k and T² d/k |
| Swartworth, Needell, Ward, Kong, Jeong, [NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/d72ae75abaa70a3b19c5d4f436c680d1-Abstract.html) | T subspaces | cyclic | forgetting O(T²/K) |
| Reich and Zalas, [arXiv:2205.13843](https://arxiv.org/abs/2205.13843), Section 3 | closed convex sets | cyclic | increments o(k^(−1/2)); O(1/k) increments for subspaces only |
| Ariza-Ruiz, López-Acedo, Nicolae, [arXiv:1411.6779](https://arxiv.org/abs/1411.6779), Theorem 3.4 and Remark 3.5 | r firmly nonexpansive maps with a common fixed point | cyclic | increments ≤ ε after order r³ (R/ε)⁴ steps in Hilbert space (their p = 2); no 1/n rate |
| Evron et al. 2025, [arXiv:2504.04579](https://arxiv.org/abs/2504.04579), Theorem 14 | closed convex sets | random | expected average of ½ dist² ≤ 7R²/k^(1/4) |
| Attia, Schliserman, Sherman, Koren, NeurIPS 2025, [arXiv:2507.11274](https://arxiv.org/abs/2507.11274), Theorems 1 and 3 | convex β-smooth, interpolation, step 1/β | random, with replacement or a single pass without | O(β R²/√k) |
| This theorem | convex L-smooth, interpolation, step 1/L | cyclic | average gap ≤ m³ L R²/K |

- **Cyclic projections with three or more sets.** In oracle calls the bound here is max_i dist² ≤ m⁴ R²/k. The bound 2T² R²/√k is below the trivial bound R² only when k > 4T⁴, and in that range the new bound is smaller. Table 2 of Evron et al. (2025) still lists T²/√k as the universal cyclic bound for classification.
- **Problem-dependent linear rates.** For separable classification, Theorem 4.12 of Evron et al. (2023) gives a linear rate whose exponent degrades with ‖w*‖² R². The bound here does not depend on that quantity. It is the better of the two when ‖w*‖² R² is large, and the linear rate wins otherwise.
- **Subspaces.** Swartworth et al. prove forgetting O(T²/K) for subspaces, through a description of the numerical range of products of projections. The proof here is elementary and applies to convex sets and smooth losses, but its dependence on the number of components is worse by a factor of order m.
- **Random orders.** Attia et al. state as open whether the last iterate of SGD with step 1/β under interpolation converges at rate 1/k or 1/√k. The theorem here does not address random sampling. It shows that for a fixed cyclic order the rate in the number of passes is 1/K.
- **Small steps.** Last-iterate results for incremental gradient methods by Liu and Zhou ([arXiv:2403.07723](https://arxiv.org/abs/2403.07723)) and Cai and Diakonikolas ([arXiv:2403.06873](https://arxiv.org/abs/2403.06873)) need steps of order 1/(mL), following the average-iterate analysis of Mishchenko, Khaled and Richtárik ([arXiv:2006.05988](https://arxiv.org/abs/2006.05988)). With such steps the per-pass bound is of order L R²/K, which is better than the bound here. Those are different methods. Exact projection, or learning each task to convergence, corresponds to the full step.
- **Why two sets are special.** Alternating projection onto two sets is projected gradient descent on ½ dist². Baillon, Combettes and Cominetti ([arXiv:1102.1378](https://arxiv.org/abs/1102.1378)) show that for three or more sets the cycles of the method admit no variational characterization, so that argument does not extend.
- **Optimality in K.** Two lines in the plane at a small angle θ give dist² proportional to θ² cos^(4K) θ, which is of order R²/K for θ² ≈ 1/(2K). So the exponent of K cannot be improved. Table 1 of Evron et al. (2025) reports a lower bound T²/k for cyclic orders on subspaces.

## Instances

- Convex feasibility with polyhedra, balls or spectrahedra, in any dimension. The sets need not satisfy any regularity or transversality condition.
- Continual linear classification on jointly separable tasks, with C_i = {w : y w·x ≥ 1 on task i}.
- Block Kaczmarz with exact block projections, and continual linear regression.
- Smooth interpolating losses such as squared hinge, Huber or log-cosh losses of linear maps, with step 1/L.

With two components, or with commuting projections, the energy Ẽ is nonincreasing and the rate is immediate. With three or more non-commuting components it can grow from one pass to the next by a factor close to m, in exact worst-case computations for small instances. One- and two-dimensional quadratic examples do not show this.

## Limitations

- **Dependence on m.** The bound m³ L R²/K is not claimed to be tight. Exact worst-case computations for cyclic projections on small instances suggest linear growth in m, against m² and m³ here: K·Ẽ_K was computed for m ≤ 8 with K ≤ 4 (and K ≤ 12 for m = 3), and K·max_i dist² for m ≤ 6 with K ≤ 6 (and K ≤ 16 for m = 4). The sharp constant of the pass inequality in step 3 was computed for m ≤ 10 and is of order m, so this potential cannot give better than m².
- **Not a complexity improvement.** Gradient descent on the average reaches ε after about m L R²/(2ε) gradient calls, and small-step incremental gradient has a per-pass bound of order L R²/K. The budget here is m⁴ L R²/ε.
- **Step and order.** The step is exactly 1/L and L is known. The paper argument also covers steps below 1/L. It does not cover steps in (1/L, 2/L), which Attia et al. allow. The order is the same in every pass. Random orders and orders that change between passes are not covered.
- **Interpolation.** A common minimizer is required. Without it the full-step method does not converge.
- **Projections.** The consequence for cyclic projections is not formalized. It relies on the standard facts about ½ dist² listed above.
- **Literature.** The question is classical, and the proof is short. We found no earlier universal 1/K bound for three or more convex sets in the sources above or in searches of the projection, fixed-point and continual-learning literature. Kohlenbach (Found. Comput. Math. 2019) and Bauschke and Borwein (SIAM Review 1996) were not available to us in full. From their abstracts, the first treats the inconsistent case with a polynomial rate of degree eight, and the second treats linear convergence under regularity. An equivalent estimate in an older source under different terminology cannot be excluded.
