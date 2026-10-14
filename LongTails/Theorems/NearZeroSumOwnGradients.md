# Accelerating near-zero-sum games with own-action gradients

The result concerns two-player games with costs `h(x,y) + g(x,y)` and `g(x,y) - h(x,y)`. The competitive component `h` is strongly convex in the first player's variable and strongly concave in the second; the shared component `g` is jointly convex and smooth. The algorithm receives only the paired own-action gradients

\[
F(x,y)=(\nabla_xh+\nabla_xg,\,-\nabla_yh+\nabla_yg).
\]

It does not receive either component separately, the other-player derivatives of either cost, or a solution. This is a centralized oracle allowing coordinated joint queries. The result does not establish decentralized or uncoupled learning, or a communication guarantee.

The formal specification is [NearZeroSumGames.lean](../Setups/NearZeroSumGames.lean), the algorithm and its explicit tuning are in [NearZeroSumFoam.lean](../Algorithms/NearZeroSumFoam.lean), and the main result is [NearZeroSumOwnGradients.lean](NearZeroSumOwnGradients.lean). The algorithm returned by the theorem is `nearZeroSumGameOutput`.

## Assumptions and guarantee

The feasible set is a nonempty compact convex product `X × Y` in arbitrary finite-dimensional real inner-product spaces. Its Euclidean diameter is at most `D`, and a feasible initial point is supplied. Let `μ, ν > 0` be the respective strong convexity and concavity parameters of `h`. Both full utility gradients `∇(h+g)` and `∇(h−g)` are `L`-Lipschitz on the domain; `∇g` is `δ`-Lipschitz there. The public parameters satisfy `μ,ν ≤ L`, `0 ≤ δ ≤ L`, and `D,ε > 0`. These are uniform bounds, not necessarily sharp constants. The specification also states Nash existence; under the other assumptions it is redundant.

Differentiability is expressed using gradient witnesses within the feasible domain. No interior, full-dimensionality, or global smooth extension is assumed. A within-gradient witness need not be unique, but its inner products with feasible displacements are fixed. The proof uses precisely those directional identities. The model includes the ordinary smooth games considered in the comparison papers; no equivalence with every ambient extension formulation is claimed.

A query returns either `F(z)` at a feasible joint point or the exact Euclidean projection of an arbitrary point onto `X × Y`. Each paired gradient query and each joint projection query costs one. The theorem counts both. The utility decomposition and its gradient witnesses are private instance data, unavailable to the algorithm. All curvature, smoothness, diameter and accuracy bounds used for tuning are public; there is no parameter-adaptivity claim.

Write `m = min(μ,ν)` and `M = max(μ,ν)`. The returned feasible point satisfies

\[
\|z_{\rm out}-z_\star\|^2\le\varepsilon
\]

for a Nash equilibrium, with at most

\[
\left\lceil
2^{24}\frac Lm
\sqrt{\frac{m+\delta}{\mu+\nu+\delta}}
\log\!\left(2+\frac{D^2}{\varepsilon}\right)
\log\!\left(2+\frac{2^{19}L^2D^2}{m^2\varepsilon}\right)
\right\rceil
\]

total oracle calls. The guarantee holds for every oracle seed sequence consistent with the exact oracle, and hence also satisfies the framework's almost-sure accuracy specification. It concerns the explicitly projected final output, not an average or an existentially selected iterate.

The universal constants are conservative. The contribution is the oracle-information requirement and the parameter dependence, not a constant-factor improvement.

## Closest results and the contribution

[Luo, Stich and Chatterjee, *Monotone Near-Zero-Sum Games: A Generalization of Convex-Concave Minimax*](https://proceedings.iclr.cc/paper_files/paper/2026/file/af45b5019c9f9aef730ba98b4b84b592-Paper-Conference.pdf), ICLR 2026, Theorem 1, Algorithm 1 and Appendix E, establish the near-zero-sum acceleration under this shared-cost structure. Their method uses the separated competitive and shared gradients, including shared-cost derivatives not recoverable from a single own-action-gradient reply. Its polynomial complexity, suppressing the stated accuracy logarithms, is

\[
\frac L{\sqrt{\mu\nu}}+
\frac Lm\min\left\{1,\sqrt{\frac\delta{\mu+\nu}}\right\}.
\]

The ICLR bound includes the two logarithms `log(LD²/(mε))` and `log(D²/ε)` in its nontrivial accuracy regime, and uses the same squared-distance accuracy criterion. It counts gradient queries; our displayed budget also counts every projection.

The present bound has equivalent polynomial dependence, up to universal constants, while using only `F` and projection. It does not improve that paper's full-information polynomial rate. The missing-information question is inferred from the scope of its theorem and algorithm; it is not presented as an open problem explicitly stated by those authors. Their Section 4.2 already motivates competition with small common incentives, so the game model itself is not claimed as new.

Applying a standard strongly monotone extragradient analysis directly to `F` gives the scale `(L/m) log(2+D²/ε)`, since the paired field is `m`-strongly monotone and at most `2L`-Lipschitz. Our polynomial factor is smaller when `m+δ` is small relative to `M`. Accounting for the extra logarithm, a sufficient asymptotic improvement regime is

\[
\sqrt{\frac{m+\delta}{M+m+\delta}}
\log\!\left(2+\frac{L^2D^2}{m^2\varepsilon}\right)=o(1).
\]

For `δ = Θ(m)` and `L = Θ(M)`, the polynomial dependence changes from `M/m` to `√(M/m)`. The extra accuracy/initialization logarithm remains. There is no uniform superiority claim when the curvatures are balanced, when `δ` is comparable to `M`, or for all accuracy regimes.

For `δ=0`, `g` is affine along feasible segments and the problem is strategically zero-sum. [Kovalev and Gasnikov, NeurIPS 2022, *The First Optimal Algorithm for Smooth and Strongly-Convex–Strongly-Concave Minimax Optimization*](https://papers.neurips.cc/paper_files/paper/2022/file/5e2ed801f62102f531d109d7c6e1b62f-Supplemental-Conference.pdf), Algorithm 4 and Theorem 3, supply the FOAM algorithm and complexity baseline. Algorithm 2 and Lemmas 1, 5–7 are the sources of the accelerated proximal proof structure. The uniform proximal construction here retains two logarithms; it does not improve the known one-log zero-sum rate.

[Lee, Ryu and Yun, *Nesterov Acceleration with Operator Decomposition*](https://arxiv.org/abs/2604.11105), version 1, April 13, 2026, Theorem 4.1 and Section 4.2, is treated as a preprint; no accepted venue was verified in this check. Its decomposition guarantees require access to separate gradient and monotone-component oracles, possibly at different points. Its single-oracle equivalence in the bilinear case does not establish a general nonlinear `F`-only guarantee for the class here. The trivial accessible split using the gradient of `m‖z‖²/2` leaves an `O(L)` monotone remainder and the extragradient conditioning scale. We do not claim to resolve every nonlinear decomposition question in that paper.

The feasible inner residual solver is established work: [Cai, Oikonomou and Zheng, ICML 2024](https://proceedings.mlr.press/v235/cai24f.html), Appendix E of [arXiv:2206.05248v6](https://arxiv.org/abs/2206.05248v6), December 4, 2024. Its projected anchored extragradient mechanism is formalized here as a supporting ingredient. Its known residual rate, ordinary proximal-point contraction, and the formalization itself are not novelty claims.

## New proof mechanism and execution

The new step is an own-gradient perturbation analysis of FOAM that retains enough primal curvature to absorb the inaccessible shared-gradient correction. For an ordered, weakly coupled subproblem, set `a=M/2`, `b=m/2`, `α=√(m/M)` and `c=b−δ`. Write `G=∇g`. With `x★` fixed only in the analysis, define

\[
\widehat\phi(x,y)=h(x,y)+g(x,y)-a\|x\|^2/2+b\|y\|^2/2,
\]
\[
V(x,z,y)=\|z\|^2/(2a)+b\|y\|^2/2+
\langle z,x\rangle-\widehat\phi(x,y)+2g(x_\star,y).
\]

The proof evaluates this potential only at feasible triples satisfying `z=F_x(x,y)−ax+n_X`, with `n_X` a normal-cone vector, and at the equilibrium triple. It requires no conjugate maximizer or potential evaluation at infeasible slow iterates. Pairwise support inequalities retain the `a`-weighted first-player displacement and the `c`-weighted second-player displacement. The inaccessible correction is

\[
e=2\bigl(G_y(x,y)-G_y(x_\star,y)\bigr),\qquad
\|e\|\le2\delta\|x-x_\star\|.
\]

Those retained terms absorb its two cross-products whenever `8δ² ≤ aαc`, yielding contraction `1−α/2` with the accessible field. The reference equilibrium and the decomposition appear only in the proof, never in a query, update, stopping rule or output.

For general `δ`, the algorithm uses proximal subproblems for the entire accessible field, with `β=m+16δ`. Their curvatures are `Mr=M+β`, `mr=m+β`, and their paired-field Lipschitz bound is `LF=2L+β`. The subproblem acceleration parameter is `α=√(mr/Mr)`. The small-coupling condition then holds automatically. This is regularization of the original operator, not an assumption that the original game already satisfies `δ≤m/8`.

Each FOAM step solves an accessible strongly monotone auxiliary variational inequality by projected anchored extragradient. It first projects its anchor, makes `K=⌈2048 LF/Mr⌉` inner iterations, and obtains a normal-cone residual relative to the anchor displacement. All gradient queries are feasible, including on domains with boundary or empty interior. One FOAM step costs `4K+2` calls. Initialization uses two gradient queries and one projection, and the returned output uses one final projection. Thus `J` FOAM steps cost exactly `4+J(4K+2)` calls before any execution padding. The explicit outer count `N`, inner count `J`, and all padding are covered by the public budget.

Initialization uses a projected forward step and bounds its normal-corrected residual by `2 LF D`. It needs no bound on the initial gradient norm. The projected FOAM output has squared error at most

\[
\frac{64L_F^2D^2}{M_r m_r}(1-\alpha/2)^J.
\]

The chosen `J` makes this at most `m²ε/(16mr²)`. The outer resolvent contracts by `β/mr`; the accumulated inner error and the initial-distance term are each at most `√ε/4`. Swapping coordinates and changing `h` to `−h` handles the opposite curvature ordering with exactly the same query count.

## Nonlinear scope and limitations

A concrete motivating family is a regularized primal–dual game with a shared penalty. On a primal ball and a nonnegative dual box, take

\[
h(x,y)=\tfrac M2\|x\|^2+
\sum_i y_i(\tfrac12\langle x,Q_i x\rangle-b_i)
-\tfrac m2\|y\|^2-\sum_j\log\cosh((Vy+r)_j)
\]

plus private affine terms, with positive semidefinite `Q_i`, and let

\[
g(x,y)=\gamma\sum_j\log\cosh((Cx+Dy-s)_j).
\]

Dense, noncommuting `Q_i` and dense matrices give interacting nonlinear instances in arbitrary primal and dual dimensions at least two. Private affine terms and shifts avoid an artificially known equilibrium at the origin. For primal radius one, `q` dual coordinates with bounds `1/√q`, `Q_i=(M/√q) Q̄_i` with `‖Q̄_i‖≤1`, a rank `q−1` matrix `V` with `‖V‖²=M`, `‖[C D]‖=1`, and `γ=m`, the bounds `μ=M`, `ν=δ=m`, `L≤4M`, and diameter at most `√5` hold. Dimension enters through the stated operator norms and domain diameter; the theorem has no additional dimension factor.

The competitive curvature in the weak block can still be of order `M`, so elementary block normalization does not automatically reduce the ordinary extragradient condition number to `√(M/m)`. Also, generic `g_xy≠0` gives a saddle-integrability defect `2g_xy` in `F`, excluding a direct zero-sum reformulation by opponent-only utility terms. These observations show substantive scope and rule out specific easy reductions. They are not lower bounds or standalone evidence of novelty. With dual regularization, a bounded dual box and a shared penalty, the game's equilibrium is not automatically a solution of the original unregularized constrained program.

No optimality claim is made for the reduced-information oracle. A matching lower bound and removal of the extra logarithm remain unresolved. Exact projections and known tuning bounds are substantive oracle assumptions. Stochastic gradients, biased feedback, noncompact domains and more than two players are outside this result.

The literature check used October 13, 2026 UTC: ICML 2025/2026, ICLR 2025/2026, the publicly available NeurIPS 2025/2026 listings and accessible papers, approximately October 2024–October 2026 arXiv submissions/revisions, and foundational citations. The closest ICLR paper was checked against its final proceedings version and arXiv:2512.02690v1; the decomposition comparison was checked at arXiv:2604.11105v1. Both arXiv histories still listed only version 1 at the focused follow-up check. Some OpenReview pages and NeurIPS 2026 poster pages were inaccessible; accessible official proceedings, arXiv papers and official acceptance listings were used where available. Inaccessibility or failure to find a paper is not treated as evidence of novelty.
