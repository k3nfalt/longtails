# Dynamic mirror acceleration under generalized smoothness

The [Lean theorem](DynamicMirrorGeneralizedAcceleration.lean) proves an explicit gradient-and-proximal oracle bound for unconstrained convex optimization in arbitrary finite-dimensional normed spaces. The contribution is an accelerated guarantee with changing local curvature and an additive generalized-smoothness transient, using a supplied strongly convex mirror geometry. It improves the curvature-parameter dependence of the applicable accelerated mirror guarantee in the regimes quantified below. Neither formalization nor the known advantages of non-Euclidean geometry are themselves novelty claims.

## Problem and available information

The [specification](../Setups/MirrorGeneralizedSmooth.lean) assumes a globally differentiable convex function `f`, with continuous derivative `g : E → E*`. For every segment on which the dual derivative norm is bounded by `M`,

\[
\|g(x)-g(y)\|_*\le (L_0+L_1M)\|x-y\|.
\]

Here `L₀ > 0`, `L₁ ≥ 0`. The norm need not come from an inner product. For twice continuously differentiable objectives the corresponding Hessian operator bound implies this segment formulation by integration. The mirror function `ψ` is globally differentiable and satisfies

\[
B_\psi(u,z)=\psi(u)-\psi(z)-\langle\nabla\psi(z),u-z\rangle
\ge \tfrac12\|u-z\|^2.
\]

Every linear perturbation of this Bregman proximal objective attains its minimum. An exact oracle returns either `g(x)` or a minimizer of `⟨v,u⟩ + Bψ(u,z)`. Each query costs one. There is no objective-value oracle, mirror-derivative oracle, stochastic assumption, or prescribed algorithm-family restriction. Exact prox access is substantive; this theorem does not assert that every mirror subproblem is cheap in arithmetic operations.

Public inputs are the normed space, `L₀,L₁,D,Δ,x₀`, where `D,Δ > 0`. A private global minimizer satisfies `Bψ(x⋆,x₀) ≤ D` and `f(x₀)−f(x⋆) ≤ Δ`. The objective, mirror function and their derivatives are private instance data; the implementation accesses them only through the permitted oracle. Accuracy `ε > 0` determines the budget, not the updates. The result is global and unconstrained: it does not automatically cover entropy mirrors at simplex boundaries or composite constrained minimizers.

These norm-based smoothness and mirror assumptions are motivated by [Yu et al., ICML 2026, Definitions 2.1 and 3.1, Theorem 3.7](https://proceedings.mlr.press/v306/yu26s.html). The affine link is a specialization of their more general link class, not a claim to cover every link. We do not require joint convexity of Bregman divergence, Hessian compatibility with the objective, or bounded sublevel sets.

## Algorithm and guarantee

The [algorithm](../Algorithms/MirrorGeneralizedAcceleration.lean) starts with `x=z=x₀`, `A=D/Δ`, and uses `R=2√D`. At each iteration it queries `g(x)` and sets

\[
M=L_0+L_1\|g(x)\|_*,\qquad
 a=\min\left\{\sqrt{A/(64M)},\frac{A}{64(1+L_1R)}\right\},\qquad
 y=\frac{Ax+az}{A+a}.
\]

It then queries `g(y)` and the proximal point

\[
z^+=\arg\min_u\{a\langle g(y),u\rangle+B_\psi(u,z)\},
\qquad x^+=\frac{Ax+az^+}{A+a},\qquad A^+=A+a.
\]

Thus a complete iteration costs exactly two derivative calls and one proximal call. The returned point is the last completed accelerated primal iterate. The finite-state implementation also defines its output between calls, retaining the previous completed point.

The public budget is exactly

\[
3\left\lceil24576\left[
1+\sqrt{\frac{2L_0D}{\varepsilon}}
+(1+2L_1\sqrt D)\log\left(2+\frac{2\Delta}{\varepsilon}\right)
\right]\right\rceil.
\]

The theorem connects this budget to `execute` and proves `f(xout)−f(x⋆) ≤ ε` almost surely under the framework's explicit algorithm/oracle product law. The supporting execution identity holds for every admissible oracle history and seed sequence; randomness is not needed. Constants are conservative proof constants, not a practical tuning recommendation.

## Proof mechanism

A single invariant controls both optimization and geometry:

\[
A_k(f(x_k)-f^*)+B_\psi(x^*,z_k)\le2D,
\qquad \|x_k-x^*\|,\|z_k-x^*\|\le2\sqrt D.
\]

The small mixing weight controls the derivative at the actual query. Strong convexity of the mirror bounds proximal displacement. Together they put both queried and returned points inside a local smoothness ball, before invoking descent. The proximal three-point identity then closes the energy induction. Primal radius containment follows from convex combinations; it does not require convexity of the second Bregman argument or an unproved restart-distance bound.

An approximate dual norming direction gives `‖g(x)‖*² ≤ 16(L₀+L₁‖g(x)‖*)(f(x)−f*)`. Consequently current curvature is bounded by `2L₀+64L₁²D/A`. The actual increment dominates `A/[4096(1+2L₁√D+√(L₀A))]`. A square-root-plus-logarithm potential proves the stated explicit iteration count. The scalar potential argument is reused from the repository; the new claim concerns the full norm/prox/curvature guarantee, not that scalar inequality.

## Closest guarantees and limits of the comparison

* [Yu et al., arXiv:2502.00753v4, equation (7) and Theorem 3.7](https://arxiv.org/html/2502.00753v4) already prove accelerated mirror descent under generalized smoothness. Write `B=Bψ(x⋆,x₀)`. Their stated error is `LB/[η T(T+1)]`, where `L=ℓ(4G)`, `τ=⌈4√(2B)L/G⌉−1`, and `η=min{1,3(τ−1)/[2(τ−3)(τ−2)]}`. The proof's equation (97) has an extra factor four; this does not affect the comparison. For the affine link, `G=2L₁Δ+√(4L₁²Δ²+2L₀Δ)`. One iteration uses one gradient and one prox. Their certified iteration expression is therefore order `1+√(LB/(ηε))`. The new method uses three calls rather than two per iteration and specializes their general link to the affine case; it covers arbitrary initial points through Bregman recentering, which leaves the prox unchanged.

For an explicit comparison take `B` comparable to `D`, `q=L₁√D≫1`, and `L₁²ε≫L₀`, with `Δ≥2ε`. Then `L=Θ(L₁²Δ)`, `τ=Θ(q)`, `η=Θ(1/q)`, and the frozen-curvature certificate costs `Θ(q^(3/2)√(Δ/ε))`. Our bound is `O(q log(2+Δ/ε))` in this regime. These are comparisons of sufficient bounds, not lower bounds on the previous algorithm.

Even granting valid restart centers with Bregman distance at most `D`, the direct halving reduction retains a larger cost. Set `δj=Δ/2^j`, `J=⌈log₂(Δ/ε)⌉`, and form `Gj,Lj,τj,ηj` by the preceding formulas with gap `δj` and distance bound `D`. Running each stage to `δj/2` uses order `1+√(Lj D/(ηj δj))` iterations, so the summed certificate is

\[
O\!\left(\sum_{j=0}^{J-1}\left[1+\sqrt{L_jD/(\eta_j\delta_j)}\right]\right).
\]

In the displayed high-curvature regime every summand is `Θ(q^(3/2))`, giving a certificate of order `q^(3/2)J`, versus our `qJ`. For example, fixing positive `D,Δ,ε,L₀` with `Δ≥2ε` and taking `L₁→∞` gives a factor `√q` improvement even against this favorable restart calculation. For a general mirror, primal gap and `Bψ(x⋆,z)` do not themselves bound `Bψ(x⋆,x)` at a restarted primal center; the calculation grants that additional property rather than asserting it. The dynamic invariant needs neither that restart property nor a frozen `η` penalty. Outside this regime the full formulas, including the `√(L₀D/ε)` term, must be compared; no universal dominance is claimed.

* [Rudomanov et al., arXiv:2610.21461v2, Theorem 3.7](https://arxiv.org/html/2610.21461v2) establish a sharper radius-only Euclidean gradient guarantee, with transient `(1+L₁R)log(2+L₁R)`. This result does not improve that Euclidean theorem. Its purpose is arbitrary supplied norm and mirror geometry, where Euclidean conversion can lose dimension-dependent factors. Our initialization-gap logarithm remains.
* [Xu and Chen, arXiv:2606.02787v1, Algorithm 1 and Theorem 4.4](https://arxiv.org/html/2606.02787v1) use dual relative smoothness and additional geometry/boundedness conditions; acceptance tests use objective differences. [Yamashita et al., arXiv:2609.34773v1, Theorem 3.5](https://arxiv.org/html/2609.34773v1) bound error through accepted parameter ratios, with objective-value tests. These are not directly executable with the oracle here. Nor do their stated parameter bounds immediately give the displayed affine-link formula. For a homogeneous squared-norm mirror and a cosh coordinate, global relative geometry constants can be infinite; simple radius localization incurs exponential curvature dependence. This excludes direct substitution, not every possible adaptation of those methods or a future sharper analysis.

All three recent arXiv sources are treated as preprints unless an acceptance record is specifically cited. The initial survey used UTC 11 November 2026, ICML and ICLR 2025/2026, NeurIPS 2024/2025, roughly the preceding two years of arXiv submissions/revisions, and older primary references. Both agents searched independently. Some HTML requests failed transiently; primary PDFs or later successful HTML requests supplied the relevant statements. This was targeted coverage, not exhaustive reading of every conference paper.

## Nonlinear geometry example

A constructed separation family, rather than a claim about a common training task, uses a Hadamard matrix of order `n≥2`, with rows `ai ∈ {−1,1}ⁿ` and variables `(u,v) ∈ ℝ²ⁿ`:

\[
h(u,v)=\log\sum_i e^{v_i}\cosh(\langle a_i,u\rangle).
\]

Subtract its tangent linear term at a private sparse point `x⋆=(u⋆,v⋆)` and add `Σj[cosh(uj−u⋆j)−1]+‖v−v⋆‖₂²/2`. Convexity gives minimizer `x⋆`. Dense scores couple coordinates. The derivative of `h` has coordinates bounded by one and its Hessian entries by one. The total function therefore has dimension-independent affine-link constants in the `ℓ₁/ℓ∞` pair. With `p=1+1/log(2n)`, norm conversion to `ℓp` costs only universal factors, and `ψ=‖·‖p²/[2(p−1)]` gives `D=O(c²log n)` for sparse shifts `x⋆=±c ej` and starting point zero. At fixed positive `c,ε`, the theorem's budget grows polylogarithmically in dimension.

For comparison with a fixed metric shared across this hidden-shift class, normalize its matrix `P` by `maxj Pjj=1`. Curvature at a minimizer is at least identity, so `L₀ ≥ λmax(P⁻¹)`. At finite selector points `u=0,vi=log(2n)`, one dense-row covariance has weight greater than `2/3`, while Euclidean gradient norm is `O_c(log n)`. Hadamard averaging and inverse-diagonal bounds imply

\[
n\le C_c[L_0+L_1\sqrt{L_0}\log n].
\]

Thus the corresponding class-uniform fixed-metric generalized-smooth conversion has complexity expression at least order `√(n/log n)` at fixed radius and accuracy. This is a limitation of that conversion, not an oracle lower bound. It does not exclude objective-adaptive metrics or other algorithms. The ordinary smooth geometry advantage is already established literature; the contribution here is preserving it with dynamic, unbounded curvature under the stated oracle model.

No optimality, universal dominance, stochastic extension, constrained extension, or parameter-free tuning claim is made. The complete public guarantee requires known smoothness, initialization and Bregman-distance bounds and exact proximal evaluations.
