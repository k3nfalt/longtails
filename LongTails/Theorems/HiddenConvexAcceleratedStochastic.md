# Accelerated stochastic optimization of hidden-convex problems with a near-affine reparametrization

Lean files:
- theorem [`HiddenConvexAcceleratedStochastic.lean`](HiddenConvexAcceleratedStochastic.lean) (`OracleTemplate.LocalHiddenConvex.result`, budget `OracleTemplate.LocalHiddenConvex.budget`);
- setup [`../Setups/LocalHiddenConvexStochastic.lean`](../Setups/LocalHiddenConvexStochastic.lean);
- algorithm [`../Algorithms/SafeguardedSimilarTriangles.lean`](../Algorithms/SafeguardedSimilarTriangles.lean);
- proofs:
  - [`HiddenConvexGeometry`](../Proofs/HiddenConvexGeometry.lean): ball projection, Taylor bound, the corrector field, and the exact hidden-convex support inequality;
  - [`HiddenConvexStep`](../Proofs/HiddenConvexStep.lean): the pathwise one-step inequality `step_bound`;
  - [`HiddenConvexExpectation`](../Proofs/HiddenConvexExpectation.lean) and [`HiddenConvexRun`](../Proofs/HiddenConvexRun.lean): the energy, its measurability, the one-sample expectation and the K-step induction;
  - [`HiddenConvexBudget`](../Proofs/HiddenConvexBudget.lean): summation estimates and budget sufficiency;
  - [`HiddenConvexExecution`](../Proofs/HiddenConvexExecution.lean): the final expected gap and the link to `execute`.

## Problem

Minimize a smooth function F over a finite-dimensional real inner-product space E, where F is
*hidden convex*: F = H ∘ c with H convex and c an invertible change of variables that the algorithm
does not know. This is the class studied by Fatkhullin, He and Hu
([arXiv 2401.00108](https://arxiv.org/abs/2401.00108), SIOPT 35(4), 2025; "FHH" below) and by
Bhaskara, Cutkosky, Kumar and Purohit
([ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/hash/c40fc068ed2b4ad43bff4f3f3206691e-Abstract-Conference.html);
"BCKP" below). Typical examples:
- convex losses seen through a smooth invertible feature map, such as an invertible residual layer
  (the main example below);
- revenue management with multinomial-logit demand, which is concave in market shares;
- policy optimization through occupancy measures.

Let 𝔅 = closedBall(x0, 2R). The assumptions (setup `spec`) are as follows. All conditions on c and H
are local to 𝔅.

1. **Hidden convexity (FHH C.1).** F = H ∘ c on ball(x0, 3R). Here c(𝔅) ⊆ U for an open set U on which
   H is convex and differentiable.
2. **Invertible Jacobian (FHH C.2, differentiable form).** For x ∈ 𝔅, c has derivative J(x), and
   μ‖v‖ ≤ ‖J(x)v‖ for all v.
3. **C^{1,1} reparametrization (BCKP Assumption A3, here local).** ‖J(x) − J(y)‖ ≤ L_J‖x − y‖ on 𝔅.
   Write M = L_J/μ.
4. **Smoothness (FHH A.1′).** F is differentiable with an L-Lipschitz gradient.
5. **Minimizer.** There is a global minimizer x* of F with ‖x0 − x*‖ ≤ R.
6. **Near-affine regime (new).** 32·L_J·R ≤ μ, that is, MR ≤ 1/32. Equivalently, the Jacobian of c
   varies by at most a small fraction of its smallest singular value over the region where the method
   operates.
7. **Oracle (FHH A.2′; repository `IsStochasticGradient`).** An IID stochastic gradient oracle: jointly
   measurable, unbiased, with variance at most σ². Only ∇F samples are available; the algorithm never
   sees H, c, J, U or x*.

Accuracy criterion: E[F(x_K)] − F(x*) ≤ ε, for the actual output x_K of the algorithm.

The algorithm receives only (L, R, σ, x0); the setup's `Public` excludes μ, L_J and ε. The method is
therefore *anytime*: its step sizes depend neither on the target accuracy nor on the horizon.

## Algorithm (`safeguardedSimilarTriangles`)

This is Nesterov's similar-triangles method (AC-SA form, Lan 2012) with a ball safeguard. It uses one
oracle call per iteration. Set τ_k = 2/(k+2) and D_k = 4L + σ(k+1)^{3/2}/R. Starting from
x_0 = z_0 = x0:

- y_k = (1 − τ_k) x_k + τ_k z_k (query point);
- z_{k+1} = Π_𝔅(z_k − ((k+1)/(2D_k)) g_k), with g_k the stochastic gradient at y_k and Π_𝔅 the
  explicit projection onto 𝔅;
- x_{k+1} = (1 − τ_k) x_k + τ_k z_{k+1}.

All queries lie in 𝔅. The output is x_K.

## Guarantee

The Lean theorem proves `Convergence spec budget` with

budget = ⌈300000 · (√(LR²/ε) + σ²R²/ε²) · log(300000 · (2 + LR²/ε + σ²R²/ε²))²⌉ oracle calls.

The underlying rate (`expected_gap`) is, for every K ≥ 1,

E[F(x_K)] − F(x*) ≤ 4 (D_K R² (20 + 6 log(K+1)) + σ R K √K / 2) / (K(K+1))
                  ≤ 16 L R² B_K / K² + 6 σ R (B_K + 1) / √K,  with B_K = 20 + 6 log(K+1).

So the complexity is O(√(LR²/ε) + σ²R²/ε²) up to log² factors, the rate of convex AC-SA. The same proof
gives the sharper factor B_K = 20 + 192·MR·log(K+1) before MR ≤ 1/32 is used. The logarithm therefore
disappears when MR·log K = O(1), but only the cruder form is formalized.

## What is new, and the mechanism

**Comparison.** On the overlap of our class with the FHH and BCKP classes (c globally C^{1,1} with a
uniformly invertible Jacobian, smooth F, stochastic gradients, and the near-affine regime):

| Result | Assumptions on the overlap | Complexity for E[F] − F* ≤ ε |
|---|---|---|
| FHH Thm 5 (projected SGD) | hidden convex, bounded U, bounded variance | Õ(L D_U²/(μ²ε) + L D_U⁴ σ²/(μ⁴ ε³)) |
| BCKP Thm 5.4 | hidden convex, C^{1,1} c, Lipschitz H, bounded stochastic gradients | O(ε^{-3}) |
| **This theorem** | hidden convex, C^{1,1} c, MR ≤ 1/32, L-smooth F, bounded variance | O(√(LR²/ε) + σ²R²/ε²) · polylog |

Neither prior bound improves when MR is small. Relative to them, in this regime:
- the statistical term improves from order ε^{-3} to ε^{-2};
- the deterministic term improves from order 1/ε to 1/√ε.

**Open questions addressed.** Both papers state these as open:
- FHH Section 7, question 1: whether their Õ(ε^{-3}) sample complexity is tight for merely convex H
  (stated for their subgradient method and projected SGD).
- FHH Section 7, question 2: is Nesterov acceleration possible under hidden convexity?
- BCKP conclusion: improving to ε^{-2} "would match the convex case".

In the near-affine regime the theorem shows that ε^{-3} is not the complexity of the problem class:
an anytime accelerated method attains ε^{-2}, matching the convex case, and acceleration is possible.
It does not decide whether FHH's bound is tight for projected SGD itself, and it does not resolve any
of these questions outside the regime.

**Why it is not a reduction to existing theory.**
- *Weak gradient domination is not enough.* Hidden convexity with bounded U implies weak gradient
  domination, F − F* ≤ (D_U/μ)‖∇F‖. For that class, Masiha, Kiyavash and Thiran
  ([arXiv 2606.28278](https://arxiv.org/abs/2606.28278)) prove Ω(ε^{-3}) stochastic and Ω(1/ε)
  deterministic lower bounds, so any improvement must use the geometry of c.
- *The objective is neither convex nor quasar-convex in the regime.*
  - Wherever c is twice differentiable, ∇²F = Jᵀ∇²H(c)J + Σ_i ∂_iH(c)∇²c_i ⪰ −L_J‖∇H(c)‖·I ⪰ −M‖∇F‖·I,
    using ‖∇H(c)‖ ≤ ‖∇F‖/μ. Negative eigenvalues occur when H has flat directions and ∇F ≠ 0.
  - For the curved-valley instance below, quasar-convexity fails with respect to *every* minimizer, for
    every γ > 0; this is proved in closed form there.
  - So quasar-convex acceleration (Hinder, Sidford and Sohoni, COLT 2020) does not apply.
  - The strong-aiming acceleration of Gupta and Wojtowytsch (ICLR 2025) needs strong aiming, which
    merely convex H does not provide.
- *Treating the curvature of c as an inexact-oracle error destroys acceleration.* The slack below
  accumulates linearly in K.

**Mechanism.**
1. *Exact support inequality.* For every y ∈ 𝔅,
   F(x*) ≥ F(y) + ⟨∇F(y), x* − y⟩ + ⟨∇F(y), q(y)⟩,
   where q(y) = J(y)^{-1}(c(x*) − c(y)) − (x* − y) satisfies ‖q(y)‖ ≤ M‖y − x*‖². Moreover q is
   Lipschitz on 𝔅 with constant 8MR (`hidden_support`, `corr_le`, `corr_lip`).
2. *Abel summation folded into the energy.* In the similar-triangles analysis, the slack term
   a_{k+1}⟨∇F(y_k), q(y_k)⟩ is rewritten through the dual increment a_{k+1}g_k = D_k(z_k − z_{k+1} − n_k).
   Here n_k is the normal component created by the projection.
   - Adding −D_k⟨z_k − x*, q(y_k)⟩ to the energy turns the slack into the increment
     D_k⟨z_{k+1} − x*, q(y_k) − q(y_{k+1})⟩.
   - Because y_{k+1} − y_k = τ_k(z_{k+1} − z_k) + τ_{k+1}(z_{k+1} − x_{k+1}), this increment is absorbed by
     the −‖z_{k+1} − z_k‖² term, up to O(MR³ D_k/k).
   - The sum of these remainders is O(MR³ D_K log K) rather than O(K).
3. *Ball margin.* Since x* ∈ closedBall(x0, R) and the safeguard has radius 2R,
   ⟨n_k, z_{k+1} − x*⟩ ≥ R‖n_k‖. This margin absorbs the normal components of the slack. This is the
   only place the regime is used; the argument cannot work beyond MR ≈ 1/4.
4. *Noise enters linearly with state-measurable coefficients.* The noise terms therefore have zero mean,
   plus (2a_{k+1}²/D_k)‖ξ_k‖². The ball keeps ‖z − x*‖ ≤ 3R, which allows the anytime step D_k.

**Lineage.** BCKP already use "query at running averages ⇒ O(1/t) movement ⇒ drift telescopes with a
harmonic log" for slowly varying preconditioners (their Section 3), and their hidden-convex algorithm
reaches only ε^{-3}. The averaging-stability idea is therefore not claimed as new. The new ingredients
are:
- its use on the nonlinear hidden-convex slack via the exact identity in step 1 and the corrector field
  q;
- the ball-margin absorption of the projection's normal components;
- acceleration together with the ε^{-2} statistical term.

## Examples

**Main family: convex losses through a near-identity residual map.** Let W ∈ ℝ^{m×d}, let φ be a
scalar C² activation applied entrywise with bounded φ′ and φ″ (for example tanh, where ‖φ′‖∞ = 1 and
‖φ″‖∞ = 4/(3√3)), and let β ≥ 0 satisfy β‖W‖²‖φ′‖∞ ≤ 1/2. Put

c(x) = x + β Wᵀφ(Wx),   F = H ∘ c,   H(u) = (1/n) Σ_i ψ(a_iᵀu − b_i),

where A = (a_iᵀ) may be rank-deficient (for example n < d) and b ∈ range(A).
- *Reparametrization constants.* J(x) = I + βWᵀdiag(φ′(Wx))W is symmetric with eigenvalues at least
  μ = 1 − β‖W‖²‖φ′‖∞ ≥ 1/2. Moreover, ‖J(x) − J(y)‖ ≤ β‖W‖²‖φ″‖∞‖W(x − y)‖ ≤ L_J‖x − y‖ with
  L_J = β‖W‖³‖φ″‖∞. Because J is symmetric and uniformly positive definite, c is the gradient of a
  strongly convex function, hence a global C¹ bijection of ℝ^d onto U = ℝ^d.
- *Regime.* MR ≤ 1/32 holds whenever R ≤ 1/(64 β‖W‖³‖φ″‖∞). The radius R can therefore be large when
  the residual branch is weak: for tanh, ‖W‖ = 1 and β = 10⁻³, any R ≤ 20 is allowed. This is a
  near-identity regime, not a tiny-neighbourhood regime.
- *A merely convex loss with no error bound.* Take ψ(t) = ∫₀ᵗ∫₀ˢ r²/(1 + r²)² dr ds. Then ψ is convex,
  ψ″ ≤ 1/4, |ψ′| ≤ π/4, and ψ(t) ≈ t⁴/12 near 0. So H is convex, smooth and Lipschitz. Its minimizers
  form the affine set {Au = b}, which is flat along null(A), and H grows only quartically away from
  that set.
  - Hence neither H nor F satisfies a PL or quadratic-growth inequality (‖∇F‖ ≤ ‖J‖‖∇H(c)‖, and
    ‖∇H‖² ~ dist⁶ while H − H* ~ dist⁴). Linear-rate PL theory therefore does not apply.
  - The minimizer set of F is the curved manifold c⁻¹({Au = b}).
  - Other losses with bounded gradients, such as Huber or logistic regression on non-separable data
    with an ill-conditioned or rank-deficient design, also fit. For them, any local PL modulus κ can be
    arbitrarily small, and our bound does not depend on κ.
- *Global smoothness.* ∇F = J ∇H(c), with ‖∇H‖ ≤ G := ‖A‖π/4 and ‖J‖ ≤ 3/2. This gives
  L ≤ (9/4)L_H + G·L_J, where L_H ≤ ‖A‖²/(4n).
- *Nonconvexity.* Wherever ∇H(c(x)) has a component along a direction where c curves, the term
  Σ_i ∂_iH(c)∇²c_i contributes negative curvature along flat directions of H, so F is nonconvex in
  general.
- *Stochastic gradients* arise from sampling one data index i, or from noisy features. Variance is
  bounded because ∇ψ and J are bounded.

**A curved valley that is nonconvex and not quasar-convex, in closed form.** Write x = (x₁, x₂, x₃, x₄, w)
with w ∈ ℝ^{d−4} and d ≥ 5. Let c(x) = x + β(‖x_{2:d}‖², 0, …, 0) and
H(u) = ½(u₁ − 1)² + ½Σ_{i=2}^{4} λ_i u_i² with λ_i > 0. Then H is flat in the w coordinates, and
F* = 0 is attained exactly on the curved manifold x̄_w = (1 − β‖w‖², 0, 0, 0, w).
- *Not quasar-convex with respect to any minimizer.* Take the test point
  x = (1 − β‖w′‖² − δ, 0, 0, 0, w′) with δ > 0. Then:
  - ∇F(x) = −δ(1, 0, 0, 0, 2βw′);
  - ⟨∇F(x), x − x̄_w⟩ = −δ(β‖w − w′‖² − δ), which is negative whenever 0 < δ < β‖w − w′‖²;
  - F(x) − F* = δ²/2 > 0.
  So for every minimizer x̄_w and every γ > 0, choosing w′ ≠ w near the ball's centre and δ small
  violates F(x) − F* ≤ γ⁻¹⟨∇F(x), x − x̄_w⟩ inside 𝔅. This holds for d ≥ 5, since one flat coordinate
  suffices to choose w′ ≠ w.
- *Nonconvex.* At the same x, take v in the w block with v ⊥ w′. Then Jv = v, the term vᵀJᵀ∇²HJv
  vanishes, and vᵀ∇²F(x)v = (u₁ − 1)·2β‖v‖² = −2βδ‖v‖² < 0. For d = 5 take w′ = 0, so every v in the
  w block works; for d ≥ 6 any w′ works.
- *Constants.* J − I = 2β e₁ x_{2:d}ᵀ, so L_J = 2β and μ ≥ 1 − 2β‖x_{2:d}‖. The regime holds for
  small β·R.

**Multinomial-logit pricing (illustration only).** Take prices p ∈ ℝⁿ, shares
s_i(p) = e^{a_i − b p_i}/(1 + Σ_j e^{a_j − b p_j}), and F(p) = −Σ p_i s_i(p).
- Revenue is concave in the share vector s (Li and Huh, MSOM 2011), so F = H ∘ s with H convex on
  U = {s > 0, Σ s_i < 1}.
- The Jacobian is J(p) = −b(diag(s) − s sᵀ), with smallest eigenvalue at least b·s₀·s_min, and
  L_J ≤ 3b². The regime therefore reads R ≤ s₀s_min/(96b).
- However, H has Hessian (1/b)[diag(1/s_i) + (1/s₀)11ᵀ] ≻ 0, so this problem is hidden *strongly*
  convex. Strongly convex methods, such as locally strongly convex AC-SA or the two-phase reduction
  mentioned below, are faster there. We include MNL only to illustrate the class and its constants,
  not as an application where this theorem is the relevant guarantee.
- We also do not verify global L-smoothness of the revenue function.

**Numerics (not part of the proof).** With H the Nesterov tridiagonal worst-case quadratic in d = 200,
c(x) = x + β v‖x‖², and MR = 1/32, at K = 3000:

| Method | σ = 0 | σ = 0.01 |
|---|---|---|
| This method | 3.5·10^{-6} | 1.2·10^{-4} |
| GD with step 1/L, or tuned SGD | 1.7·10^{-3} | 1.8·10^{-3} |

The results are similar at MR = 1/4.

## Limitations and scope

- **The result is regime-limited.** The near-affine condition MR ≤ 1/32 is a warm-start or
  near-identity condition: for a residual map it allows large R when the residual branch is weak, but
  for strongly curved c it forces a small neighbourhood.
  - Outside the regime, the best known complexity remains Õ(ε^{-3}) (FHH, BCKP).
  - Whether acceleration or ε^{-2} is possible for general hidden-convex problems is open; a lower
    bound may exist.
  - In the hidden *strongly* convex case (for example MNL pricing), a standard two-phase reduction
    already reaches the regime and strongly convex methods are faster, so no claim is made there.
  - FHH and BCKP do not require the regime. The comparison above holds only on the overlap that
    satisfies it.
- **It needs c ∈ C^{1,1}.** This is local here and global in BCKP. FHH need no differentiability of c.
- **Scope.**
  - The problem is unconstrained, with an interior minimizer; the projection is only a safeguard.
  - F is assumed globally L-smooth, and the oracle is unbiased at every query point, though only points
    in 𝔅 are queried.
  - The guarantee is in expectation only, not with high probability.
  - The rate carries log factors, and the universal constants (300000 in the budget) are not optimized.
- **Optimality.** In ε, the rate matches the convex lower bounds (Ω(√(LR²/ε)) and Ω(σ²R²/ε²)) up to
  logarithms within the regime. No claim is made about optimal dependence on M.
