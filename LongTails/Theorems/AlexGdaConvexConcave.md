# Alternating-extrapolation GDA on smooth convex–concave problems: a global constant-step guarantee with a rate

This note explains the contribution formalized in
[AlexGdaConvexConcave.lean](AlexGdaConvexConcave.lean), with
[setup](../Setups/BlockSmoothConvexConcave.lean),
[algorithm](../Algorithms/AlexGda.lean) and proofs
[AlexGdaStep](../Proofs/AlexGdaStep.lean), [AlexGdaRun](../Proofs/AlexGdaRun.lean),
[AlexGdaTuning](../Proofs/AlexGdaTuning.lean).

**Summary.** Alex-GDA (Lee, Cho and Yun, ICML 2024) is alternating gradient descent–ascent in which each
player evaluates its partial gradient at an extrapolation of the other player's iterate. It needs one
∇ₓ and one ∇ᵧ evaluation per iteration. Its (γ, δ) = (2, 1) member is the "prediction method" of Yadav
et al. (ICLR 2018) and Algorithm 1.1 of Clason, Mazurenko and Valkonen with G = F* = 0. For smooth
convex–concave objectives that are not bilinearly coupled, no global constant-step guarantee was known
to us: Lee–Cho–Yun prove a linear rate only under strong convexity–concavity and for γ, δ > 1 (their
steps depend on the moduli only through √(μy/μx), but the contraction factor tends to 1 as the moduli go
to zero, so the theorem gives no conclusion at μ = 0), and state convergence in the convex–concave case as
Conjecture 8.2.
We prove that for every γ ∈ (1, 2] and every δ ≥ 1, with constant steps of order (γ−1)/(γ²δ²L),

  Σₖ (α‖gₖ‖² + β‖hₖ‖²) ≤ (9/(2(γ−1)))·(‖x₀−x*‖²/α + ‖y₀−y*‖²/β),

where gₖ, hₖ are the two partial gradients the method computes, and that the best iterate seen so far is
an ε-stationary point after 2⌈180γ⁴δ⁴Λ²R²/((γ−1)³ε²)⌉ partial-gradient evaluations,
Λ = max(Lx, Ly) + Lxy. The proof is a Lyapunov argument with a new energy that contains a cross term and
a function-value term. The rate is the O(1/K) best-iterate rate on the squared gradient norm; it is **not**
a new complexity for the problem class and **not** a last-iterate rate (see "What is known").

## Setup and proved guarantee

- **Spaces.** E and F are real Hilbert spaces of any dimension.
- **Objective.** f : E × F → ℝ. For every y, f(·, y) is convex and differentiable; for every x, f(x, ·) is
  concave and differentiable. The partial gradients satisfy, for all arguments,

    ‖∇ₓf(x,y) − ∇ₓf(x′,y)‖ ≤ Lx‖x−x′‖,  ‖∇ₓf(x,y) − ∇ₓf(x,y′)‖ ≤ Lxy‖y−y′‖,
    ‖∇ᵧf(x,y) − ∇ᵧf(x,y′)‖ ≤ Ly‖y−y′‖,  ‖∇ᵧf(x,y) − ∇ᵧf(x′,y)‖ ≤ Lxy‖x−x′‖.

  This is the class "convex–concave with (Lx, Ly, Lxy)-Lipschitz gradients" of Lee–Cho–Yun (their
  Assumption for F(μx, μy, Lx, Ly, Lxy) with μx = μy = 0), without their twice-differentiability requirement. A saddle point (x*, y*) exists, i.e.
  f(x*, y) ≤ f(x*, y*) ≤ f(x, y*) for all x, y, and ‖x₀−x*‖² + ‖y₀−y*‖² ≤ R². Nothing else is assumed: no
  strong convexity, no bounded domain, no bounded gradients, no bilinear structure.
- **Oracle and cost.** A query is a point together with a block tag; the reply is ∇ₓf or ∇ᵧf at that
  point. Each query costs one call. The oracle returns the true partial gradients of f.
- **Success.** The output ẑ satisfies ‖∇ₓf(ẑ)‖² + ‖∇ᵧf(ẑ)‖² ≤ ε².
- **Validity.** Lx, Ly, Lxy ≥ 0, Lx + Lxy > 0, Ly + Lxy > 0, 1 < γ ≤ 2, δ ≥ 1, R ≥ 0, ε > 0.
- **Information.** The algorithm is built from (Lx, Ly, Lxy, γ, δ, x₀, y₀). R and ε enter only the budget.
- **Admissible algorithms.** The setup's `allowedAlgorithm` only admits the Alex-GDA state machine below
  with the public (γ, δ), started at (x₀, y₀) with ỹ₀ = y₀, with some constant steps α, β > 0 and the
  best-seen output. The theorem is therefore a statement about this algorithm, not about the best possible
  method for the class.

**Algorithm** (Lee–Cho–Yun, Algorithm 2). With ỹ₀ = y₀, for k = 0, 1, …:

  gₖ = ∇ₓf(xₖ, ỹₖ),  xₖ₊₁ = xₖ − αgₖ,  x̃ₖ₊₁ = xₖ − γαgₖ,
  hₖ = ∇ᵧf(x̃ₖ₊₁, yₖ),  yₖ₊₁ = yₖ + βhₖ,  ỹₖ₊₁ = yₖ + δβhₖ,

  α = (γ−1)/(4γ²δ²(Lx + Lxy)),  β = (γ−1)/(4γ²δ²(Ly + Lxy)).

Two oracle calls per iteration. The only deviation from Algorithm 2 is the output: instead of (x_K, y_K)
the method returns the iterate (xₖ, yₖ), k < K, with the smallest computed value of
mₖ = ‖gₖ‖² + ‖hₖ‖² + ‖hₖ₋₁‖² (h₋₁ = 0). This costs no oracle calls.

**Guarantee** (`theorem result : Convergence spec budget`). With

  budget = 2·⌈180·γ⁴·δ⁴·(max(Lx, Ly) + Lxy)²·R² / ((γ−1)³·ε²)⌉

oracle calls the returned point satisfies ‖∇f(ẑ)‖ ≤ ε. The supporting lemmas give, for all k,

  Vₖ − Vₖ₊₁ ≥ ((γ−1)/4)(α‖gₖ‖² + β‖hₖ‖²),  ½(‖xₖ−x*‖²/α + ‖yₖ−y*‖²/β) ≤ Vₖ,  V₀ ≤ (9/8)(‖x₀−x*‖²/α + ‖y₀−y*‖²/β),

for the energy defined below (`step_decrease`, `energy_lower`, `energy_init`), and
‖∇f(xₖ, yₖ)‖² ≤ (5/4)mₖ (`residual_le`).

## Mechanism

Write c = γ − 1, θ = (2−γ)(δ−1)/2 + 3(γ−1)/8, f* = f(x*, y*) and

  Vₖ = ‖xₖ−x*‖²/α + ‖yₖ−y*‖²/β − ⟨xₖ − x*, gₖ⟩ − c·(f(xₖ, ỹₖ) − f*) + θβ‖hₖ₋₁‖².

1. The squared distances change by 2⟨gₖ, xₖ−x*⟩ − α‖gₖ‖² and 2⟨hₖ, y*−yₖ⟩ − β‖hₖ‖². The plain distance is
   not monotone, already for bilinear f.
2. Convexity in x at (xₖ, ỹₖ) and at (xₖ₊₁, ỹₖ₊₁) towards x*, concavity in y at (x̃ₖ₊₁, yₖ) towards y*, and the
   saddle inequalities turn Vₖ − Vₖ₊₁ into

    (2−γ)·[f(xₖ, ỹₖ) − f(x̃ₖ₊₁, yₖ)] + γ·[f(xₖ₊₁, ỹₖ₊₁) − f(x̃ₖ₊₁, yₖ)] − α‖gₖ‖² − β‖hₖ‖² + θβ(‖hₖ₋₁‖² − ‖hₖ‖²).

   The cross term −⟨x − x*, g⟩ is what makes the two x-inequalities enter with weight 1 and the y-inequality
   with weight 2; the function-value term −c(f − f*) converts the remaining function values into the two
   differences above. This is where γ ≤ 2 is used (the weight 2 − γ must be nonnegative).
3. Each difference is bounded below by first-order inequalities along axis-parallel segments, e.g.
   f(xₖ₊₁, yₖ) − f(x̃ₖ₊₁, yₖ) ≥ (γ−1)α⟨∇ₓf(x̃ₖ₊₁, yₖ), gₖ⟩, and the gradients at the auxiliary points are
   compared with gₖ, hₖ through the four Lipschitz conditions, one coordinate at a time. The leading terms
   are (γ−1)·α‖gₖ‖² and (γ−1)(2δ−1)·β‖hₖ‖² minus the cost of the memory term; the errors are of second order
   in the steps and are absorbed by the step-size choice. For γ = 1 the leading coefficient vanishes: this
   is alternating GDA, which cycles on bilinear problems.
4. The certificate uses the min–max structure. With only monotonicity and Lipschitz continuity of the
   saddle operator the statement is false (an operator with a rotation inside the x-block makes the
   x-step diverge), so the result does not follow from extragradient-type operator arguments.

The energy was found by a small semidefinite search over quadratic-plus-function-value potentials on a
grid of auxiliary points and then proved by hand.

## What is known, and what is new

| source | algorithm | assumptions | guarantee |
|---|---|---|---|
| Lee, Cho, Yun, ICML 2024, [arXiv:2402.10475](https://arxiv.org/abs/2402.10475), Thm 5.1 | Alex-GDA, γ, δ > 1 | strongly-convex–strongly-concave | linear rate with factor max{1−αμx, 1−βμy}; steps α ≲ min{1/Lx, √μy/(Lxy√μx)}, β ≲ min{1/Ly, √μx/(Lxy√μy)} (μ-free when μx = μy); the factor tends to 1 as μ → 0, so no conclusion at μ = 0 |
| same paper, Conjecture 8.2 | Alex-GDA | convex–concave, (Lx, Ly, Lxy)-Lipschitz gradients | conjectured last-iterate convergence; no proof, no rate |
| Yadav et al., ICLR 2018, [arXiv:1705.07364](https://arxiv.org/abs/1705.07364), Thm 1 | prediction method = Alex-GDA (2, 1) | convex–concave, bounded gradients, **bounded iterates assumed**, steps C/√k | ergodic gap O(1/√k) |
| Clason, Mazurenko, Valkonen, Appl. Math. Optim. 2021, [arXiv:1901.02746](https://arxiv.org/abs/1901.02746), Alg. 1.1, Thm 6.1 | GPDPS; with G = F* = 0, ω = 1 it is Alex-GDA (2, 1) | three-point condition, initial point close to a solution | local convergence, no rate without strong convexity |
| Condat 2013, Vũ 2013 (linearised PDHG) | Alex-GDA (2, 1) when f(x,y) = φ(x) + ⟨Ax, y⟩ − ψ(y) | convex–concave, bilinear coupling | global convergence, ergodic O(1/K) gap |
| Shugart, Wang, Altschuler, [arXiv:2604.17145](https://arxiv.org/abs/2604.17145), Thm 3.1 | Alt-GDA with negative momentum (a different one-gradient alternating method) | convex–concave, L-smooth | averaged ‖∇f‖² ≤ 12‖z₀−z*‖²/(η²T) |
| Korpelevich; Popov; Gorbunov–Loizou–Gidel 2022; Cai–Oikonomou–Zheng 2022 | extragradient, optimistic GDA | monotone, L-Lipschitz | last-iterate ‖F(z_K)‖² = O(L²R²/K) |
| Yoon–Ryu 2021 | extra anchored gradient | monotone, L-Lipschitz | ‖F(z_K)‖² = O(L²R²/K²), optimal |
| **this theorem** | Alex-GDA, γ ∈ (1, 2], δ ≥ 1, constant μ-free steps | convex–concave, (Lx, Ly, Lxy)-Lipschitz gradients | Σₖ‖∇-terms‖² bounded; best-iterate ‖∇f‖² ≤ 180γ⁴δ⁴Λ²R²/((γ−1)³K) |

**New.** To our knowledge this is the first global guarantee for Alex-GDA / the prediction method / GPDPS
with a general (non-bilinear) smooth convex–concave coupling that needs neither strong convexity nor
bounded iterates nor a good initial point, uses constant steps, and comes with a rate. It establishes the
summability of the computed gradients, hence the convergence asserted in Conjecture 8.2 (see the next
section for what is formalized), for the whole range γ ∈ (1, 2], δ ≥ 1 with step sizes in the conjecture's
own parameters (Lx, Ly, Lxy) and α ≠ β.

**Not new, and limitations.**
- The O(1/K) rate on the squared gradient norm is the rate extragradient and optimistic GDA already have
  for the *last* iterate, and anchored methods reach O(1/K²). As an oracle complexity for the class,
  O(L²R²/ε²) is not state of the art. The contribution is the guarantee for this specific algorithm.
- The rate is for the best iterate (selected by a computed quantity). No last-iterate rate is claimed; a
  semidefinite search over one-step quadratic residual potentials found none.
- For bilinearly coupled f the (2, 1) method is linearised PDHG and its convergence is classical; the
  novelty is confined to non-bilinear coupling.
- Regularisation gives a better ε-dependence. Adding (μ/2)‖x−x₀‖² − (μ/2)‖y−y₀‖² with μ ≈ ε/R and applying
  Lee–Cho–Yun's Theorem 5.1 (μx = μy, so its steps are μ-free) gives Õ(LR/ε) calls for Alex-GDA with
  γ, δ > 1 run on the *regularised* objective, against O(L²R²/ε²) here. That reduction needs ε and R, changes
  the objective, requires γ, δ > 1 (so it excludes the δ = 1 member, i.e. the prediction method / GPDPS),
  and says nothing about Alex-GDA on f itself.
- Constants are not optimised (the steps are 4γ²δ² times smaller than 1/L-type steps).
- Parameter region. Formalized: γ ∈ (1, 2] and δ ≥ 1. Covered on paper only (next section): δ ∈ (1, 2]
  and γ ≥ 1, in particular the slice γ = 1. Not covered: min(γ, δ) > 2; (γ, δ) = (1, δ) with δ > 2
  (e.g. the setting (1, 4) used in one of Lee–Cho–Yun's experiments); and its mirror image γ > 2 with δ = 1. (γ, δ) = (1, 1) is alternating GDA and
  must be excluded.
- Two papers, "A new primal-dual hybrid gradient scheme for solving minimax problems with nonlinear term"
  (2024) and "A note on the convergence of PDHG for saddle point problem with nonlinear function" (2025),
  were accessible to us only through their abstracts; according to these they modify the extrapolation and prove local
  convergence under metric regularity. We could not check their full texts.

## Proved on paper only (not formalized)

1. **Iterate convergence** (the literal statement of Conjecture 8.2), in finite dimension. By the lower
   bound on Vₖ the iterates are bounded; by summability gₖ, hₖ → 0, so ∇f(xₖ, yₖ) → 0 and every cluster
   point z̄ is a saddle point. Applying the energy inequality with z* = z̄: Vₖ(z̄) is nonincreasing and tends
   to 0 along the subsequence converging to z̄ (the energy is bounded above by a multiple of the squared
   distance to z̄ plus terms in ‖hₖ₋₁‖), hence Vₖ(z̄) → 0 and (xₖ, yₖ) → z̄.
2. **Mirror slice.** After its first x-update, Alex-GDA with parameters (γ, δ, α, β) on f is Alex-GDA with
   parameters (δ, γ, β, α) on f̃(u, w) = −f(w, u) with u = y, w = x (uₖ = yₖ, wₖ = xₖ₊₁); for γ = 1 the
   initial extrapolated point coincides with the initial point, so the theorem applies verbatim with the
   roles of (γ, Lx, α) and (δ, Ly, β) exchanged. Hence the same guarantee, with a different constant, holds
   for δ ∈ (1, 2], γ = 1; for δ ∈ (1, 2] and γ > 1 the same argument needs the energy inequality with a
   nonzero initial memory term, which the step lemma `step_decrease` provides for every state, and in
   addition an upper bound on the initial energy with nonzero memory. That bound is elementary but is not
   formalized: `energy_init` covers only zero initial memory.

## Examples

Any smooth convex–concave saddle function with a saddle point, for instance
f(x, y) = Σⱼ log cosh(aⱼᵀx + bⱼᵀy) − ½Σⱼ(bⱼᵀy)² + xᵀCy + φ(Px) − ψ(Qy) with smooth convex φ, ψ: convex in x,
concave in y, not strongly, with non-bilinear coupling between all coordinates, in any dimension. The
dimension does not enter the bound.

## Lean layout

- [AlexGdaStep](../Proofs/AlexGdaStep.lean): hypotheses `Hyp`, the arithmetic core, the one-step energy
  decrease `step_decrease`, the energy bounds and the residual bound.
- [AlexGdaRun](../Proofs/AlexGdaRun.lean): iterates, best-seen record, proof that the state machine's
  execution with 2K calls equals the analysed recursion (`execute_alex`), telescoping and `best_bound`.
- [AlexGdaTuning](../Proofs/AlexGdaTuning.lean): the step-size conditions for the stated α, β, the passage
  from convexity/concavity and the saddle property to `Hyp`, and `alex_guarantee`.
