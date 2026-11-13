# A fixed multiplier cap for nonlinear coupled minimax optimization

The [Lean theorem](CoupledMinimaxCappedKkt.lean) constructs a deterministic first-order algorithm for nonlinear, nonconvex–strongly-concave minimax problems with inner coupled inequalities. It obtains ordinary ε-KKT accuracy in O(ε⁻² log(1/ε)) complete first-order calls when the problem constants and dimensions are fixed. The central contribution is a quantitative transfer from approximate stationarity on a fixed multiplier cap to feasibility and complementarity under a violated-constraints-only qualification. The inner accelerated solver and the smooth-envelope descent argument are established ingredients, not separate novelty claims.

## Problem and oracle

The [setup](../Setups/CoupledStronglyConcaveMinimax.lean) specifies

\[
\min_{x\in X}\max_{y\in Y,\ c(x,y)\le0} f(x,y).
\]

The dimensions are arbitrary finite integers. X and Y are nonempty compact convex sets with supplied starting points and diameter bounds D_X,D_Y. The objective has an L_f-Lipschitz full gradient on X×Y and is μ-strongly concave in y. Each component of c is convex in y. The full Jacobian has norm at most J and is L_J-Lipschitz. Supplied bounds G_x,G_y,C control the two objective-gradient blocks and ‖c‖. These are uniform bounds on the product domain, not only along a realized trajectory. Differentiability is ambient at domain points; no Hessian or neighborhood smoothness is assumed.

The qualification is uniform: at every (x,y)∈X×Y there is d with ‖d‖≤Z, ⟨n,d⟩≤0 for every n∈N_Y(y), and

\[
\langle\nabla_y c_i(x,y),d\rangle\le-\delta
\quad\text{whenever }c_i(x,y)>0.
\]

Here δ,Z>0 are known. The condition does not demand a descent direction for satisfied or exactly active constraints. No Slater point, feasible coupled initialization, multiplier oracle, value-function oracle, or supplied minimizer is assumed.

One complete oracle call returns f, its full gradient, c, and its full Jacobian at a queried pair. Exact projections onto the known sets are internal operations, as in the projected/proximal first-order comparison model. No evaluation outside X×Y is needed. The setup does not restrict the algorithm family. It is a problem-class upper bound, not a claim about every gradient-descent implementation.

## Algorithm, output, and exact budget

Write m for the number of constraints and define

\[
M=1+\frac{2Z(G_y+1)}\delta,\qquad
B=1+\mu+L_f+ML_J+2J,\qquad
L_\phi=B(1+B/\mu),
\]
\[
\Delta=G_xD_X+G_yD_Y+MC,\qquad
S=1+\sqrt m+M,\qquad
 t=\frac{\varepsilon}{2(1+\varepsilon)S}.
\]

The [algorithm](../Algorithms/CoupledMinimax.lean) minimizes in q=(x,λ)∈X×{λ≥0:∑λ_i≤M}, maximizes in y∈Y, and uses the Lagrangian f−λᵀc. It starts at (x₀,0). For each outer step it approximately maximizes in y by the [feasible accelerated inner algorithm](../Algorithms/CoupledMinimaxInner.lean), starting from y₀. Its queries are convex combinations of feasible iterates. The feasible estimate-sequence construction follows the Similar Triangles tradition; see [Vasin–Gasnikov–Dvurechensky–Spokoiny, arXiv:2102.02921v3, §4, Algorithm 1 and Theorem 4.7](https://arxiv.org/pdf/2102.02921v3) in the zero-noise case. The Lean proof uses conservative explicit polynomial weights and proves their potential inequality directly, rather than claiming identical tuning to that paper. A phase has

\[
k=\left\lceil4\sqrt{B/\mu}\right\rceil,
\qquad R=\left\lceil\frac{\log(2+12BD_Y/t)}{\log2}\right\rceil
\]

steps and restarts respectively, giving distance at most t/(12B) from the inner maximizer. One further gradient query defines a projected ascent cleanup b. A query at b defines the projected minimizing step with step size 1/(2L_φ). The candidate is (x⁺,b,λ⁺). After

\[
N=1+\left\lceil72L_\phi\Delta/t^2\right\rceil
\]

outer steps, the algorithm returns the candidate with smallest observed ‖q⁺−q‖. Selection requires no extra oracle call.

The actual plan uses (2+kR)N complete calls. The public theorem supplies the following simplified sufficient budget, written fully in setup parameters in Lean:

\[
\mathcal B=
\left(2+\left\lceil4\sqrt{B/\mu}\right\rceil
\left\lceil\frac{\log(2+24BD_Y(1+\varepsilon)S/\varepsilon)}{\log2}\right\rceil\right)
\left(1+\left\lceil\frac{576B^2\Delta(1+\varepsilon)^2S^2}{\mu\varepsilon^2}\right\rceil\right).
\]

The [budget proof](../Proofs/CoupledMinimaxBudget.lean) uses L_φ≤2B²/μ and proves that this budget covers the actual plan. The framework's execution may pad finished plans; the proof covers every supplied call budget at least this large. Besides oracle calls, the unpadded plan uses (kR+1)N projections onto Y and N projections each onto X and the multiplier simplex. Arithmetic and projection implementation costs are not included in the oracle budget.

For κ=B/μ and 0<ε≤1, the bound is

\[
O\!\left((1+\sqrt\kappa\log(2+BD_YS/\varepsilon))
(1+(B^2/\mu)\Delta S^2/\varepsilon^2)\right).
\]

The initialization, constraint-count, conditioning, and qualification constants are retained. In particular, large M, small μ, or large m can make this bound unattractive. There is no assertion of optimal condition-number dependence or uniform parameter dominance.

The returned point has x∈X, y∈Y, λ≥0, and

\[
\|[c(x,y)]_+\|_2\le\varepsilon,
\qquad\sum_i|\lambda_i c_i(x,y)|\le\varepsilon.
\]

There are normals n_x∈N_X(x), n_y∈N_Y(y) with

\[
\|\nabla_x(f-\lambda^Tc)+n_x\|\le\varepsilon,
\qquad\|\nabla_y(f-\lambda^Tc)-n_y\|\le\varepsilon.
\]

This is deterministic for every admissible oracle execution. The setup's almost-everywhere formulation is satisfied pointwise; it is not merely constant-probability success. The complementarity sum also bounds |λᵀc|. This is a stationarity result, not global minimax objective accuracy or an enhanced limiting-KKT guarantee.

## Why the fixed cap is valid

The [multiplier proof](../Proofs/CoupledMinimaxMultipliers.lean) explicitly derives the normal structure of the nonnegative simplex. If v is its normal at λ, there is β≥0 with v_i≤β, equality on positive multiplier coordinates, and β>0 only when ∑λ_i=M. A residual |v_i−c_i|≤e implies that β>e makes every positive-multiplier constraint violated. Applying the qualification direction and the y-stationarity residual e_y then gives

\[
\delta M\le Z(G_y+e_y).
\]

The choice of M makes this impossible for e_y≤1. Thus β≤e, and the proof yields coordinate feasibility at most 2e and total absolute complementarity at most 2Me. This argument excludes false stationary points caused by the artificial cap, including when no Slater point exists. Merely asserting a bounded optimal multiplier would not establish this approximate-stationarity transfer.

The [value proof](../Proofs/CoupledMinimaxValue.lean) derives its on-domain quadratic upper model directly from strong concavity and joint smoothness. The [outer proof](../Proofs/CoupledMinimaxOuter.lean) establishes the selected displacement bound. The [certificate](../Proofs/CoupledMinimaxCertificate.lean) transports both gradient blocks to the actual returned point; the [KKT proof](../Proofs/CoupledMinimaxKkt.lean) applies the cap lemma to the actual Jacobian. No unqueried output gradient is used by the algorithm. Its appearance in the guarantee is justified analytically.

## Closest results and scope of the gain

- [ALDER, arXiv:2611.00691v1, 31 October 2026](https://arxiv.org/html/2611.00691v1), Assumption 1(A1–A4), Assumption 2, Definition 3, and Theorem 16, is the closest baseline for the nonlinear coupled class and violated-only qualification. Its strongly-concave complete-oracle rate is O(ε⁻⁷ᐟ²). Here the fixed-cap transfer avoids accuracy-dependent penalty conditioning and gives O(ε⁻² log(1/ε)). The comparison fixes the other parameters and takes ε→0; it trades the single-loop structure for nested accelerated inner solves. ALDER is an arXiv preprint, not an established conference acceptance.
- [Lu–Mei FAL, arXiv:2512.22909v2, 5 January 2026](https://arxiv.org/html/2512.22909v2), Assumptions 1, 3, 4 and Theorem 2, gives O(ε⁻⁷ᐟ² log(1/ε)) operations. Its inner uniform Slater condition is replaced here by violated-only qualification, which permits equality pairs. FAL also handles outer nonlinear constraints and general composite terms, which this theorem does not. Compare only its outer-constraint-free indicator-function specialization. Its unconstrained minimax solver already has the ε⁻² logarithmic rate; that solver alone does not prove capped approximate stationarity implies original coupled KKT. The [journal publication](https://doi.org/10.1080/10556788.2025.2612350) is in Optimization Methods and Software. Independent comparison of v1 and v2 found no theorem or assumption change.
- [Hu–Toh–Wang–Xiao, arXiv:2408.17213v1](https://arxiv.org/html/2408.17213v1), Assumption 1.1(4), Propositions 3.9–3.10, Theorem 3.14 and §4, supplies important dualization and minimization precedents. Its relative-interior Slater/nondegeneracy assumptions and unbounded-dual stationary-point equivalence do not directly give the finite uniform cap transfer proved here. The [SIOPT publication](https://doi.org/10.1137/24M1689727) was identified, but its final full text was inaccessible; comparison is verified against the accessible preprint, not claimed against unseen final text.
- [Tsaknakis–Khanduri–Hong–Zhang, JOTA 211, article 15 (2026)](https://doi.org/10.1007/s10957-026-03098-9), Assumptions 2.1 and 3.3 and Theorem 3.4(ii), provides an ε⁻²-type dual-residual rate under stronger convex–concave/separable coupling structure and Slater. This result is not the first ε⁻² result for every coupled problem. The gain concerns general nonconvex nonlinear coupling under the stated weaker qualification.

The ancestry includes classical exact penalties and dual truncation. The proposed new step is the quantitative, violated-only, fixed-cap transfer, together with its resulting oracle guarantee. Applying known unconstrained minimax algorithms after dualization requires a justified compact multiplier domain; assuming that transfer would assume the central missing step. Standard batching, clipping, or regularization does not supply it in this deterministic model. Familiar accelerated projection techniques supply the inner solver; no novelty is assigned to their formalization.

## Meaningful nonlinear instances and limitations

A concrete family is a decision-dependent moment-constrained adversary. Let Y be a rotated box U[−R,R]^d, with r<d coordinates constrained by paired inequalities ±((Uᵀy)_i−b_i(x))≤0. Let each smooth nonlinear b_i(x) stay strictly inside (−R,R). On the remaining coordinates v, also allow the constraint ‖v‖²−a(x)²≤0 with a(x)≥a₀>0. An inward correction of the violated moment coordinates, combined with −v/‖v‖ when the ball constraint is violated, satisfies the qualification with Z=√(r+1) and δ=min(1,2a₀). It lies in the box tangent cone. The paired equalities rule out strict Slater feasibility while leaving a nontrivial adversarial subspace.

For example, smooth nonlinear h and s and a dense matrix A give a nonseparable payoff h(x)+⟨s(x),y⟩−μ‖y‖²/2−γ‖Ay‖⁴, γ≥0. Smoothness and derivative bounds are finite on compact domains. This family illustrates the established decision-dependent uncertainty question; it is not an extra restriction of the Lean setup. Neither scalar nor quadratic structure is used in the proof.

The guarantee requires known uniform bounds and exact projections. It does not cover stochastic gradients, merely concave inner objectives, additional outer nonlinear constraints, or general nonsmooth composite penalties. The qualification cannot simply be deleted: without a suitable direction, the positive simplex normal may coexist with infeasibility. The global product-domain assumption is stronger than an along-trajectory condition; the theorem does not claim the latter. The additive 1 and μ in B ensure positive tuning and B≥μ even for degenerate domains.

Literature checks were refreshed on 13 November 2026 UTC. The research and independent review surveyed the latest publicly available ICML, ICLR and NeurIPS editions and recent arXiv work, then followed older dualization, penalty, and minimax analyses. The final Hu journal text remains an explicit access limitation. No lower bound, optimality claim, or actual conference acceptance is asserted.
