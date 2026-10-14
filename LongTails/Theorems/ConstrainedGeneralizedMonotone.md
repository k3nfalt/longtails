# Constrained monotone variational inequalities with (L0, L1)-Lipschitz operators: an O(1/ε) residual rate

Lean files: theorem [`ConstrainedGeneralizedMonotone.lean`](ConstrainedGeneralizedMonotone.lean)
(`OracleTemplate.ConstrainedMonotone.result`, budget `OracleTemplate.ConstrainedMonotone.budget`), setup
[`../Setups/ConstrainedGeneralizedMonotone.lean`](../Setups/ConstrainedGeneralizedMonotone.lean), algorithm
[`../Algorithms/ConstrainedAnchoredExtragradient.lean`](../Algorithms/ConstrainedAnchoredExtragradient.lean)
(`constrainedAnchored`), proofs
[`../Proofs/ConstrainedAnchoredStep.lean`](../Proofs/ConstrainedAnchoredStep.lean) (projection facts, the one-point lemma, one
iteration), [`../Proofs/ConstrainedAnchoredRun.lean`](../Proofs/ConstrainedAnchoredRun.lean) (invariants: potential, residual,
distance), [`../Proofs/ConstrainedAnchoredRate.lean`](../Proofs/ConstrainedAnchoredRate.lean) (operator-norm bound, step growth,
accuracy) and [`../Proofs/ConstrainedAnchoredExecution.lean`](../Proofs/ConstrainedAnchoredExecution.lean) (execution, call counts,
assembly).

To our knowledge, the theorem gives the first rate for solving **constrained** monotone variational inequalities whose operator is only
(L0, L1)-Lipschitz. An anchored extragradient method with projections and an observable step rule returns a point x ∈ X
together with a certificate ξ ∈ N_X(x) satisfying ‖F(x) + ξ‖ ≤ ε, after

    O( (L0 + L1 G)(1 + L1 R) · R/ε + (1 + L1 R)² · log(2 + (L0 + L1 G0) R/ε) )

evaluations of F and as many projections, where R ≥ ‖x0 − x*‖, G ≥ ‖F(x*)‖ and G0 ≥ ‖F(x0)‖. All constants are polynomial.
Choudhury and Loizou ([NeurIPS 2025, arXiv:2510.22421](https://arxiv.org/abs/2510.22421)) list the constrained setting as an open
direction in their conclusion ("does not handle the constrained setup").

## Setup

[`ConstrainedGeneralizedMonotone`](../Setups/ConstrainedGeneralizedMonotone.lean), on a real inner-product space E of any
dimension (no completeness is used):

- **Operator.** F : E → E is continuous and monotone on all of E, ⟨F x − F y, x − y⟩ ≥ 0, and satisfies the 1-symmetric
  (L0, L1)-Lipschitz condition: if ‖F‖ ≤ M on the segment [x, y] then ‖F x − F y‖ ≤ (L0 + L1 M)‖x − y‖. This is Assumption 1.1
  (α = 1) of Choudhury–Loizou and the condition of Vankov, Nedić and Sankar
  ([ICML 2024, PMLR 235:49137–49170](https://proceedings.mlr.press/v235/vankov24a.html)); it is the same first-order form as the
  repository setup [`GeneralizedLipschitzMonotone`](../Setups/GeneralizedLipschitzMonotone.lean). With L1 = 0 it is ordinary
  L0-Lipschitz continuity.
- **Constraint.** X ⊆ E is convex and is accessed through an exact projection oracle: some map P with P z ∈ X and
  ⟨z − P z, w − P z⟩ ≤ 0 for all w ∈ X answers every projection query. Projections are counted.
- **Solution data.** x0 ∈ X with ‖F(x0)‖ ≤ G0; a solution x* ∈ X of the variational inequality, ⟨F(x*), w − x*⟩ ≥ 0 for all w ∈ X,
  with ‖x0 − x*‖ ≤ R and ‖F(x*)‖ ≤ G. The validity conditions are L0, R, ε > 0 and L1, G, G0 ≥ 0. G is typically positive:
  at a constrained solution F need not vanish.
- **Information.** The public input is (E, L0, L1, x0); R, G, G0 and ε are parameters of the budget only, so the Lean types
  guarantee that the method does not use them.
- **Cost and success.** Oracle 0 evaluates F, oracle 1 projects onto X. Success means that the returned point x lies in X and
  that some ξ with ⟨ξ, w − x⟩ ≤ 0 for all w ∈ X (a normal vector) satisfies ‖F(x) + ξ‖ ≤ ε, that is,
  dist(0, F(x) + N_X(x)) ≤ ε (the tangent residual). The method also returns ξ implicitly: it is the normal vector produced by its
  last projection.

**Important scope condition.** F must be defined, monotone and (L0, L1)-Lipschitz on all of E, not only on X: the method evaluates
F at the unprojected half step and the key lemma tests monotonicity at points near x* that may lie outside X. This is the standard
setting of the (L0, L1)-VI papers above (which work on R^d), but it excludes operators defined only on X.

**Instances.** Constrained convex minimization with an (L0, L1)-smooth objective (F = ∇f, for example ℓ1- or simplex-constrained
Poisson and exponential-loss regression, Σ_i exp(⟨a_i, x⟩) − b_i⟨a_i, x⟩), where the guarantee is a projected-gradient-type
stationarity certificate; and convex–concave saddle problems with polynomially growing terms and bilinear coupling, such as
min_{w1 ∈ X1} max_{w2 ∈ X2} ‖w1‖^{p+1}/(p+1) + w1ᵀBw2 − ‖w2‖^{p+1}/(p+1) (the operator of Example 3 of Choudhury–Loizou, which is
(L0, L1)-Lipschitz but not Lipschitz), with box or ball constraints. In both cases F(x*) ≠ 0 whenever a constraint is active.

## Algorithm

[`constrainedAnchored L0 L1 x0`](../Algorithms/ConstrainedAnchoredExtragradient.lean) keeps x ∈ X, a normal vector ξ ∈ N_X(x)
(initially 0) and an accumulated step S (initially 0); the anchor is a = x0. One iteration makes three calls:

    g = F(x)                                               (call: F)
    p = g + ξ,  m = ‖g‖ + ‖p‖ + ‖x − a‖/S                  (the last term is 0 when S = 0)
    γ = 1/(4(L0 + L1 m)) if S = 0, else min{S/3, 1/(4(L0 + L1 m))};  t = S/(S + γ),  β = γ/(S + γ)
    y = x + β(a − x),  z = y − tγ p,  h = F(z)             (call: F; z need not lie in X)
    w = y − γ h,  x⁺ = Π_X(w),  ξ⁺ = (w − x⁺)/γ             (call: projection)
    (x, ξ, S) ← (x⁺, ξ⁺, S + γ)

The output is the current x. With X = E (so ξ = 0) this is the repository's unconstrained anchored extragradient method
([`AnchoredGeneralizedMonotone`](AnchoredGeneralizedMonotone.md)); with a constant step it is the fast extragradient method of
Lee and Kim (NeurIPS 2021). Using the normal vector of the previous projection inside p is the device of Cai, Oikonomou and Zheng
for constrained extra-anchored methods (NeurIPS 2022). There is no restart, line search or phase switch.

## Guarantee

The Lean theorem `result : Convergence spec budget` certifies, with

    n = ⌈16 (L0 + L1 G)(1 + 8 L1 R) R/ε + (132 L1 R (1 + L1 R) + 4) · log(2 + 8R(L0 + 2 L1 G0)/ε)⌉ + 1

iterations, a budget of 2n evaluations of F and n projections; the returned point lies in X and has tangent residual at most ε.
Expanding, the leading term is 16(L0 + L1 G)R/ε + 128 L1 (L0 + L1 G) R²/ε, and the start-up term is
O((1 + L1R)² log((L0 + L1 G0)R/ε)), in which G0 enters only through the logarithm.

## Mechanism and the new step

Write T = F + N_X (monotone and set-valued, 0 ∈ T(x*)), p_k = F(x_k) + ξ_k ∈ T(x_k) and L* = L0 + L1 G.

1. **Potential.** With V = (S²/2)‖p‖² + S⟨p, x − a⟩, the anchored identity of the unconstrained proof holds verbatim with
   q = F(z) + ξ⁺ and r = F(x⁺) + ξ⁺: the normal vector ξ⁺ cancels in r − q = F(x⁺) − F(z), and monotonicity of T gives the cross
   term. The observable step rule keeps both extragradient segments inside the (L0, L1) trust region of the last observed operator
   value, so V decreases by (3/8)Γ²‖q − tp‖². Hence S_k‖p_k‖ ≤ 2R, which is the certified residual.
2. **Distance control under projections.** Anchored methods are not Fejér monotone, and a projected step mixes the large normal
   component of F into the distance recursion. The potential bounds every single step, (S + γ)‖q − tp‖ ≤ (7/6)R, so the only error
   term in the projected distance recursion is at most (7/6)βR‖x⁺ − x*‖; it is absorbed by the anchor contraction and
   ‖x_k − x*‖ ≤ 3R for all k ([`ConstrainedAnchoredRun`](../Proofs/ConstrainedAnchoredRun.lean), `inv_step`).
3. **One-point co-coercivity for monotone (L0, L1) operators (the new lemma, `one_point`).** For all x, y and every
   0 < ε with L1 ε ≤ 1/2,

       ‖F x − F y‖ · ε ≤ ⟨F x − F y, x − y⟩ + 2(L0 + L1‖F y‖) ε (‖x − y‖ + ε).

   It follows by testing monotonicity of the pair (x, y + εv) with v the direction of F x − F y, and using the (L0, L1) condition
   only in the ball of radius ε around y. No segment between x and y, no differentiability and no gradient structure are needed;
   it replaces the co-coercivity of gradients, which monotone operators lack. The idea of testing monotonicity at nearby points is
   classical (local boundedness of monotone operators); the quantitative (L0, L1) form is, to our knowledge, new.
4. **Operator-norm bound along the run.** At y = x*, monotonicity of N_X gives
   ⟨F x_k − F x*, x_k − x*⟩ ≤ ⟨p_k, x_k − x*⟩ ≤ 6R²/S_k, and the lemma with ε = R/(1 + 2L1R) gives
   ‖F(x_k)‖ ≤ G + 8L*R + 6R(1 + 2L1R)/S_k. This is the step that fails in the unconstrained proof once F(x*) ≠ 0: there,
   ‖F(x_k)‖ is itself the residual. Without it, the step sizes could only be bounded through the Lipschitz constant of F on the
   ball B(x*, 3R), which can be of order (L0 + L1 G) e^{3 L1 R}.
5. **Step growth.** The step rule then gives γ_k ≥ min{S_k/3, 1/(4(A + C/S_k))} with A = L*(1 + 8L1R) and C = 12L1R(1 + L1R);
   the function 8AS + (11C + 4) log S increases by at least one per iteration, which yields the budget.

## Comparison

| result | problem | residual criterion | complexity (F-calls) | constants |
|---|---|---|---|---|
| Choudhury–Loizou, NeurIPS 2025, Thm 3.5 / 3.6 | unconstrained (F(x*) = 0) | min_k ‖F(x_k)‖ | O(L0²R²(1 + L1R e^{L1R})²/ε²); O(L0²R²/ε² + L1²R²) | Thm 3.5 exponential |
| Vankov–Nedić–Sankar, ICML 2024, Thms 5.2–7.1 | constrained, p-quasi-sharp operators only | distance | linear / O(k^{−2/p}) | clipped EG: exp(L1 D̄) |
| repository [`AnchoredGeneralizedMonotone`](AnchoredGeneralizedMonotone.md) | unconstrained | ‖F(x)‖ | O(L0R/ε + (1 + L1R) log) | polynomial |
| anchored EG with projections (Yoon–Ryu ICML 2021; Cai–Oikonomou–Zheng NeurIPS 2022) with L = Lipschitz constant of F on B(x*, 3R) | constrained, Lipschitz | tangent residual | O(L R/ε), L ≤ (L0 + L1G)e^{3L1R} | exponential in L1R |
| penalty: T_λ = F + (I − Π_X)/λ, then an unconstrained method | constrained | tangent residual at Π_X | O(L_loc G R/ε²) via this route when G > 0 (see below) | polynomial |
| **this theorem** | constrained, monotone (L0, L1) | tangent residual | O((L0 + L1G)(1 + L1R)R/ε + (1 + L1R)² log) | polynomial |

*Penalty route.* T_λ is monotone on E and its zeros z satisfy F(z) = −(z − Π_X z)/λ, so dist(z, X) = λ‖F(z)‖ ≈ λG. The tangent
residual of Π_X z is at most ‖F(Π_X z) − F(z)‖ ≈ L_loc λ G, so it is ε-small only for λ ≲ ε/(L_loc G). Even granting that the
unconstrained theorem applies to T_λ (whose (L0, L1) parameters are measured against ‖F‖, not ‖T_λ‖), its leading term
(L0 + 1/λ)R/ε is then of order L_loc G R/ε². The two routes agree only when G = 0.

*Improvement regimes.* For constrained problems with G > 0 the rate improves from ε^{−2} (penalty) to ε^{−1}, and the constants
improve from exponential in L1R (Lipschitz-on-ball) to polynomial. In the unconstrained case G = 0 the bound also improves the
published extragradient rate of Choudhury–Loizou from ε^{−2} to ε^{−1}, but it is worse than the repository's unconstrained theorem
by the factor (1 + L1R) in the leading term.

## Limitations

- **Leading constant.** The leading term carries (L0 + L1G)(1 + L1R) instead of L0 + L1G. The lower bound Ω(LR/ε) for Lipschitz
  monotone problems (Yoon–Ryu) applies with L = L0 + L1G, so the factor (1 + L1R) is an open gap of this analysis, not a proved
  necessity. It comes from points (other solutions or iterates) at distance of order R from x*, where the operator norm can be of
  order G + (L0 + L1G)R, as for rotation-type operators.
- **Unconstrained case.** At X = E and G = 0 the bound does not recover the repository's L0R/ε, because the operator-norm bound of
  step 4 is used instead of the direct residual bound.
- **Domain.** F must be monotone and (L0, L1)-Lipschitz on all of E, and X must admit an exact projection oracle.
- **Parameters.** The method uses L0 and L1; R, G, G0 and ε appear only in the budget. R must be positive.
- **Constants.** The numerical constants (16, 128, 132) are not optimized.
- **Accuracy notion.** The guarantee is a tangent-residual (stationarity) certificate, not a gap-function bound.
