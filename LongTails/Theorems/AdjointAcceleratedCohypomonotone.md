# Cohypomonotone root-finding for every ρ at cost O(LR log(e(1+ρL))/ε): accelerating the adjoint inner solver

This note explains the result formalized in
[AdjointAcceleratedCohypomonotone.lean](AdjointAcceleratedCohypomonotone.lean).

## Summary

**Problem.** Find a point with ‖F(x̂)‖ ≤ ε, where F : ℝ^d → ℝ^d has the following properties:
- ρ-cohypomonotone: ⟨F x − F y, x − y⟩ ≥ −ρ‖F x − F y‖²;
- L-Lipschitz;
- L₂-Lipschitz Jacobian.

The oracle returns F(x) and vector–Jacobian products DF(x)ᵀw. There is **no restriction on ρL**.

**Prior result.** This exact setup is the repository's [CohypomonotoneAdjoint](../Setups/CohypomonotoneAdjoint.lean), from the theorem [AdjointAnchoredCohypomonotone](AdjointAnchoredCohypomonotone.md). That theorem gives the first dimension-free complexity for ρL ≥ 1, with leading term

  128 (1+ρL) log(11+10ρL) · LR/ε.

Its note lists as open "whether a Krylov inner solver can remove this factor".

**This result.** The same outer scheme is used. The inner solver is replaced by Nesterov's accelerated gradient method on the inner merit function, with a computable entry test and a fallback. The bound becomes

  ⌈(4LR/((1+ρL)ε) + 2)(3 + 8(2+2ρL) log(22+20ρL)) + 324 (1+2ρL)² (2+2ρL)³ log(11+10ρL) · L₂R (4 + log(1 + 4LR/ε))² / L⌉

calls to F and DF(·)ᵀ(·). The leading term is

  ≈ 64 log(22+20ρL) · LR/ε.

**Consequences.**
- The factor (1+ρL) is removed from the leading term.
- The ε-dependent cost is within a factor log(e(1+ρL)) of the Ω(LR/ε) lower bound for span methods with F and adjoint queries; see "Lower bound" below.
- The level of nonmonotonicity ρ therefore costs only a logarithm in the leading term, for every ρ ≥ 0.

## Setup (reused, unchanged)

The [setup](../Setups/CohypomonotoneAdjoint.lean) is the one the prior theorem uses; it is not modified.
- **Space.** E is a finite-dimensional real inner-product space.
- **Public data.** L, L₂, ρ, x0. The full parameters add R and ε.
- **`valid`.** L > 0, L₂ ≥ 0, ρ ≥ 0, R ≥ 0, ε > 0.
- **Admissible instances.** There is J with:
  - F differentiable with derivative J(x) at every x;
  - ‖J x − J y‖ ≤ L₂‖x − y‖;
  - F L-Lipschitz;
  - F ρ-cohypomonotone;
  - a zero x* with ‖x0 − x*‖ ≤ R.
- **Oracle.** `inl x` returns F x. `inr (x, w)` returns b with ⟨b, h⟩ = ⟨w, J x h⟩ for all h, that is, b = J(x)ᵀw. Each query of either kind counts as one call.
- **Success.** ‖F(output)‖ ≤ ε for every seed.

Provenance of each condition (from the prior note):
- Lipschitz and cohypomonotone are Assumptions 1–2 of Alacaoglu–Kim–Wright (AKW), ICML 2024 ([arXiv 2402.05071](https://arxiv.org/abs/2402.05071)), with H = 0 and *without* their ρL < 1.
- The Lipschitz Jacobian and vector–Jacobian-product access are standard for Hessian-vector-product methods. For a min–max objective, DF(x)ᵀw is a Hessian-vector product, computable by reverse mode at a constant multiple of the cost of a gradient.

**This result adds no assumption** relative to the prior theorem. Only the algorithm and the analysis change.

## Algorithm ([AdjointAcceleratedProximal.lean](../Algorithms/AdjointAcceleratedProximal.lean), `adjointAccelerated`)

Constants:
- γ = 2ρ + 1/L, μ = ρ + 1/L, Λ = 2 + 2ρL;
- T(v) = v + γF(v);
- for a target t, the inner residual r(v) = T(v) − t and the merit m(v) = ½‖r(v)‖².

The gradient is ∇m(v) = r(v) + γDF(v)ᵀr(v). It costs one F call, which also yields r(v), and one adjoint call.

**Outer loop.** This is unchanged from the prior theorem: the anchored relative-error scheme with step γ.
- *Start.* Solve with t = v0 = x0, giving u₁, and set the anchor a = T(u₁).
- *Step k ≥ 1.* With β = 1/(k+1):
  - target t_k = βa + (1−β)(T(u_k) − μF(u_k));
  - predictor v0 = t_k − γ(1−β)F(u_k);
  - u_{k+1} = inner solve from v0.
- *Output.* The last completed u_k.

**Inner solve (new).** From v0, one F query gives r0 = r(v0). Then:
- **Accelerated branch.** Used if 7γL₂Λ‖r0‖ ≤ 1. Run strongly convex AGD for N_a = ⌈4Λ log(22+20ρL)⌉ steps, with μ_m = ½, L_m = 2Λ², q = 1/(2Λ), and x₀ = z₀ = y₀ = v0:
  - x_{k+1} = y_k − ∇m(y_k)/L_m;
  - z_{k+1} = (1−q)z_k + q y_k − 2q ∇m(y_k);
  - y_{k+1} = (x_{k+1} + q z_{k+1})/(1+q).

  Return x_{N_a}. One extra F query at x_{N_a} provides F(u_{k+1}) for the next outer step.
- **Fallback branch.** Used otherwise: the prior theorem's damped gradient method on m, for ⌈16γL₂Λ²‖r0‖⌉ + ⌈4Λ² log(11+10ρL)⌉ steps.

Call counts:
- an accelerated loop uses 2N_a + 1 calls;
- a fallback loop uses 1 + 2N calls.

The branch and the loop lengths are computed from L, L₂, ρ and the observed ‖r0‖ only. R and ε enter only the budget.

## Guarantee (Lean theorem `OracleTemplate.CohypomonotoneAdjoint.AdjointAcceleratedCohypomonotone.result` in [AdjointAcceleratedCohypomonotone.lean](AdjointAcceleratedCohypomonotone.lean))

`result : Convergence spec budget`, with the one-line public budget above. Execute the algorithm for `budget` calls, counting every F call and every adjoint call. Then it returns x̂ with ‖F(x̂)‖ ≤ ε, for every admissible operator and oracle.

The outer rate is unchanged: ‖F(u_{n+1})‖ ≤ 4L‖x0 − x*‖/((n+1)(1+ρL)). Hence 4LR/((1+ρL)ε) + 2 loops suffice.

**Reading the budget.**
- **First term.** (number of loops) × (calls per accelerated loop ≤ 3 + 8Λ log(22+20ρL)). This is ≈ 64 log(22+20ρL) LR/ε.
- **Second term.** The total cost of the fallback loops. A loop falls back only if its initial residual exceeds 1/(7γL₂Λ). Its cost is charged against that residual: lcost(x) ≤ 3 + 8Λ log(22+20ρL) + 81γL₂Λ³ log(11+10ρL)·x. The sum of loop residuals is O(γLR log²(LR/ε)), from the prior theorem's harmonic iterate bound. The only ε-dependence of this term is log²(LR/ε).

## Mechanism and what is new

**What the prior proof used.**
- For γ ≥ 2ρ the map T is expanding: ‖Tx − Ty‖ ≥ ‖x − y‖.
- Hence ‖∇m(v)‖ ≥ ‖r(v)‖: a PL inequality with modulus 1.
- Gradient steps with step 1/Λ² then contract ‖r‖ by 1 − 1/(4Λ²). This costs Λ² log per inner solve and gives the leading factor (1+ρL)².

The outer scheme needs only O(LR/((1+ρL)ε)) loops, so the per-loop cost Λ² log(Λ) is exactly where the extra (1+ρL) comes from.

**New ingredient 1: local strong convexity and smoothness of the merit, with condition number 4Λ², for every ρ** (`merit_bounds` in [AdjointAcceleratedInner.lean](../Proofs/AdjointAcceleratedInner.lean)). PL with modulus 1 only gives the unaccelerated Λ² rate. We prove a two-sided quadratic bound. Suppose 4γL₂‖r(x)‖ ≤ 1. Then for all y,

  ¼‖y−x‖² ≤ m(y) − m(x) − ⟨∇m(x), y−x⟩ ≤ Λ²‖y−x‖².

Proof. Write Δ = r(y) − r(x) and E₁ = F(y) − F(x) − DF(x)(y−x). Then

  m(y) − m(x) − ⟨∇m(x), y−x⟩ = ½‖Δ‖² + γ⟨r(x), E₁⟩.

- The expansion of T gives ‖Δ‖ ≥ ‖y−x‖. The Lipschitz bound gives ‖Δ‖ ≤ Λ‖y−x‖.
- The Taylor bound ‖E₁‖ ≤ L₂‖y−x‖² gives |γ⟨r(x), E₁⟩| ≤ ¼‖y−x‖².

The lower curvature ½ thus comes from the *expansion* of T, which is where cohypomonotonicity with γ ≥ 2ρ enters, and not from convexity of m. m is not convex globally.

**New ingredient 2: region invariance for a non-monotone method.** AGD iterates are not monotone in m, so the region condition 4γL₂‖r(y_k)‖ ≤ 1 must be maintained differently.
- A root w of r exists in finite dimension: the sublevel set {‖r‖ ≤ ‖r0‖} is compact by expansion, and a minimizer must be a root by the prior damped step. Moreover ‖v0 − w‖ ≤ ‖r0‖ (`exists_root`).
- The Lyapunov function Φ_k = m(x_k) + ¼‖z_k − w‖² contracts by (1−q) whenever the region condition holds at y_k (`agd_step`). It uses the lower bound with comparators w and x_k and the upper bound at x_{k+1}.
- Φ_k ≤ ¾‖r0‖² gives ‖y_k − w‖² ≤ 3‖r0‖², and then ‖r(y_k)‖ ≤ √3 Λ‖r0‖.
- The entry test 7γL₂Λ‖r0‖ ≤ 1 (note 4√3 < 7) closes the induction (`agd_region`).
- After N_a steps, m(x_{N_a}) ≤ (1−q)^{N_a}·¾‖r0‖², so ‖r(x_{N_a})‖ ≤ ‖r0‖/(11+10ρL) (`agd_guarantee`). This is exactly the relative-error accuracy the outer potential needs (`solve_guarantee`).

**New ingredient 3: hybrid accounting.** The entry test may fail in early loops. In that case the prior damped method is used, and its whole cost, including its Λ² log term, is charged against the loop's initial residual, which then exceeds 1/(7γL₂Λ) (`lcost_le`). Because the loop residuals are summable up to log², fallback loops affect only the ε-free burn-in (`cum_le`).

The outer analysis (potential decrease, rate, iterate bound, residual sums) is reused verbatim, generalized to the new inner solver ([AdjointAcceleratedOuter.lean](../Proofs/AdjointAcceleratedOuter.lean)). Every oracle call of the actual state machine is counted in [AdjointAcceleratedExecution.lean](../Proofs/AdjointAcceleratedExecution.lean).

**What is standard.**
- Strongly convex AGD and its estimate-sequence Lyapunov function (Nesterov 2004, §2.2).
- Accelerating an inner solver inside an inexact proximal-point scheme (Catalyst, Lin–Mairal–Harchaoui; Monteiro–Svaiter). Here the outer scheme is the cohypomonotone anchored method, and the inner problem is not convex.

What is new is the observation and proof that the inner merit of the cohypomonotone resolvent is locally well conditioned (κ = 4Λ²) for every ρ, together with a region-invariance argument that makes AGD provably safe there. This is what turns the (1+ρL)² inner cost into (1+ρL)·log.

## Comparison

| Result | Class | Oracle | Leading cost for ‖F‖ ≤ ε |
|---|---|---|---|
| EG+/CEG+/FEG (Diakonikolas–Daskalakis–Jordan AISTATS 2021; Pethick et al. ICLR 2022; Lee–Kim NeurIPS 2021) | ρ < 1/(2L) to 1/(8L) | F | O(LR/ε) |
| AKW ICML 2024, Thm 2.1 ([arXiv 2402.05071](https://arxiv.org/abs/2402.05071)) | ρL < 1 | F (+ resolvent of H) | O(LR (1−ρL)⁻² log(e/(1−ρL))/ε) |
| Prior repo theorem [AdjointAnchoredCohypomonotone](AdjointAnchoredCohypomonotone.md) | any ρ, L₂-Lipschitz Jacobian | F + DF(·)ᵀ(·) | 128(1+ρL) log(11+10ρL) LR/ε + 128(1+2ρL)²(2+2ρL)² (L₂R/L) log² |
| **This theorem** | same | same | **64 log(22+20ρL) LR/ε** + 324(1+2ρL)²(2+2ρL)³ log(11+10ρL) (L₂R/L) log² |

**Regimes and trade-offs.**
- **Leading term.** It improves by a factor of about 2(1+ρL)·log(11+10ρL)/log(22+20ρL), which is at least 1.5 for every ρ and ≈ 2(1+ρL) for large ρL.
- **Burn-in.** It is worse by the factor 324(2+2ρL)log(11+10ρL)/128 = (81/16)(1+ρL)log(11+10ρL): (1+ρL)⁵ log instead of (1+ρL)⁴.
- **When the total bound is smaller.** For ρL ≥ 1 (so that ρL·log(11+10ρL) ≥ log 2), the leading-term saving is at least 64(1+ρL)log(11+10ρL)·LR/ε. The new burn-in is at most 2592(1+ρL)³(1+2ρL)²log(11+10ρL)·L₂R(4+log(1+4LR/ε))²/L. The log(11+10ρL) factors cancel, so for ρL ≥ 1 a sufficient condition for the new total bound to be smaller is

  ε ≤ L² / (41 (1+ρL)² (1+2ρL)² L₂ (4+log(1+4LR/ε))²).

  For larger ε the prior bound can be smaller. We claim no improvement there.
- **ρ = 0 (monotone, Lipschitz Jacobian).** Only the constant changes (64 log 22 vs 128 log 11). This is not a contribution for monotone problems.
- **Literature.** No published method gives a dimension-free complexity for ρL ≥ 1 under any oracle that we are aware of. So relative to the published literature, the result is a complexity of LR log(e(1+ρL))/ε (+ ε-free burn-in) for the whole cohypomonotone class with Lipschitz Jacobian. The direct improvement is over the repository's prior theorem, which is not published.

**Lower bound.** Take the skew linear instances of Yoon–Ryu (ICML 2021, Theorem 3) for deterministic span methods.
- They are monotone, so they lie in the class for every ρ ≥ 0, with L₂ = 0.
- For skew M we have Mᵀ = −M, so adjoint queries keep iterates in the same Krylov space.
- Hence Ω(LR/ε) calls are needed for span methods with F and adjoint queries.

The leading term here is within a factor O(log(e(1+ρL))) of this bound. Whether the log(1+ρL) factor (or the (1+ρL)⁵ burn-in) is necessary is open; we do not claim optimality.

## Examples

**Affine.** Take F(z) = Mz with M invertible. Then ρ = max{0, −λ_min(sym(M⁻¹))} and L = ‖M‖. A real eigenvalue −a < 0 with a < ‖M‖ forces ρL ≥ ‖M‖/a > 1. So ρL ≫ 1 is generic under scale separation.

**Coupled nonlinear family, any dimension.**
- Let M be invertible with σ_min(M) = s, sym(M⁻¹) ⪰ −ρ₀I and ‖M‖ = L₀.
- Let G be smooth with G(0) = 0, ‖DG‖ ≤ ℓ_G, and DG L_G-Lipschitz. For example, G(z) = Bᵀ tanh(Bz) with a dense matrix B, which couples all coordinates.
- For 0 ≤ δ < s/ℓ_G set F(z) = Mz + δG(z).

Then F is (L₀ + δℓ_G)-Lipschitz, its Jacobian is δL_G-Lipschitz, F(0) = 0, and F is ρ-cohypomonotone with

  ρ = ρ₀ + δℓ_G / (s(s − δℓ_G)).

Proof. F(x) − F(y) = A(x−y) with A = M + δĜ and ‖Ĝ‖ ≤ ℓ_G. So ‖A⁻¹ − M⁻¹‖ ≤ δℓ_G/(s(s−δℓ_G)). With w = A(x−y),

  ⟨w, x−y⟩ = ⟨w, A⁻¹w⟩ ≥ −ρ‖w‖².

For M = blockdiag(−a, L₀·Rot(θ)) with a ≪ L₀, take s = a and ρ₀ = 1/a. With δℓ_G = a/2 this gives ρ ≤ 2/a and ρL ≈ 2L₀/a ≫ 1. In this family the nonlinearity couples the repelling direction with all other coordinates. *Caveat:* the nonlinear part has Lipschitz size δℓ_G < a ≪ L₀, so the family is a nonlinear perturbation of an affine operator (its Jacobian varies, and L₂ = δL_G > 0). We do not claim a family whose nonlinearity is of the same order as L with explicitly computed ρ.

## Lean layout

- [Algorithms/AdjointAcceleratedProximal.lean](../Algorithms/AdjointAcceleratedProximal.lean): the state machine `adjointAccelerated` (AGD constants `agdq`, `agdL`, `agdLen`, entry test `useAgd`).
- [Proofs/AdjointAcceleratedInner.lean](../Proofs/AdjointAcceleratedInner.lean):
  - `res_expand`, `res_lip`, `merit_bounds`;
  - `exists_root`;
  - `jensen_sq`, `agd_step`, `agd_region`, `agd_guarantee`, `solve_guarantee`.
- [Proofs/AdjointAcceleratedOuter.lean](../Proofs/AdjointAcceleratedOuter.lean): the prior outer analysis, instantiated with the new inner solver (`Acc.rate`, `Acc.gnorm`, `Acc.loopRes_sum`, …).
- [Proofs/AdjointAcceleratedExecution.lean](../Proofs/AdjointAcceleratedExecution.lean):
  - state-machine traces for both branches (`agd_pairs`, `gd_pairs`, `loop_end`);
  - the output lemma `output_late`;
  - the per-loop cost bound `lcost_le` and the total `cum_le`.
- Reused without change: [AdjointLocal](../Proofs/AdjointLocal.lean), [AdjointInner](../Proofs/AdjointInner.lean), [AdjointOuter](../Proofs/AdjointOuter.lean), [AdjointBudget](../Proofs/AdjointBudget.lean), [AdjointExecution](../Proofs/AdjointExecution.lean).

## Limitations

- **Same added structure as the prior theorem.** A Lipschitz Jacobian, vector–Jacobian products, unconstrained problems, a deterministic oracle, finite dimension, and known L, L₂, ρ.
- **Larger burn-in.** It grows as (1+ρL)⁵ log(e(1+ρL)) · L₂R/L · log²(LR/ε). The improvement holds for small ε, in the regime above.
- **Residual log factor.** The log(e(1+ρL)) factor in the leading term remains. The Ω(LR/ε) lower bound is not matched exactly.
- **Baseline is unpublished.** The direct baseline is the repository's own prior theorem. The relation to published work is as stated in "Literature" above.
