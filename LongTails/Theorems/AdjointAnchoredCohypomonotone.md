# Beyond the 1/L barrier: cohypomonotone root-finding for every ρ with one vector–Jacobian product per step

This note explains the contribution formalized in
[AdjointAnchoredCohypomonotone.lean](AdjointAnchoredCohypomonotone.lean).

**Problem.** Find a zero of a ρ-cohypomonotone, L-Lipschitz operator F on ℝ^d. Cohypomonotonicity means

  ⟨F x − F y, x − y⟩ ≥ −ρ ‖F x − F y‖².

Every first-order method with a complexity guarantee for this class requires ρL < 1. Some require ρ < 1/(2L), others reach ρ < 1/L. Alacaoglu, Kim and Wright write that "it has been conjectured that first-order methods can tolerate a value of ρ no larger than 1/L" ([arXiv 2402.05071](https://arxiv.org/abs/2402.05071), ICML 2024, introduction). The same conjecture appears in [arXiv 2310.02987](https://arxiv.org/abs/2310.02987) and [arXiv 2206.05248](https://arxiv.org/abs/2206.05248).

This note makes two contributions:

1. **Barrier (pen-and-paper proof in this note).** When ρL ≥ 1, no zero-respecting method that queries only F can reduce ‖F‖ at all within k steps, for every k, on suitable linear instances in dimension 2(k+1). To our knowledge this is the first proof of the conjectured 1/L barrier for zero-respecting first-order methods. It is not formalized in Lean.
2. **Algorithm and guarantee (the Lean main theorem).** Suppose the Jacobian is L₂-Lipschitz and the oracle also returns vector–Jacobian products DF(x)ᵀw. For a min–max objective f these are Hessian-vector products, computable by reverse mode at a constant multiple of the cost of a gradient. Then an anchored inexact proximal method finds ‖F(x̂)‖ ≤ ε for **every** ρ ≥ 0 after

   O( LR (1+ρL) log(e(1+ρL)) / ε  +  (1+2ρL)² (1+ρL)² (L₂R/L) log²(e + LR/ε) )

   calls to F and DF(·)ᵀ(·). To our knowledge no dimension-free oracle-complexity bound for ρL ≥ 1 was known before, under any oracle.

Together the two results say:
- Under F-only, zero-respecting access, the threshold ρL = 1 is a hard limit.
- One adjoint product per step removes the limit, at a cost linear in 1 + ρL in the leading term.

## Setup

The [setup](../Setups/CohypomonotoneAdjoint.lean) uses a finite-dimensional real inner-product space E. Its public data are L, L₂, ρ and x0. The full parameters add R and ε.

`valid`: L > 0, L₂ ≥ 0, ρ ≥ 0, R ≥ 0, ε > 0. There is **no** restriction on ρL.

An instance F : E → E and an oracle are admissible when there is a map J : E → (E →L[ℝ] E) with the following properties.

| Condition | Statement | Provenance |
|---|---|---|
| Lipschitz | ‖F x − F y‖ ≤ L‖x − y‖ | AKW Assumption 1 (with H = 0) |
| cohypomonotone | ⟨F x − F y, x − y⟩ ≥ −ρ‖F x − F y‖² for all x, y | AKW Assumption 2 (H = 0), Bauschke–Moursi–Wang 2021; **without** ρL < 1 |
| differentiable | `HasFDerivAt F (J x) x` for all x | added (see below) |
| Lipschitz Jacobian | ‖J x − J y‖_op ≤ L₂‖x − y‖ | added; standard for Hessian-vector-product and second-order methods, e.g. Nesterov–Polyak cubic regularization, Lin–Jordan higher-order VI methods, [arXiv 2405.15990](https://arxiv.org/abs/2405.15990) |
| solution | ∃ x* with F x* = 0 and ‖x0 − x*‖ ≤ R | standard |

- **Oracle.** A query `inl x` returns F x. A query `inr (x, w)` returns some b with ⟨b, h⟩ = ⟨w, J x h⟩ for every h, that is, b = J(x)ᵀw. Every query of either kind is counted as one call.
- **Success.** The output x̂ satisfies ‖F x̂‖ ≤ ε, for every seed.
- **Information.** The [algorithm](../Algorithms/AdjointAnchoredProximal.lean) is built from L, L₂, ρ and x0 only. R and ε enter only the budget.

**Relation to the closest established setup.** This is the unconstrained (H = 0) deterministic setting of AKW, changed in three ways:
- the restriction ρL < 1 is removed;
- a Lipschitz Jacobian is added;
- the oracle is strengthened by vector–Jacobian products.

The repository's existing [CohypomonotoneInclusion](../Setups/CohypomonotoneInclusion.lean) setup cannot be reused, for two reasons. Its `valid` contains ρL < 1, and its oracle has no adjoint queries.

**Why ρL ≥ 1 is the natural regime.** Take an affine operator F(z) = Mz − b with M invertible, for example a linear–quadratic game. Then ρ = max{0, −λ_min(sym(M⁻¹))} and L = ‖M‖.
- If M has a real eigenvalue −a < 0 (a repelling direction) with a < ‖M‖, then ρ ≥ 1/a and therefore ρL ≥ ‖M‖/a > 1.
- So ρL < 1 excludes every repelling mode that is weaker than the dominant scale of the problem. With scale separation, ρL ≥ 1 is the generic case for nonmonotone problems.

**A nonlinear example with explicit constants.** Take z = (x₁, x₂, y₁, y₂) and

  f(x, y) = −(a/2)‖x₁‖² + (a/2)‖y₁‖² + h(x₂, y₂),

with h convex–concave, L_h-smooth, and with an L₂-Lipschitz Hessian, for example h = x₂ᵀBy₂ + Σ log cosh(x₂ᵢ) − Σ log cosh(y₂ᵢ). Then F = (∇ₓf, −∇ᵧf) is (1/a)-cohypomonotone with L = max{a, L_h}, so ρL = L_h/a ≥ 1 whenever L_h ≥ a.

*Caveat:* this example is block-separable, and its ρL ≥ 1 part is a linear repelling block. We do not claim an explicit coupled nonlinear family with computed constants; the affine argument above is the main evidence that the regime is natural.

## Algorithm

Set γ = 2ρ + 1/L, μ = ρ + 1/L, Λ = 1 + γL = 2 + 2ρL, and T(v) = v + γF(v). Note that γ ≥ 2ρ for every ρ.

- **Inner step.** This is a gradient step on ½‖T(v) − t‖². Let r = T(v) − t and b = DF(v)ᵀr (one adjoint query). Then

  v⁺ = v − α (r + γ b),  α = 1/(Λ² · max{1, 4γL₂‖r‖}).

  The next F query, at v⁺, also gives the next residual.
- **Inner length.** Each inner run starts from v0, observes r0 = T(v0) − t from one F query, and then performs

  N(‖r0‖) = ⌈16γL₂Λ²‖r0‖⌉ + ⌈4Λ² log(11 + 10ρL)⌉

  inner steps. N is computed from public constants and the observed residual.
- **Outer loop.** This is the repository's anchored relative-error scheme, run with step γ.
  - *Start.* Run the inner loop on t = v0 = x0. Call the result u₁ and set the anchor a = T(u₁).
  - *Step k = 1, 2, ….* With β = 1/(k+1):
    - target t_k = β a + (1 − β)(T(u_k) − μF(u_k));
    - predictor v0 = t_k − γ(1 − β)F(u_k);
    - u_{k+1} is the result of the inner loop from v0.
  - *Output.* The last completed u_k.

Each loop uses 1 + N F-calls and N adjoint calls.

## Guarantee (Lean theorem `OracleTemplate.CohypomonotoneAdjoint.AdjointAnchoredCohypomonotone.result`)

The completed outer points satisfy, for every n ≥ 0,

  ‖F(u_{n+1})‖ ≤ 4L‖x0 − x*‖ / ((n+1)(1+ρL)).

The public budget is

  ⌈(4LR/((1+ρL)ε) + 2)(5 + 8(2+2ρL)² log(11+10ρL)) + 128(1+2ρL)²(2+2ρL)² L₂ R (4 + log(1 + 4LR/ε))² / L⌉.

The theorem `result : Convergence spec budget` states the following. Execute the algorithm for `budget` calls, counting every F call and every adjoint call. Then it returns a point with ‖F‖ ≤ ε, for every admissible operator and every admissible oracle.

How to read the budget:
- **First term.** About 128(1+ρL) log(11+10ρL) · LR/ε. This is the number of outer steps, 4LR/((1+ρL)ε), times the number of calls per loop once the inner residual is in its linear phase.
- **Second term.** An additive burn-in that covers the damped phase of the inner solver, where α < 1/Λ². Its only dependence on ε is log²(LR/ε). That factor comes from the harmonic growth of the iterate bound ‖T(u_k) − x*‖ ≤ R(6 + 4 log k). There is no L₂R/ε term.
- **Edge cases.** The budget covers the initial loop even when R = 0. The cases r = 0 and L₂ = 0 are handled by the max in α and by the formula for N.

**Lean layout.**
- [AdjointLocal](../Proofs/AdjointLocal.lean): local analysis.
  - ‖J x‖ ≤ L; cohypomonotonicity of the Jacobian.
  - The lower bound ‖(I + γJ)h‖ ≥ ‖h‖, and in finite dimension ‖r + γJᵀr‖ ≥ ‖r‖.
  - The Taylor bound ‖F(v+d) − F v − J v d‖ ≤ L₂‖d‖².
  - One inner step contracts the residual: ‖r⁺‖ ≤ (1 − α/4)‖r‖.
- [AdjointInner](../Proofs/AdjointInner.lean): the run-length lemma (damped phase, then linear phase), the inner guarantee ‖r_N‖ ≤ ‖r0‖/(11+10ρL), and the relative-error conversion.
- [AdjointOuter](../Proofs/AdjointOuter.lean): cocoercivity of realized pairs in y = T(u); the potential decrease through the repository's `potential_identity`; the rate; and ‖T(u₁) − x*‖ ≤ 2‖x0 − x*‖.
- [AdjointBudget](../Proofs/AdjointBudget.lean): the iterate bound, the bound on each loop's initial inner residual, and the harmonic sums.
- [AdjointExecution](../Proofs/AdjointExecution.lean): every oracle call of the actual state machine is counted; the output after any K ≥ (calls of the first n+1 loops) is some u_m with m ≥ n; and the cost bound.

## Mechanism and what is new

**What is known.**
- For γ ≥ 2ρ, the map T = I + γF is expanding: ‖Tx − Ty‖ ≥ ‖x − y‖. Equivalently, the resolvent of γF is nonexpansive (Bauschke–Moursi–Wang, *Math. Program.* 2021, Prop. 3.7 / Thm 2.17; used in the proof of Cor. 4.5 of [arXiv 2310.02987](https://arxiv.org/abs/2310.02987)).
- The exact proximal point method converges for every ρ (Combettes–Pennanen 2004; Gorbunov et al., [arXiv 2210.13831](https://arxiv.org/abs/2210.13831)).
- The anchored relative-error potential is the repository's ([MultiStepAnchoredCohypomonotone](MultiStepAnchoredCohypomonotone.md)).

What blocks first-order methods is that for ρL ≥ 1 the resolvent cannot be computed from F alone. The forward iteration v ↦ t − γF(v) needs γL < 1, while single-valuedness needs γ > ρ.

**New ingredients.**
1. *A ρ-uniform PL modulus from the adjoint.* Differentiating the expansion property gives ‖(I + γDF(v))h‖ ≥ ‖h‖. In finite dimension the operator I + γDF(v) is therefore invertible with inverse of norm ≤ 1, so its adjoint satisfies ‖r + γDF(v)ᵀr‖ ≥ ‖r‖. Consequently the merit ½‖T(v) − t‖² satisfies a PL inequality with modulus 1 that does not depend on ρ, and a single adjoint product supplies its gradient. Gradient steps with step 1/Λ² then contract the residual at rate 1 − 1/(4Λ²) once ‖r‖ ≤ 1/(4γL₂). An adaptive damped step covers the region before that.
2. *Computable inner stopping with relative error.* The inner guarantee ‖r_N‖ ≤ ‖r0‖/(1 + 5Λ) and the predictor identity v − v0 = r(v) − γ(F(v) − (1−β)F(u_k)) together give the relative-error condition ‖e‖ ≤ (μ/2)‖w‖ required by the anchored potential. The inner loop length is a deterministic function of the observed ‖r0‖.
3. *Burn-in accounting without an L₂/ε term.* Each loop's initial residual is O(γLR(1 + log k)/k). So the damped phases add up to O(γ²L₂LΛ²R log²k), which is independent of 1/ε except for logarithms.

**Barrier (contribution 1; full proof here, not verified in Lean).** A *zero-respecting F-only method* produces iterates with x_{i+1} ∈ x0 + span{F(x0), …, F(x_i)}.

*Claim.* Let ρL ≥ 1, k ≥ 0, d = 2(k+1). For j = 0, …, k set θ_j = (2j+1)π/(k+1) and let M = L · blockdiag(R(θ_0), …, R(θ_k)), where R(θ) is the 2×2 rotation. Choose x0 with ‖(x0)_j‖ = R/√(k+1) on each block. Then F(x) = Mx belongs to the class with L₂ = 0 and x* = 0, and every zero-respecting F-only method satisfies ‖F(x_i)‖ ≥ LR = ‖F(x0)‖ for all i ≤ k.

*Proof.*
- (a) **F is in the class.** M is normal with ‖M‖ = L. For u = M(x − y), cohypomonotonicity reads ⟨u, M⁻¹u⟩ ≥ −ρ‖u‖². Here sym(M⁻¹) = L⁻¹ blockdiag(cos θ_j I₂) ⪰ −L⁻¹I ⪰ −ρI because ρL ≥ 1. The case ρL = 1 is included.
- (b) **Krylov form of the iterates.** By induction x_i − x0 ∈ span{Mx0, …, M^i x0}. Hence F(x_i) = M p_i(M) x0 for a real polynomial p_i with deg p_i ≤ i ≤ k and p_i(0) = 1.
- (c) **Norm on each block.** Identify each block with ℂ. Then M acts on block j as multiplication by λ_j = L e^{iθ_j}, so

  ‖F(x_i)‖² = (L²R²/(k+1)) Σ_j |p_i(λ_j)|².
- (d) **Mean-value bound.** The λ_j/L are the (k+1)-th roots of −1. For 1 ≤ m ≤ k,

  Σ_j e^{imθ_j} = e^{imπ/(k+1)} Σ_j e^{2πijm/(k+1)} = 0.

  Hence (1/(k+1)) Σ_j p_i(λ_j) = p_i(0) = 1. By Cauchy–Schwarz, Σ_j |p_i(λ_j)|² ≥ k+1, so ‖F(x_i)‖ ≥ LR. □

On these instances one adjoint product solves the problem, because MᵀM = L²I gives x1 = x0 − MᵀF(x0)/L² = 0.

*Scope.* The barrier covers zero-respecting (Krylov-span) F-only methods. Randomized methods and non-zero-respecting methods are not covered.

Numerically, on a nonlinear coupled instance with ρL ≈ 1.22, extragradient diverges for every step size we tried, while this method shows k‖F(u_k)‖ → 1.7. This is only a sanity check.

## Comparison with the closest results

| Result | Class | Oracle | Rate for ‖F‖ ≤ ε |
|---|---|---|---|
| EG+/CEG+/FEG (Diakonikolas–Daskalakis–Jordan 2021; Pethick et al. ICLR 2022; Lee–Kim NeurIPS 2021) | ρ < 1/(2L) or ρ < 1/(8L) | F | O(LR/ε) |
| AKW ICML 2024, Thm 2.1 ([arXiv 2402.05071](https://arxiv.org/abs/2402.05071)); repo `MultiStepAnchoredCohypomonotone` | ρL < 1, constrained | F + resolvent of H | O(LR(1−ρL)⁻² log(e/(1−ρL))/ε) |
| Exact PPM (Combettes–Pennanen 2004; Gorbunov et al. 2022) | any ρ | exact resolvent of F | no oracle complexity in F |
| Second-order / higher-order VI methods (Lin–Jordan; [arXiv 2405.15990](https://arxiv.org/abs/2405.15990)) | monotone or Minty (ρ = 0) | F, DF | — |
| **This note** | **any ρ ≥ 0**, unconstrained, L₂-Lipschitz Jacobian | F + DF(·)ᵀ(·) | O(LR(1+ρL) log(e(1+ρL))/ε + (1+2ρL)²(1+ρL)²(L₂R/L) log²(e+LR/ε)) |

**Regimes.**
- *ρL ≥ 1.* This is the first dimension-free complexity under any oracle we are aware of. The barrier above shows that F-only zero-respecting methods cannot achieve it.
- *ρL ≤ 1.* The bound is O(LR/ε + (L₂R/L) log²(LR/ε)), with no (1−ρL)⁻² blow-up near ρL = 1. This uses a **stronger oracle** (adjoint queries) and an **added assumption** (Lipschitz Jacobian), so the comparison with F-only baselines is context, not a like-for-like improvement.
- *Lower bound.* Ω(LR/ε) holds for span methods using F and adjoint queries. On skew linear instances (Yoon–Ryu, ICML 2021) the adjoint of a skew M is −M, so the span stays a Krylov space. The leading term is therefore optimal for ρL = O(1), up to constants. For ρL ≫ 1 there is a gap of a factor (1+ρL)log(e(1+ρL)).

**Strongest rejection argument and answer.** "Proximal point plus a Gauss–Newton inner solver is a textbook composition."
- The individual components are classical, and we say so.
- What was missing is an oracle-complexity guarantee for ρL ≥ 1 together with an explanation of why first-order methods stop at 1/L. The barrier supplies the second part, as a proof for zero-respecting methods, which until now was only a conjecture in AKW and earlier work.
- The upper bound shows that the obstruction is exactly the missing adjoint. One VJP per step, with an inner merit whose PL modulus is 1 for every ρ, yields a complexity linear in 1+ρL. It also comes with a computable stopping rule and a burn-in that is free of 1/ε.

## Limitations

- **Unconstrained only.** H = 0; constrained games are not covered.
- **Constants must be known.** ρ, L and L₂ are inputs to the algorithm.
- **Stronger oracle, added assumption.** The oracle includes vector–Jacobian products, and the Lipschitz-Jacobian assumption is added relative to AKW.
- **Barrier scope.** The barrier covers zero-respecting F-only methods only and is not formalized in Lean.
- **Gap for large ρL.** For ρL ≫ 1 the leading term exceeds the Ω(LR/ε) lower bound by a factor (1+ρL) log(e(1+ρL)). Whether a Krylov inner solver can remove this factor is open.
- **Finite dimension.** E must be finite-dimensional, because the proof uses that an injective operator on E is surjective. Infinite-dimensional Hilbert spaces are not covered.
- **Deterministic oracle only.**
