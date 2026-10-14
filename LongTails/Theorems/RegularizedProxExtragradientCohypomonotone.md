# Stochastic composite cohypomonotone inclusions: Õ(LR/ε + σ²/ε²) with a deterministic budget

**Lean files.**
- Main theorem: [`RegularizedProxExtragradientCohypomonotone.lean`](RegularizedProxExtragradientCohypomonotone.lean). It contains `OracleTemplate.StochasticCohypomonotone.result` and the budget `OracleTemplate.StochasticCohypomonotone.budget`.
- Setup: [`../Setups/StochasticCohypomonotoneInclusion.lean`](../Setups/StochasticCohypomonotoneInclusion.lean).
- Algorithm: [`../Algorithms/RegularizedProxExtragradient.lean`](../Algorithms/RegularizedProxExtragradient.lean), which defines `regularizedProxExtragradient` and `RegCfg`.
- Parameters: [`../Proofs/RegularizedProxEgTuning.lean`](../Proofs/RegularizedProxEgTuning.lean), which defines `tunedCfg`.
- Main proof chain:
  - `CohypoRegularizedOperator`: resolvents, the regularized pairwise inequality, and regularized zeros.
  - `CohypoEgStep`: the one-step inequality for the extragradient step.
  - `CohypoStageGeometry`: the stage geometry and the final certificate.
  - `RegularizedProxEgStage` and `RegularizedProxEgRepeat`: per-step and per-stage expectations.
  - `RegularizedProxEgAssembly` and `RegularizedProxEgMain`: the recursion and the final bound.

## Problem and assumptions

The space E is an arbitrary finite-dimensional real inner-product space. We seek a point x with 0 ∈ F(x) + G(x), where:

- **(A1)** F : E → E is L-Lipschitz. It is **not** assumed monotone.
- **(A2)** G : E ⇉ E is monotone. It is accessed only through an exact resolvent oracle J(γ, z), which satisfies γ⁻¹(z − J(γ,z)) ∈ G(J(γ,z)) for every γ > 0. Examples are a projection onto a closed convex set, or the prox map of a convex regularizer.
- **(A3)** The sum F + G is **ρ-cohypomonotone**: for all u ∈ (F+G)(x) and v ∈ (F+G)(y),

  ⟨u − v, x − y⟩ ≥ −ρ‖u − v‖².

  We require 0 ≤ ρ < 1/(2L), and write τ := 1 − 2ρL ∈ (0, 1].
- **(A4)** A solution x* exists with ‖x₀ − x*‖ ≤ R.
- **(A5)** Each oracle call at a point x returns g(x, ξ). The samples ξ form an IID stream under an abstract probability measure P. The oracle g is jointly measurable, unbiased (E g(x, ξ) = F(x)), and has variance E‖g(x, ξ) − F(x)‖² ≤ σ².

(A1)–(A5) are the stochastic cohypomonotone setting of Alacaoglu–Kim–Wright ([ICML 2024, arXiv 2402.05071](https://arxiv.org/abs/2402.05071), Assumptions 1, 2 and 4). The deterministic version of this class is already in the repository ([`CohypomonotoneInclusion`](../Setups/CohypomonotoneInclusion.lean)); our setup keeps the same formulation and adds the stochastic oracle. The step-size range ρ < 1/(2L) is the range of Chen–Luo ([JMLR 2024, arXiv 2208.05925](https://arxiv.org/abs/2208.05925), Thm 5.4) and of fixed-step EG+ (Pethick et al., ICLR 2022). It is narrower than the range ρ < 1/L of Alacaoglu–Kim–Wright.

**Oracle and cost model.** The Lean query type is E ⊕ (ℝ × E): either a stochastic F-sample at a point, or a resolvent evaluation J(γ, z). **Every call is counted,** including resolvent calls. The algorithm uses L, ρ, R, σ and ε; the instance's F, G and J are available only through the oracle.

**Accuracy criterion (strong residual).** The algorithm outputs a pair (x̄, u). For every sample path, u ∈ G(x̄); the certificate is exact, because it comes from a resolvent step. The guarantee is

E ‖F(x̄) + u‖ ≤ ε,

so E dist(0, (F+G)(x̄)) ≤ ε. This criterion controls the forward–backward residual (gradient mapping) used by Alacaoglu (arXiv 2609.08380) and the resolvent residual used by Alacaoglu–Kim–Wright, up to constants.

## Algorithm (`regularizedProxExtragradient`)

The algorithm is a two-loop recursive regularization. The outer recursion follows Allen-Zhu (NeurIPS 2018, SGD3) and Chen–Luo (RAIN). The inner solver is a **mini-batched stochastic proximal EG+**. No multilevel Monte Carlo (MLMC) is used.

**Stages.** For stages s = 0, …, S:
- Set λ_s = 2^s λ₀ and Λ_s = Σ_{t≤s} λ_t.
- The anchors are a₀ = x₀ and a_s = the output of stage s − 1.
- Stage s works on the regularized operator H_s = F + G + Σ_{t≤s} λ_t(· − a_t), whose forward part is F + Λ_s(· − c_s) with center c_s = Λ_s⁻¹ Σ_{t≤s} λ_t a_t.

**Inner step.** Each stage runs T_s steps. One step at the point x uses two independent mini-batches of size b_s, giving the averages v₁ (at x) and v₂ (at x̄):
- x̄ = J(γ, x − γ(v₁ + Λ_s(x − c_s))) (resolvent call);
- x⁺ = x − αγ[γ⁻¹(x − x̄) − (v₁ + Λ_s(x − c_s)) + (v₂ + Λ_s(x̄ − c_s))].

A step therefore costs 2b_s + 1 oracle calls.

**Output.** After stage S, the algorithm computes one forward–backward step with a batch of size b_f:
- y = x − γ(v + Λ_S(x − c_S));
- x̄ = J(γ, y);
- output (x̄, u), with u = γ⁻¹(y − x̄) ∈ G(x̄).

**Parameters (`tunedCfg`).** All parameters are explicit:

| Quantity | Formula |
|---|---|
| γ | (1 + 2ρL)/(2L) |
| α | τ/16 |
| Λ_max | τ³L/256 |
| λ₀ | εΛ_max/(2ε + 24RΛ_max) |
| S | ⌊log₂⌊Λ_max/λ₀⌋⌋ − 1 |
| K₀ | 2¹⁵/τ³ |
| δ_s | ε/(K₀(S+1)λ_{s+1}) |
| T_s | ⌈log(16K₀²(S+1)²)/(αγΛ_s)⌉ |
| b_s | ⌈44γσ²/(τΛ_sδ_s²)⌉ + 1 |
| b_f | ⌈256σ²/ε²⌉ + 1 |

## Theorem

`result : Convergence spec budget`. For every valid parameter tuple and every admissible instance and oracle:
- the algorithm makes `budget` oracle calls;
- the output is measurable;
- the certificate lies in G(x̄) on every sample path;
- E‖F(x̄) + u‖ ≤ ε.

The budget is

budget = ⌈ 2⁵³ τ⁻⁸ (1 + LR/ε + σ²/ε²) (1 + log(2 + LR/ε) + log(2/τ))⁴ ⌉, where τ = 1 − 2ρL.

**Finer bound actually proved.** The proof bounds the true number of calls by

Õ( τ⁻⁴(1 + LR/ε)·ℓ + τ⁻⁸ (σ²/ε²) (S+1)³ ℓ ),

where S + 1 ≤ 2 log(2 + LR/ε) and ℓ = log(16K₀²(S+1)²) = O(log(2/τ) + log log(2 + LR/ε)). In particular:
- the deterministic term is (LR/ε) up to a log factor;
- the stochastic term is σ²/ε² up to log⁴ factors.

The one-line budget multiplies every term by the same log⁴ factor for readability. The constants 2⁵³ and the powers of τ are explicit but far from optimized. On a numerical parameter sweep, the stated budget exceeded the actual plan length by more than three orders of magnitude.

## What is new, and what is already known

**Closest prior work.**

1. **Alacaoglu–Kim–Wright, ICML 2024** ([arXiv 2402.05071v3](https://arxiv.org/abs/2402.05071)).
   - Corollary 4.1 covers the same constrained, stochastic, cohypomonotone class with ρ < 1/L. It gives Õ(ε⁻⁴) stochastic first-order complexity for the resolvent residual. The method is an inexact Halpern iteration with stochastic forward–backward–forward inner solves.
   - Remark 4.2 states as an open question (the Conclusions section mentions a related direction but not this sentence): "to get a similar complexity improvement [Õ(ε⁻²), as Chen–Luo obtained for unconstrained problems] in our constrained setup with a wider range for ρ".
   - **Our result gives Õ(ε⁻²) on the overlap ρ < 1/(2L) of their class.** That is a polynomial improvement, from ε⁻⁴ to ε⁻² up to logarithms. It answers the *constrained/composite half* of their question only. The *wider range* ρ ∈ [1/(2L), 1/L) remains open.
2. **Chen–Luo, JMLR 2024** ([arXiv 2208.05925](https://arxiv.org/abs/2208.05925)), Theorem 5.4 (RAIN++).
   - This gives Õ(σ²ε⁻² + LDε⁻¹) *expected* SFO calls for **unconstrained** negatively comonotone problems with ρ ≤ 1/(2L).
   - The mechanism runs RAIN on the saddle envelope f_{2L}. Gradients of f_{2L} need inner resolvent solves, which are debiased by MLMC (their Thms 5.1–5.2). The result is a multi-loop method with random cost.
   - Alacaoglu–Kim–Wright (App. D) note that "it is not clear … if their arguments generalize to constraints".
   - In the unconstrained case our rate matches theirs. Our method avoids MLMC and has a deterministic budget. **We do not claim this as an improvement.**
3. **Alacaoglu, arXiv 2609.08380 (Sep 2026)** and **Ji–Lan–Zhu, arXiv 2609.04188.**
   - Both give Õ(ε⁻²) for constrained **monotone** stochastic VIs.
   - Alacaoglu's conclusion suspects that ideas from Chen–Luo could handle cohypomonotone constrained problems. His inner solver needs the perturbed operator F + μI + ∂r to be strongly monotone, and that fails when F + G is only cohypomonotone.
4. **Lee–Kim, arXiv 2609.35631 (Sep 2026).**
   - RRSEG obtains near-optimal complexity with fixed queries for **monotone** composite inclusions.
   - Their Section 8 states that under negative comonotonicity "corresponding stochastic guarantees are unknown".
   - We therefore do **not** claim the first deterministic-budget or first two-loop method in the monotone case.
5. **Tran-Dinh–Nguyen-Trung, arXiv 2603.15576.** This work treats nonmonotone composite inclusions at Õ(ε^{−10/3}) with variance reduction, under a stronger oracle. **Pethick et al., ICLR 2023**, treat stochastic weak MVI at Õ(ε⁻⁴) under mean-square Lipschitz same-sample access.
6. **Other related work found in a targeted search.** Constrained nonconvex–nonconcave minimax under KL conditions (Lu–Wang, [arXiv 2510.01168](https://arxiv.org/abs/2510.01168)) is deterministic. Game-stationarity reformulations ([arXiv 2609.32970](https://arxiv.org/abs/2609.32970)) appear, from the abstract, to be deterministic; we did not verify the full text. We found no stochastic Õ(ε⁻²) result for constrained cohypomonotone inclusions.

**Technical mechanism.** We avoid Chen–Luo's envelope + MLMC detour, because the regularized cohypomonotone operator is itself well behaved:
- **Regularized pairwise inequality** (`OpHyp.reg_pair`). For H = F + G that is ρ-cohypomonotone, and H_Λ = H + Λ(· − c), every pair satisfies

  (1 − 2ρΛ)⟨Δw, Δx⟩ ≥ −ρ‖Δw‖² + Λ(1 − ρΛ)‖Δx‖².

  So H_Λ is simultaneously ρ/(1−2ρΛ)-cohypomonotone and Λ-strongly monotone in the Minty sense.
- **EG+ step** (`OpHyp.eg_step`, `OpHyp.eg_expect`). A fixed-step prox-EG+ step contracts toward the zero of H_Λ for all ρ < 1/(2L). Its contraction factor is (1 − αγΛ), and its noise term is O(αγ²σ²/(τb)).
  - The first-step noise passes through the resolvent. It is absorbed by Young's inequality into the (γ/2 − ρ′) margin.
  - Single-sample steps would leave a floor of order γσ²/Λ, because γ > 2ρ cannot shrink. **Mini-batching is therefore necessary,** with b_s ∝ λ_s.
- **Geometry without monotonicity** (`OpHyp.stage_dist`, `path_succ`). The successive regularized zeros satisfy ‖z_s − a_s‖² ≤ 2‖z_{s−1} − a_s‖² and ‖z_s − z_{s−1}‖ ≤ ‖z_{s−1} − a_s‖. These replace the strong-monotonicity arguments of Allen-Zhu and Chen–Luo. The anchored quantity Q_s = ‖Λ_s(z_s − c_s)‖ then obeys Q_{s+1} ≤ Q_s + 3λ_{s+1}‖z_s − a_{s+1}‖.
- **Existence of regularized zeros** (`regZero`). Each zero is the fixed point of two nested contractions. The resolvent of γH is single-valued and nonexpansive because 2ρ ≤ γ < 1/L.

## Instances and the scope of "constrained"

Five facts describe which problems the theorem covers:

- **(a) Unconstrained interaction-dominant games (G = 0).** Take f(x,y) = φ(x) + ⟨x, By⟩ − ψ(y), with B square and singular values in [s, b], and φ, ψ with ℓ-Lipschitz gradients (possibly nonconvex). Then F is ℓ/(s−ℓ)²-cohypomonotone with L ≤ b + ℓ.
- **(b) Constrained, nonmonotone, interacting example.** Consider convex–nonconcave bilinearly coupled games

  min_{x∈ℝⁿ} max_{y∈Y} φ(x) + ⟨x, By⟩ − ψ(y),

  where:
  - Y is any closed convex set (box, simplex, ball);
  - φ is convex and β-smooth;
  - ψ is ℓ-weakly convex, so the game is **nonconcave** in y;
  - B has full column rank with σ_min(B) ≥ s > √(βℓ).

  Then F + ({0} × N_Y) is ℓ/(s − √(βℓ))²-cohypomonotone. **This was proved during the review,** by splitting on whether ‖Δ∇φ‖ ≥ √(βℓ)‖Δy‖. It is not formalized in Lean, and it was checked numerically on simplex and box instances.
- **(c) Hidden structure of (b).** In class (b) the dual function −D(y) = φ*(−By) + ψ(y) is (s²/β − ℓ)-strongly convex on Y. The game is a strongly convex constrained problem in disguise.
  - If φ is μ-strongly convex, a standard reduction applies: inexact projected gradient on −D, with SGD inner solves of the strongly convex x-problem. It reaches a similar Õ(σ²/ε²) cost with only a log(1/ε) deterministic term. **For such instances our result is no improvement.**
  - When φ is convex but not strongly convex (μ = 0, e.g. unregularized logistic or Huber loss), we know of no reduction achieving ε⁻².
- **(d) Inequality constraints can break the class.** For F = bJ − ℓ′I (J skew, F alone ℓ′/b²-cohypomonotone) and a halfspace constraint, F + N_C is only (1/ℓ′)-cohypomonotone. So the assumption that "F + G is cohypomonotone" must be checked per instance. It holds in (b), and for affine equality constraints when the restricted operator is cohypomonotone.
- **(e) The motivating examples of Alacaoglu–Kim–Wright are unconstrained.** Their interaction-dominant examples (their Ex. 1.1, Grimmer et al.; Hajizadeh et al.) are unconstrained. For those, Chen–Luo already gives the rate in expectation.

## Limitations

- **Range of ρ.** The range is ρ < 1/(2L), and the constants degrade polynomially in 1/τ (τ⁻⁸ in the simplified budget). The range ρ ∈ [1/(2L), 1/L) treated deterministically by Alacaoglu–Kim–Wright is not covered.
- **Required inputs.** The algorithm needs L, ρ, R and σ. This is the same drawback that Alacaoglu–Kim–Wright point out for Chen–Luo.
- **Logarithmic factors.** The stochastic term carries a log⁴ factor in the stated budget (log³ times ℓ in the finer bound). We do not claim optimality of the logarithms or of the τ-dependence.
- **Not optimal for strongly convex instances.** For structured instances whose hidden dual is strongly convex with strongly convex φ, the standard reduction in (c) is better in the deterministic term.
- **No pointwise convergence.** The guarantee is in expectation, for one output, and says nothing about pointwise convergence.
