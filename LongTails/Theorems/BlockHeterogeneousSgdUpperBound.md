# Block-heterogeneous stochastic nonconvex optimization: optimal upper bound

Lean: [theorem](BlockHeterogeneousSgdUpperBound.lean), [setup](../Setups/BlockHeterogeneousNonconvex.lean), [algorithm](../Algorithms/BlockSgd.lean), proofs [BlockSgdRate](../Proofs/BlockSgdRate.lean) and [BlockSgdConvergence](../Proofs/BlockSgdConvergence.lean). Companion lower bound: [BlockHeterogeneousLowerBound](BlockHeterogeneousLowerBound.md).

## Setup

The variable is split into `B` blocks (layers): `x = (x_1, …, x_B)`, given by an arbitrary block map `blk : Fin d → Fin B` on `ℝ^d`, with orthogonal block projections `P_j`. The objective `f` is differentiable, bounded below, and `f(x_0) − inf f ≤ Δ`. There are four assumptions.

- **Two-sided block smoothness.** For all `x, y`, `|f(y) − f(x) − ⟨∇f(x), y − x⟩| ≤ ½ Σ_j L_j ‖P_j(y − x)‖²`. For C² functions this is `−diag(L_j I) ⪯ ∇²f ⪯ diag(L_j I)`. It is the block version of the anisotropic smoothness of [Jiang–Maladkar–Mokhtari (COLT 2025), Assumption 4b](https://arxiv.org/abs/2406.04592) and [Liu–Pan–Zhang (ICLR 2025)](https://arxiv.org/abs/2406.15244). It is also the block (ESO-type) smoothness of block-coordinate methods. Off-diagonal blocks may interact arbitrarily within the bound.
- **Stochastic oracle.** Each query returns `g(x, ξ)` with IID samples `ξ`. It is unbiased, `∫ g(x, ξ) dp = ∇f(x)`, and has per-block variance `E‖P_j(g(x, ξ) − ∇f(x))‖² ≤ σ_j²` for every `j`. Joint measurability and the integrability conditions are part of the setup. This is the per-layer variance of [You et al. (LARS/LAMB, ICLR 2020), §3](https://arxiv.org/abs/1904.00962), without their bounded-gradient assumption. Noise may be correlated across blocks.
- **Accuracy criterion.** `E Σ_j ‖P_j ∇f(x̂)‖ ≤ ε`, the sum of layer-gradient norms. This is the dual of the max-over-layers product norm used in layer-wise and LMO-based optimizer analyses. It is exactly LARS/LAMB's criterion up to the factor `1/√h`. With `B = 1` it is the standard `E‖∇f(x̂)‖ ≤ ε`.
- **Cost.** One stochastic-gradient call per oracle query.

The parameters `L_j > 0`, `σ_j ≥ 0`, `Δ` and `ε` are known to the algorithm. This is a known-parameter oracle-complexity result.

## Algorithm and guarantee

The method is block-wise SGD, `x_{k+1} = x_k − D g(x_k, ξ_k)`, where `D = Σ_j η_j P_j` and

`η_j = 1/(L_j + β w_j)`, with `w_j = (L_j σ_j²)^{1/3}`, `S = Σ_j w_j`, and `β = max(4S²/ε², 2√(S Σ_j L_j)/ε)`.

The output is a uniformly random iterate among `x_0, …, x_K`, chosen from the algorithm's own seed. The oracle-call budget is

`⌈8 (Σ_j L_j) Δ/ε² + 20 (Σ_j (L_j σ_j²)^{1/3})³ Δ/ε⁴⌉ + 1`,

that is, `O(‖L‖₁Δ/ε² + S³Δ/ε⁴)` with `S = Σ_j L_j^{1/3} σ_j^{2/3}`. The bound holds for every valid parameter vector, with any number of blocks of any sizes. It also applies verbatim on the high-dimensional setup used by the lower bound. That setup's `valid` implies the general `valid` (its regime forces `Δ > 0`), and its `admissible` and `successful` are, by definition, those of the general setup at `toGeneral q`.

Proof mechanism, all formalized:
1. The block descent inequality gives `E f(x_{k+1}) ≤ E f(x_k) − ½ Σ_j η_j E‖P_j∇f(x_k)‖² + ½ Σ_j L_j η_j² σ_j²`.
2. Cauchy–Schwarz gives `(Σ_j ‖a_j‖)² ≤ (Σ_j 1/η_j)(Σ_j η_j‖a_j‖²)`, which converts this into the ℓ_{2,1} criterion.
3. Jensen's inequality finishes the bound.

The choice `η_j ∝ (L_j σ_j²)^{−1/3}` balances the two terms by Hölder's inequality. The descent inequality itself is standard. The contribution is the step-size law and its matching lower bound.

## Comparison with prior guarantees (same criterion, known parameters)

Hölder's inequality gives `S³ = (Σ_j L_j^{1/3} σ_j^{2/3})³ ≤ (Σ_j L_j)(Σ_j σ_j)² = ‖L‖₁‖σ‖₁²`, with equality iff `L_j ∝ σ_j`. The ratio `‖L‖₁‖σ‖₁²/S³` can be large. For example, with B/2 blocks of `(L, s)` and B/2 blocks of `(L/B³, Bs)` it is ≍ B².

| Method | Calls for `E Σ_j‖∇_j f‖ ≤ ε` | Notes |
|---|---|---|
| SGD with one step size (Ghadimi–Lan, in our criterion) | `O(B·max_j L_j Δ/ε² + B²max_j L_j ‖σ‖₂² Δ/ε⁴)` via `Σ_j‖a_j‖ ≤ √B‖a‖` | no block adaptation |
| LARS ([You et al. 2020, Thm 2](https://arxiv.org/abs/1904.00962)) and LAMB (Thm 3) | `≈ (‖L‖₁Δ + ‖σ‖₁²)²/ε⁴` (batch `b = T`) | also assumes bounded gradients |
| AdaGrad, coordinate blocks ([Jiang et al. 2025, Thm 3.1](https://arxiv.org/abs/2406.04592)) | `Õ(‖L‖₁Δ/ε² + ‖σ‖₁²‖L‖₁Δ/ε⁴ + ‖σ‖₁⁴/ε⁴)` | **adaptive** (no parameter knowledge) |
| Layer-wise LMO/normalized methods ([Gluon 2505.13416](https://arxiv.org/abs/2505.13416), [Hao et al. 2510.14009](https://arxiv.org/abs/2510.14009)) | `‖L‖₁‖σ‖₁²`-type noise terms, or a single shared σ | tuned |
| **This theorem** | `O(‖L‖₁Δ/ε² + S³Δ/ε⁴)` | tuned (known `L_j, σ_j`) |

The comparison with AdaGrad is between a tuned method and an adaptive one. AdaGrad's own lower bound ([Jiang et al., Thm 3.2](https://arxiv.org/abs/2406.04592)) is already of order `S³`, so this theorem does **not** show that AdaGrad is worse than `S³`. It shows only that the known AdaGrad/LAMB/SignSGD-type upper bounds, which carry the factor `‖L‖₁‖σ‖₁²`, are not the class complexity.

**Not a reweighting corollary.** One could run SGD in the weighted norm `‖x‖_a² = Σ_j a_j‖x_j‖²` and apply Cauchy–Schwarz, using the general-norm analyses of [Kovalev 2025](https://arxiv.org/abs/2503.12645) and [Pethick et al. (Scion)](https://arxiv.org/abs/2502.07529). That gives `(max_j L_j/a_j)(Σ_j σ_j²/a_j)(Σ_j a_j)²Δ/ε⁴`. Take two blocks with `L = (1, ℓ)`, `σ = (s, 0)` and `ℓ ≥ 1`. The best weights give order `ℓs²Δ/ε⁴`, because the noiseless high-curvature block still forces `Σ_j a_j ≥ ℓ`. By contrast `S³ = s²`. Reaching `S³` needs the block-diagonal curvature–noise coupling `Σ_j L_j η_j² σ_j²`, not just a reweighted geometry.

## Examples

The class covers interacting nonlinear models. One family is `f(x) = Σ_j φ_j(x_j) + ψ(Σ_j A_j x_j)`, where `φ_j` are nonconvex regularizers with the two-sided bound `‖∇²φ_j‖ ≤ c_j`, for example `λ Σ log(1 + t²)`, and `ψ` is a loss whose Hessian is bounded in operator norm, `−M I ⪯ ∇²ψ ⪯ M I`, such as softplus or logistic loss of a linear model. Since `|(Σ_j A_j h_j)ᵀ∇²ψ(Σ_j A_j h_j)| ≤ M B Σ_j ‖A_j‖²‖h_j‖²`, we can take `L_j = c_j + M B ‖A_j‖²`. Minibatch noise with per-block variances `σ_j²`, such as different feature scales per block, fits the oracle model. More generally, any C² loss whose Hessian is bounded by `diag(L_j I)` in Loewner order qualifies. Deep-network losses satisfy this on bounded regions, with layer-dependent `L_j`.

## Scope and what is new

- **New:** an `O(‖L‖₁Δ/ε² + S³Δ/ε⁴)` upper bound in the block model, attained by simple block-wise step sizes `η_j ∝ (L_jσ_j²)^{−1/3}`. Combined with the [companion lower bound](BlockHeterogeneousLowerBound.md), this is the minimax oracle complexity for known parameters, tight up to a universal constant (≈ 20·2^57), in the stated regime. We found no published `S³` upper bound for any method. The search covered Jiang et al., Liu–Pan–Zhang, You et al., Gluon, Hao et al., Scion/Kovalev, and the SignSGD ℓ1 lower-bound paper [2605.06615](https://arxiv.org/abs/2605.06615).
- **Known:** the block descent lemma, and the idea of allocating `Δ` and `ε` across coordinates in proportion to `σ_i^{2/3} L_i^{1/3}`. The latter appears in the AdaGrad-specific lower bound of Jiang et al., Thm 3.2.
- **Limitations:**
  - Tightness is claimed only in the companion regime, where every block satisfies `2^57 ε² ≤ L_j Δ` and every block is high-dimensional. Outside that regime this upper bound is not tight. A block with `L_jΔ ≪ ε²` is essentially free, since `‖∇_j f(x)‖² ≤ 2L_j(f(x) − inf f)`. Freezing such blocks (`η_j = 0`) would remove their `w_j` from `S`. The mixed trivial/nontrivial case is left open.
  - The per-coordinate ℓ1 model of Jiang et al. (blocks of size 1) is **not** closed by this pair. The upper bound applies there, but the lower bound needs high-dimensional blocks.
  - The step sizes need `L_j`, `σ_j`, `Δ` and `ε`. A block-adaptive method attaining `S³` is open.

## How the strict research requirements are met

- The setup is popular and important: layer-wise heterogeneity of smoothness and noise, as in LARS/LAMB, AdaGrad/Adam-type and layer-wise LMO optimizers.
- Both an upper bound (this file) and a lower bound ([companion](BlockHeterogeneousLowerBound.md)) are proved in Template / TemplateLowerBound. They are tight up to a universal constant (≈ 20·2^57) on the common regime.
- Lower-bound techniques are reused (Arjevani et al.; repository PR #185), as allowed.
