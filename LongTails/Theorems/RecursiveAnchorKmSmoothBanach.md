# Stochastic fixed points of nonexpansive maps in 2-uniformly smooth Banach spaces: ε⁻² oracle complexity

## Result in one sentence
Recursive anchoring with stochastic Krasnosel'skii–Mann (KM) inner loops finds a point with expected fixed-point residual at most ε. It needs

  ⌈ℓ · (16 + 20 D/ε + 2048 K σ² ℓ² / ε²)⌉ oracle calls, where ℓ = log₂(1 + D/ε) + 4.

This holds in any real Banach space that is 2-uniformly smooth with constant K, under the standard unbiased, bounded-variance, IID oracle model.

In order notation the bound is O(log(D/ε) · D/ε + K σ² log³(D/ε) / ε²). To our knowledge this is the first ε⁻² guarantee outside Hilbert space for nonexpansive maps when the oracle is only unbiased with bounded variance, with no per-sample regularity: no samplewise nonexpansiveness, no Lipschitzness in expectation and no common-seed two-point queries. Under these assumptions the best previous guarantees on this class were ε⁻³ or ε⁻⁴. Under the stronger samplewise-nonexpansive oracle, ε⁻² was already known in quadratically smoothable spaces ([2607.09097](https://arxiv.org/abs/2607.09097)).

## Setup
Lean file: [`LongTails/Setups/StochasticFixedPointSmoothBanach.lean`](../Setups/StochasticFixedPointSmoothBanach.lean)

**Space.**
- `E` is a real Banach space. It is assumed separable (`SecondCountableTopology`) and carries its Borel σ-algebra. These are measure-theoretic requirements that exclude none of the examples below.
- `E` is 2-uniformly smooth in Xu's form: there are K and a map j : E → E* with

    ‖x + y‖² ≤ ‖x‖² + 2 j(x)(y) + K ‖y‖²  for all x, y ∈ E.

  This is the standard characterization (H.-K. Xu, *Inequalities in Banach spaces with applications*, Nonlinear Anal. 1991). The same assumption is used in [2610.00295](https://arxiv.org/abs/2610.00295), §4, and in [Juditsky–Nemirovski, 0809.0813](https://arxiv.org/abs/0809.0813).
- Examples: any Hilbert space (K = 1, j(x) = ⟨x, ·⟩); ℓ_p, L_p and the Schatten class S_p for 2 ≤ p < ∞ (K = p − 1).
- No measurability, normalization or norm bound is required of j.

**Problem.**
- T : E → E is nonexpansive on all of E and has a fixed point x⋆ with ‖x0 − x⋆‖ ≤ D. This is the unconstrained setting of 2610.00295. It does not cover a nonexpansive self-map of a closed convex subset, as in the compact-domain setting of 2609.09524; in Banach spaces such a map need not extend nonexpansively to E.
- Validity: 0 ≤ K, 0 < D, 0 ≤ σ, 0 < ε.

**Oracle.**
- Each query x is answered by `M.sample ξ x`, with a fresh sample ξ.
- The samples (ξ_k) are IID with law `M.law`. This uses the repository's `IID` structure: measurability, `iIndepFun`, and marginal laws.
- `M.sample` is jointly measurable.
- It is Bochner-unbiased: ∫ sample(ξ, x) = T x.
- Its variance in the native norm is bounded: ∫ ‖sample(ξ, x) − T x‖² ≤ σ².

**Accuracy criterion.**
- The output is measurable, and ‖x̂ − T x̂‖ is integrable with E‖x̂ − T x̂‖ ≤ ε.
- This is the criterion of 2610.00295, 2610.26484 and 2609.09524 (the last in high probability).

The algorithm receives only the public parameters (K, σ, D, ε, x0). It does not know T, x⋆, j or the law of the samples. The setup imposes no `allowedAlgorithm` restriction, since the contribution concerns the problem class.

## Algorithm
Lean file: [`LongTails/Algorithms/RecursiveAnchorKm.lean`](../Algorithms/RecursiveAnchorKm.lean), definitions `recursiveAnchorKm` and `tunedAnchorKm`.

**Weights.**
- λ = ε/(4D) and S = ⌈log₂⌈4D/ε⌉⌉.
- Anchor weights λ_t = 2^t λ, with cumulative weights Λ_u = Σ_{t≤u} λ_t = (2^{u+1} − 1)λ.

**Stages u = 0, …, S.** Stage u keeps the anchor vector A_u = Σ_{t≤u} λ_t x̂_t, where x̂_0 = x0. It runs N_u single-sample KM steps on the regularized map T_u(y) = (T y + A_u)/(1 + Λ_u), which is a 1/(1+Λ_u)-contraction:

  y ← (1 − α_u) y + α_u/(1 + Λ_u) · (sample(ξ, y) + A_u).

The stage ends with x̂_{u+1} = y, and the new anchor λ_{u+1} x̂_{u+1} is added to A.

**Tuning.**
- Targets: η_u = ε/(6(S+1)λ_{u+1}) for u < S, and η_S = ε/(4(S+1)).
- Steps: α_u = a_u/(a_u + 2Kσ²), with a_u = η_u² Λ_u (1+Λ_u). So α_u = 1 when σ = 0.
- Lengths: N_u = M_u ⌈(1+Λ_u)/Λ_u + 2Kσ²/(η_uΛ_u)²⌉, with M_0 = 2S + 7 and M_u = 5 for u ≥ 1.

**Output.** The output is x̂_{S+1}, the last iterate of the last stage. If the budget exceeds Σ N_u, the algorithm idles, so every oracle call it makes is counted.

## Theorem
Lean file: [`LongTails/Theorems/RecursiveAnchorKmSmoothBanach.lean`](RecursiveAnchorKmSmoothBanach.lean), `result : Convergence spec budget`. The budget is the one-line formula above.

Supporting proofs live in `LongTails/Proofs/RecursiveAnchorKm{Deterministic,Stochastic,Expectation,Schedule,Execution,Convergence}.lean`.

## Proof idea
1. **Norm-only anchoring geometry** (`RecursiveAnchorKmDeterministic`).
   - Let z_u be the unique point with (1+Λ_u) z_u = T z_u + A_u. The map x ↦ (1+Λ)x − Tx is Λ-expansive in any norm.
   - Let δ_u = ‖x̂_{u+1} − z_u‖ and Q_u = ‖A_u − Λ_u z_u‖. Pathwise:
     - Q_0 ≤ 2λD;
     - Q_{u+1} ≤ Q_u + 3λ_{u+1} δ_u;
     - ‖x̂_{u+1} − z_{u+1}‖ ≤ 2δ_u;
     - ‖x̂ − T x̂‖ ≤ 2δ_S + Q_S.
   - No inner product or monotonicity is used.
2. **Stochastic KM on a contraction in a 2-uniformly smooth space** (`RecursiveAnchorKmStochastic`).
   - Write the step error as a + cζ, where a depends only on the past, ‖a‖ ≤ ρ‖y − z‖ and ρ = 1 − αΛ/(1+Λ).
   - Xu's inequality gives E‖a + cζ‖² ≤ ‖a‖² + 2c j(a)(Eζ) + Kc²σ² = ‖a‖² + Kc²σ², because j(a) is a continuous linear functional and Eζ = 0.
   - The past/future factorization uses independence through the repository's prefix-product lemma. All expectations are lintegrals.
3. **Error chain** (`RecursiveAnchorKmExpectation`, `RecursiveAnchorKmSchedule`).
   - The stage targets and lengths give E δ_u² ≤ η_u² inductively. Bernoulli's inequality gives the contraction count ρ^{2N_u} ≤ 4^{−M_u}.
   - Then 3λ_{u+1}η_u = ε/(2(S+1)), and summing gives E‖x̂ − T x̂‖ ≤ ε/2 + ε/2.
4. **Cost.**
   - Each stage costs O(1/Λ_u + K σ² S²/ε²) up to the halving factor M_u. The deterministic parts sum to O(log S · D/ε), and the noise parts to O(K σ² S³/ε²).
   - The schedule and every oracle call are tied to the actual execution in `RecursiveAnchorKmExecution`.

Both ingredients are individually standard. The outer loop is the recursive anchoring of 2609.09524. The smooth-space mean-square recursion is that of Juditsky–Nemirovski (0809.0813) and 2610.00295, Remark 4.4. The essential new point is how they are combined, in step 2. Earlier recursive-anchoring analyses in normed spaces (2609.09524) estimate T inside each anchored stage by a median-of-means minibatch at every step. Earlier 2-uniformly-smooth analyses (2610.00295) apply the smooth-space recursion to a single Halpern or KM sequence. Applying the smooth-space mean-square recursion to the strongly contractive regularized maps T_u removes per-step minibatching. Each stage then costs only Kσ²/(η_uΛ_u)² = O(Kσ²S²/ε²) samples, because the product η_uΛ_u stays of order ε/S at every stage.

## Comparison with prior work (expected residual unless stated)

| Paper | Space and assumptions | Guarantee |
|---|---|---|
| Chen–Luo, as used in [2610.00295](https://arxiv.org/abs/2610.00295) Thm 4.8 | Hilbert (F = I − T monotone, 2-Lipschitz) | Θ̃(σ²/ε² + D/ε): upper bound and matching lower bound |
| [2609.28543](https://arxiv.org/abs/2609.28543), [2608.12043](https://arxiv.org/abs/2608.12043) | Hilbert only | Õ(σ²/ε²) upper bounds |
| [2610.00295](https://arxiv.org/abs/2610.00295) Thm 4.3 | 2-uniformly smooth (Xu constant K), same oracle | O(K σ² D² ε⁻⁴) |
| [2610.26484](https://arxiv.org/abs/2610.26484) Thm 3 (dual Halpern) | ℓ_p, 2 ≤ p < ∞ | O(D/ε + (p−1) D σ² ε⁻³) |
| [2609.09524](https://arxiv.org/abs/2609.09524) (recursive anchoring + median-of-means) | type-2 normed spaces, high probability | Õ(σ² ε⁻³ + 1/ε); lower bound Ω(σ²ε⁻³) on ℓ∞^d with d ≳ 1/ε (Thm 13) |
| [2608.15966](https://arxiv.org/abs/2608.15966) | finite-dimensional Banach, Markovian samples | Õ(ε⁻³) |
| [2607.09097](https://arxiv.org/abs/2607.09097) (VR-GHAL) | quadratically smoothable Banach, high probability | ε⁻⁵ under bounded variance only; ε⁻³ under Lipschitzness in expectation; ε⁻² under samplewise nonexpansiveness |
| [2403.12338](https://arxiv.org/abs/2403.12338) | finite-dimensional normed | Õ(ε⁻⁵); lower bound Ω(σ²ε⁻³) for span-based averaged iterations, built in (ℝ^d, ‖·‖₁) with d ≍ 1/ε (Thm 3.7) |
| **This result** | 2-uniformly smooth (any K), unbiased IID oracle | O(log(D/ε)·D/ε + K σ² log³(D/ε)/ε²) |

**Improvement regimes.**
- Against 2610.00295 (same class): a factor of order D² ε⁻² / log³ in the noise term.
- Against 2610.26484 (ℓ_p): the noise term drops from (p−1)Dσ²ε⁻³ to (p−1)σ² log³(D/ε) ε⁻², a gain of order (D/ε)/log³(D/ε).
  - The deterministic term is worse by a factor log(D/ε). In the noiseless or low-noise regime σ² ≲ D ε/log², Lee's O(D/ε) is better by that log factor.
- Against 2609.09524: in 2-uniformly smooth spaces the noise term improves from Õ(σ²ε⁻³) to Õ(Kσ²ε⁻²). That paper gives high probability over the larger type-2 class, while this result is in expectation only.

**Why this does not contradict the ε⁻³ lower bounds.**
- Both known ε⁻³ lower bounds live in spaces with no dimension-free 2-uniform smoothness constant: ℓ∞^d for 2609.09524, and ℓ₁^d for 2403.12338, each with d ≍ 1/ε.
- Passing to an equivalent ℓ_{log d} norm does not help, because it destroys nonexpansiveness.
- Together with this result, the lower bounds therefore give a geometric separation. The residual problem costs ε⁻² up to logarithms in 2-uniformly smooth spaces and ε⁻³ in ℓ∞ or ℓ₁.
- 2607.09097 (line 205) states, about the bounded-variance setting without samplewise regularity, that it is "unclear whether [ε⁻²] scaling can be transferred to other norms; in fact, there is evidence that this may not be possible [BC26]". This result shows that for nonexpansive maps under a bounded-variance oracle the ε⁻² scaling does transfer to every 2-uniformly smooth norm.

## Limitations
- **Expectation only.** No high-probability bound is proved. A median-of-means wrapper on stage outputs is a natural extension that is not done here.
- **Log factors.** The bound has log³(D/ε) on the noise term and log(D/ε) on the deterministic term. The Hilbert lower bound Ω(σ²/ε² + D/ε) of Chen–Luo (see 2610.00295, Thm 4.8) is matched only up to these logarithms and the factor K.
- **K-dependence lower bound.** Whether the linear dependence on K (for ℓ_p, on p − 1) is necessary is open. The known lower bound applies to the Hilbert subclass, K = 1.
- **Unconstrained maps.** T must be nonexpansive on all of E. Constrained self-maps of closed convex sets are not covered (see Setup).
- **Known parameters.** The algorithm needs K, σ, D and ε, as do the compared methods.
- **Non-2-smooth norms.** ℓ_p with 1 < p < 2 (only p-uniformly smooth), ℓ₁, ℓ∞, and type-2 spaces without an equivalent 2-uniformly smooth norm that keeps T nonexpansive are not covered.
- **Scope of the novelty claim.** The literature search covered arXiv through 2026-10-22 and the cited conference versions. Novelty is relative to those sources.
