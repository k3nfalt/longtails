This result proves that **no randomized algorithm** with value-and-subgradient access can minimize a μ-weakly sharp, L-Lipschitz convex function to expected accuracy ε in fewer than

**⌊(L/μ)² · (1 + log(μD/ε)) / 4608⌋ oracle calls**

in sufficiently high dimension, for every κ = L/μ ≥ 96 and 0 < ε ≤ μD. The algorithm may be randomized, or deterministic without any span condition. Together with the classical restarted subgradient method, formalized for the same oracle and criterion in [SharpLipschitzConvexRestartedSubgradient](SharpLipschitzConvexRestartedSubgradient.lean), this settles the oracle complexity of the class up to a universal constant factor on that whole regime:

**Θ((L/μ)² · (1 + log(μD/ε))).**

Before this result, the logarithmic factor was proved only for *subgradient-span* methods, by [Wang (arXiv 2512.13863 v1, Dec 2025)](https://arxiv.org/abs/2512.13863). For general deterministic methods and for randomized methods, the best known lower bound was the log-free Ω((L/μ)²) of Juditsky and Nesterov.

## Setup

The [main theorem](SharpLipschitzConvexLowerBound.lean) uses [HighDimensionalSharpLipschitzConvex](../Setups/HighDimensionalSharpLipschitzConvex.lean). Its parameters, instances, oracle and success criterion are by definition those of [SharpLipschitzConvex](../Setups/SharpLipschitzConvex.lean), the setup of the upper bound.

Public parameters are d, L, μ, D, ε and x₀ ∈ ℝᵈ. An admissible instance is f : ℝᵈ → ℝ with:

- **Convexity:** f is convex.
- **Lipschitz continuity:** |f(x) − f(y)| ≤ L‖x − y‖.
- **Initial distance:** some minimizer x⋆ satisfies ‖x₀ − x⋆‖ ≤ D.
- **Global weak sharpness:** for every x there is a minimizer z with μ‖x − z‖ ≤ f(x) − f(z), that is, f(x) − f⋆ ≥ μ·dist(x, argmin f).
- **Oracle:** the oracle returns (f(x), g(x)) for a fixed subgradient selection g, so f(y) ≥ f(x) + ⟨g(x), y − x⟩ for all y.

Success means that the output's objective gap f(x̂) − f(x⋆), for some minimizer x⋆, is integrable with expectation at most ε.

Weak sharpness (Polyak's sharp minimum) is the standard nonsmooth error bound. Examples include consistent ℓ₁/ℓ_∞ regression, polyhedral convex functions and distances to convex sets. It is studied for subgradient methods in, among others, [Yang–Lin, JMLR 2018](https://arxiv.org/abs/1512.03107), [Davis–Drusvyatskiy–MacPhee–Paquette, JOTA 2018](https://arxiv.org/abs/1803.02461) and [Wang 2025](https://arxiv.org/abs/2512.13863).

`valid` restricts the parameters, with κ = L/μ:

- 0 < μ and 96μ ≤ L, that is, κ ≥ 96;
- 0 < D and 0 < ε ≤ μD;
- d ≥ 2¹⁰ · (1 + κ²(1 + log(μD/ε)))⁶ · (LD/ε)².

These conditions restrict only the parameter point, not the instances. Every valid point here is also valid for the upper-bound setup, which only asks 0 < μ ≤ L, D > 0 and ε > 0.

## Theorem

`result : NonConvergence spec budget` with

budget p = ⌊(L/μ)² · (1 + log(μD/ε)) / 4608⌋₊.

- For every valid p, every randomized algorithm A and every budget b ≤ budget p, including b = 0, there is an admissible instance and oracle on which the expected gap of A's output after b calls exceeds ε.
- Queries and outputs are arbitrary and adaptive. No span, zero-respecting or other algorithm restriction is imposed.
- The instance depends on A and b, but not on A's realized seed.
- The hard instances have f⋆ = 0, so the bound holds even if the optimal value is revealed, and Polyak-type methods gain nothing from it.
- The regime is nonempty with a nontrivial budget. For example, L = 96, μ = 1, D = 1 and ε = 1/e give budget 4, for any d ≥ 2¹⁰ · 18433⁶ · (96e)².
- The budget is at least 1 whenever κ² ≥ 4608. So for large κ the bound is nontrivial even at ε = μD, where it reduces to the log-free Ω(κ²).

## Hard instance

All pieces are written in shifted coordinates u = x − x₀, and the instance is f(x) = (L/3)·F(u). Fix a chain length k = b, a ratio μ₀ = 48μ/L ≤ 1/2 and a hidden injective word π : {0, …, k} ↪ {1, …, d}. The geometric radii are Δ_m = D(1 − μ₀²)^{m/2}. The hidden target t has t_{π(j)} = −μ₀Δ_j for j < k and t_{π(k)} = −Δ_k, with zeros elsewhere. Its tails satisfy Σ_{j ≥ m} t_{π(j)}² = Δ_m²; this is Wang's recursion with h(s) = μ₀s. F is the maximum of three kinds of convex pieces ([SharpChainGeometry](../Proofs/SharpChainGeometry.lean)):

- **Chain pieces**, m = 0, …, k:

  φ_m(u) = μ₀ √(Σ_{j<m} (u_{π(j)} − t_{π(j)})² + Δ_m²) + u_{π(m)} − m·γ,

  with offset step γ = μ₀Δ_k/(4(k+1)).
- **A half-weight radial piece** R(u) = (μ₀/2)·‖P_π u − t‖, where P_π restricts to the hidden coordinates.
- **A cone** C(u) = 3‖u‖ − 9D.

The oracle answers with the value and the gradient of a maximizing piece. Ties are broken by a fixed order: the cone first, then the chain (first strict maximum), then the radial piece. This selection is a valid subgradient everywhere, and it is deterministic and history-free.

Proved properties ([SharpChainInstance](../Proofs/SharpChainInstance.lean), [SharpChainMargins](../Proofs/SharpChainMargins.lean), [SharpChainSharpness](../Proofs/SharpChainSharpness.lean)):

1. **Convexity and Lipschitz continuity.** F is convex and 3-Lipschitz, so f is L-Lipschitz. This follows from the inequality ⟨a, b⟩ + s² ≤ √(‖a‖² + s²)√(‖b‖² + s²), which yields a subgradient inequality for every piece.
2. **Minimum value.** F ≥ R ≥ 0, and F = 0 at every point that agrees with t on the hidden coordinates and has norm at most 3D. At such points each chain piece is ≤ 0, thanks to the exact cancellation of u_{π(m)} against t_{π(m)}. In particular x⋆ = x₀ + t is a minimizer with ‖x₀ − x⋆‖ = ‖t‖ = D.
3. **Global sharpness with respect to the true argmin.** For every u there is a minimizer z with (μ₀/16)‖u − z‖ ≤ F(u). The proof combines the radial piece, which controls the hidden error, with the cone, which controls the excess norm in the orthogonal directions. After scaling, this is μ-sharpness for f because (L/3)(μ₀/16) = μ.
4. **Robust zero chain.** Suppose that ‖u‖ ≤ 8D and every not-yet-revealed hidden coordinate u_{π(j)}, j ≥ t, has absolute value at most θ = μ₀Δ_k/(32(k+1)²).
   - Then every φ_m with m > t and the radial piece are *strictly* below the best of φ_0, …, φ_t.
   - The proof compares with the point whose tail coordinates are zeroed, where the values are exact. The offsets give margin γ, and the perturbation costs at most (3/2)(k+1)θ ≤ γ/8.
   - If ‖u‖ > 8D, the cone strictly dominates.
   - In both cases the full answer equals a *partial* answer that depends only on π(0), …, π(t).
5. **Large error at the end.** If the output u satisfies ‖u‖ > 8D or |u_{π(k)}| ≤ θ, then F(u) ≥ μ₀Δ_k/4. Hence f(x̂) − f⋆ ≥ 4μΔ_k ≥ 2ε, because Δ_k ≥ ε/(2μ) whenever μ₀²k ≤ (1 + log(μD/ε))/2. This uses (1 − x)^k ≥ e^{−2xk} for x ≤ 1/2, and e ≤ 4.

The hiding argument ([SharpChainHiding](../Proofs/SharpChainHiding.lean)) is the random-coordinate-word prefix simulation used for the repository's weak-Minty lower bound, with the counting lemma `bounded_prefix_bad_count`.

- A word is *bad* if one of the k + 1 observations (the k queries and the output, each in the ball of radius 8D) has a coordinate larger than θ at a position of π not yet revealed.
- By the prefix property, the fraction of bad words is at most (k+1)²(8D/θ)²/(d − k − 1), which is at most 1/4 under the dimension condition.
- On good words the actual execution coincides with the partial-answer simulation, and the output has loss at least 2ε. Averaging over words gives some word with expected loss above ε.
- The connection to the actual execution uses `OracleTemplate.execute`; see [SharpChainLowerBound](../Proofs/SharpChainLowerBound.lean).

## What was known, and what is new

- **[Wang, arXiv 2512.13863 v1](https://arxiv.org/abs/2512.13863), Theorem 2.** This shows that for any subgradient-span method, "x_n ∈ x₀ + span{g₀, …, g_{n−1}}", there is an instance in F_{h,L,D} with dist(x_n, argmin) ≥ Δ_n. For h(s) = μs, his rates Δ_n = D(1 − μ²/L²)^{n/2} give the same Ω((L/μ)² log(μD/ε)) order for span methods. His text after Corollary 1 states the resulting iteration count for Hölderian error bounds, with a log(cD/ε) term at θ = 1.
  - Wang's Introduction states the gap: "Even in the simplest setting of weakly-sharp Lipschitz convex optimization, lower bounds exactly matching the guarantees of PolyakGD or GeomGD have yet to be exhibited."
  - His result covers only span methods, and his class needs the error bound only within distance D of argmin f.
  - arXiv lists only v1 of this paper.
- **[Juditsky–Nesterov, arXiv 1401.1792](https://arxiv.org/abs/1401.1792) (Stochastic Systems 2014), Appendix, Theorem 8.** For Lipschitz uniformly convex classes on a ball this gives A(ε) ≥ min{n, ⌊L²R²/(16ε²)⌋, ⌊L²/(8ε^{2(ρ−1)/ρ})⌋}. Taken at the sharp end ρ = 1 with unit modulus, it is Ω((L/μ)²) with no dependence on ε. The proof is deterministic, via a resisting oracle following Nemirovski–Yudin Ch. 3.
- **Upper bounds.** Restarted or decaying-step subgradient and Polyak steps achieve O((L/μ)² log(μD/ε)) (Polyak 1969; [Yang–Lin 2018](https://arxiv.org/abs/1512.03107); [Davis et al. 2018](https://arxiv.org/abs/1803.02461); Wang's Theorem 1).

So for randomized algorithms, and also for deterministic methods without the span condition, the logarithmic factor was open. The present theorem closes it for both, since a deterministic algorithm is a randomized one with a trivial seed. It does so under global sharpness (a subclass of Wang's class, so the bound is stronger) and for the expected function-gap criterion. The additive κ² term is the classical log-free bound; it is reproved here inside the same statement, so the budget matches the upper bound uniformly over the regime.

**Why Wang's instance does not extend.** Wang's hard function is max(φ₁, …, φ_{N+1}, h(‖x − x⋆‖)), with a *full-weight* radial term. His proof uses the span condition to keep the iterates in the coordinate subspaces on which the resisting oracle can answer with a chain piece. Nothing in his construction controls the answer elsewhere. Wherever the radial term is the active piece, its subgradient is h′·(x − x⋆)/‖x − x⋆‖, which together with the value (for h(s) = μs) determines x⋆ from a single query. We did not check whether this happens at specific points of his instance. The point is that his argument offers no robustness guarantee off the span, and random-coordinate hiding needs exactly such a guarantee.

The construction here separates the two roles of the radial term:

- **Sharpness.** A *half-weight* radial piece certifies global sharpness but is provably never selected at the queries that matter (property 4).
- **Information.** Explicit lifted chain pieces carry the information and include the exact cancellation term u_{π(m)}.
- **Robustness.** Strictly ordered offsets mγ create margins, so the zero-chain structure survives small unrevealed coordinates.
- **Unbounded queries.** A cone handles far queries.

These ingredients make the chain *robust*, which is what random-coordinate hiding needs. Wang's paper itself identifies enforcing a global error bound as the core difficulty for lower-bound constructions.

## Limitations

- **Constants.** The constants are not optimized. Whenever the lower budget is positive, the upper/lower budget ratio is at most 15 · 9216 ≈ 1.4·10⁵, uniformly over the regime (see the upper-bound note).
- **Dimension.** The bound is a high-dimensional statement: d must be at least of order (κ² log(μD/ε))⁶ (LD/ε)². This is polynomial in κ, log(μD/ε) and LD/ε. The factor (LD/ε)² comes from using one global threshold θ ∝ Δ_k. A scale-dependent threshold might remove it; this is not attempted. In low dimension, cutting-plane methods with O(d log(LD/ε)) calls are faster, and no contradiction arises.
- **Parameter regime.** The lower bound requires κ ≥ 96 and ε ≤ μD. Its budget is zero, so it is vacuous, when κ²(1 + log(μD/ε)) < 4608.
- **Information asymmetry.** The upper bound uses L, μ, D and ε, and ignores the function value. The lower bound allows the value, all parameters, and even f⋆ = 0.
- **Oracle model.** Both sides use one oracle model: any fixed, history- and seed-independent subgradient selection together with the exact value.

## Scope

This is a tight upper/lower pair for a standard, widely used problem class: weakly sharp Lipschitz convex minimization, the canonical setting for linearly convergent subgradient methods. It is formalized with `Template` (`Convergence`) and `TemplateLowerBound` (`NonConvergence`), with the same oracle, instance class and accuracy criterion on both sides. The upper bound is known; the lower bound is new for randomized and non-span algorithms. The pair determines the complexity Θ((L/μ)²(1 + log(μD/ε))) up to universal constants in the stated high-dimensional regime.
