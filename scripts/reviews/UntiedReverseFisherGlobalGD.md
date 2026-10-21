# UntiedReverseFisherGlobalGD: novelty assessment

[Theorem](../../LongTails/Theorems/UntiedReverseFisherGlobalGD.lean) · [Setup](../../LongTails/Setups/UntiedGaussianReverseFisher.lean) · [Algorithm](../../LongTails/Algorithms/UntiedReverseFisherGD.lean)

The theorem fits an untied two-mean student `½N(µ₀,I)+½N(µ₁,I)` to a teacher `½N(µ̄₀,I)+½N(µ̄₁,I)` in `ℝ^d`. It runs constant-step GD (`γ = 1/32`) using exact gradients of the population reverse Fisher loss `E_{x∼p_µ}‖s_µ(x)−s̄(x)‖²`, started from a mirrored random point `(w,−w)` with `w` a normalized uniform-cube point. With probability `≥ 1−δ`, the last iterate satisfies `min_π Σᵢ‖µᵢ^K − µ̄_{π(i)}‖² ≤ ε`.

**Proved budget.** The parameters are as follows:
- `d ≥ 1` is the dimension.
- `Δ = ‖µ̄₀−µ̄₁‖` is the separation. The algorithm receives a bound `s`, and the theorem requires `0 ≤ s ≤ Δ ≤ 1`.
- `B ≥ ‖(µ̄₀+µ̄₁)/2‖` bounds the teacher centre.
- `ε ∈ (0,1]` is the squared accuracy and `δ ∈ (0,1]` the failure probability.

The budget counts exact-gradient calls:

  K = O( log(d(1+B)/(δε)) / max(s², ε) )   (constants 10¹⁶ and 10²⁰ are in the Lean budget).

The constant step is enforced by `allowedAlgorithm = constantStepGD`: the same `γ` in every state, querying the current point and returning it as output. The budget depends on the supplied `s`, not on `Δ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin, [arXiv:2606.19876v1](https://arxiv.org/abs/2606.19876) (18 Jun 2026, preprint), Thm 2.1 / Cor 2.5. **Restriction:** single teacher, i.e. `Δ = 0` | Cor 2.5 with `n = 2` gives `O(1/ε + log(R₀²/ε))`. From this start `R₀ ≤ 1+B`, so `O(1/ε + log((1+B)/ε))` → `O(log(d(1+B)/(δε))/ε)` at `s = 0` | **Worse** at `Δ = 0` by the factor `log(d(1+B)/(δε))` | Single-Gaussian teacher → any teacher with `0 ≤ Δ ≤ 1` and unknown centre `‖ū‖ ≤ B` | None. Tyurin's bound is deterministic, holds from any start, and covers all `k ≥ K`. This result covers one fixed `K` and needs a random start. | `n = 2` only, while Tyurin allows any `n`. Mirrored start, not arbitrary. Adds a `log(1/δ)` cost. |
| Tyurin, same paper, Thm 3.2 / E.1. **Restriction:** `Δ ≥ 2¹⁰√(log(2²⁰n³max{n,m}R₀⁴/ε²))·(…)` and `d ≥ 8 + …`, a class disjoint from `Δ ≤ 1` | `Θ̃(n²/ε) = Θ̃(1/ε)` (large-sphere start, closest-teacher criterion) → `O(log(d(1+B)/(δε))/max(s²,ε))` | **Not comparable:** the classes are disjoint | Separation `≥ 2¹⁰√log(…/ε)` → `0 ≤ Δ ≤ 1`, including `Δ = 0`. The classes are complementary, not nested. Dimension condition → `d ≥ 1`. | "Closest-teacher ε-close" → recovery up to permutation | General `n, m` → `n = m = 2`. The window `1 < Δ ≲ √log(1/ε)` remains uncovered. |
| Same exact-gradient oracle with any algorithm (problem-class baseline; reduction sketched below, **unverified**) | Plausibly `O(1)` calls → `O(log(d(1+B)/(δε))/max(s²,ε))` | **Worse** if the sketch holds. The companion note concedes this. | None | None | The selected result only constrains constant-step GD. |
| Repository [`SymmetricReverseFisherGlobalGD`](SymmetricReverseFisherGlobalGD.md) (2026-10-19). **Restriction:** tied `±θ`, centre 0 | On the overlap (`ū = 0`, `Δ ≤ 1`) both budgets are `O(log(d/(δε))/max(s²,ε))` | None: same order | Tied student, known centre → untied student, unknown centre `‖ū‖ ≤ B` | None | The symmetric result covers every `Δ`, but this one needs `Δ ≤ 1`. It also inherits that result's NO IMPROVEMENT review. |

**Reduction check.** The proof's gradient formula (`hasGradientAt_loss`) gives `g(x) = (x−ū) − ½R_a(⟨x−ū,b⟩)b` for both components at a query `µ₀ = µ₁ = x`, where `b = (µ̄₀−µ̄₁)/2` and `a = ‖b‖`.
- Differences of two queries reveal the direction of `b`, and `g` then gives the component of `ū` orthogonal to `b`.
- Two or three further scalar equations in the unknowns `(⟨ū,e⟩, a)` remain. I did not verify that they are injective, which is why that row is marked unverified.
- On the tied slice, the sibling review verified a two-call GD-family solution.

So the oracle model makes the problem class easy. The theorem has content only as a statement about constant-step GD.

**New mechanism and proof ancestry.** The new technical step is an exact decoupling of the loss (`loss_decomposition`) into:
- a centre term `‖w‖²`;
- the tied radial term;
- two scalar ridge potentials.

For `a ≤ ½`, the decoupling yields a uniform centre contraction (`centre_norm_step`). It also reduces the axis dynamics to the tied map plus a defect that is multiplicative in `κ`. The phase analysis, scalar functions and lemmas are reused from the repository's tied proof. Tyurin's Lyapunov analysis is conceptual ancestry, not a baseline. Population EM for the same untied model ([Xu–Hsu–Maleki, arXiv:1608.07630](https://arxiv.org/abs/1608.07630); qualitative global convergence; venue not rechecked) uses a different oracle. [Shah–Chen–Klivans, NeurIPS 2023](https://arxiv.org/abs/2307.01178) uses the forward DDPM objective with sample access and a symmetric model. Neither is a table baseline.

**Search coverage (2026-10-21 UTC).** I searched the web and arXiv for:
- reverse/forward Fisher and score-matching GD on Gaussian mixtures;
- small-separation results;
- EM and gradient EM for two-component mixtures.

I read Tyurin v1's Thm 2.1, Cor 2.5, Thm 3.2 and E.1 and its future-work remark in HTML. I did not reread Xu–Hsu–Maleki's theorems. I found no later reverse-Fisher work on near-zero separation, but OpenReview and 2026 proceedings were not crawled.

The companion note's descriptions of Tyurin are accurate. However, it describes the `Δ = 0` endpoint as having "the same `1/ε` shape" and omits that the full bound there is worse by a multiplicative `log(d(1+B)/(δε))`.

## Conclusion

**No oracle-complexity improvement; what is new is a GD-dynamics guarantee in a regime Tyurin left open, for two components only.** The strongest baseline is Tyurin's June 2026 constant-step reverse-Fisher GD analysis:

| Regime | Tyurin (v1) | This result |
|---|---|---|
| `Δ = 0` | `O(1/ε + log((1+B)/ε))`, any start, deterministic | `O(log(d(1+B)/(δε))/ε)`, w.p. `1−δ` |
| `0 < Δ ≤ 1` | no guarantee (needs `Δ ≳ 2¹⁰√log(1/ε)`) | `O(log(d(1+B)/(δε))/max(s²,ε))` |

Where the two overlap (`Δ = 0`), this result is worse by a logarithmic factor. For `0 < Δ ≤ 1` it is the first guarantee I found for this GD method. With the exact population-gradient oracle, the problem itself appears solvable in `O(1)` calls by non-constant-step methods (verified for the tied slice, sketched for this one). The constant-step restriction is therefore what gives the result its meaning.

The gain is modest for concrete reasons:
- It covers only `n = m = 2` with a special mirrored start.
- It leaves the window `1 < Δ ≲ √log(1/ε)` open.
- It is a perturbative extension of the repository's tied analysis.

My search found no competing analysis, but that does not establish priority. What can be claimed is a new, apparently unpublished proof that constant-step reverse-Fisher GD recovers two untied, weakly separated means, which partially answers Tyurin's near-zero-separation question.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
