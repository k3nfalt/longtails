# KnownValueNondualGeneralizedRate: what is actually new?

The [theorem](../../LongTails/Theorems/KnownValueNondualGeneralizedRate.lean) ([setup](../../LongTails/Setups/KnownValueNondualGeneralizedConvex.lean), [algorithm](../../LongTails/Algorithms/KnownValueNondual.lean)) is deterministic. For every convex `C¹` function `f : ℝᵈ → ℝ` satisfying the symmetric `(L₀,L₁)` condition `‖∇f(x)−∇f(y)‖₂ ≤ (L₀ + L₁ sup_{z∈[x,y]}‖∇f(z)‖₂)‖x−y‖₂`, with a global minimizer `x⋆` such that `f(x⋆) = f⋆` (known) and `‖x₀−x⋆‖₁ ≤ R`, the returned incumbent satisfies `f(x̂) − f⋆ ≤ ε` after a fixed number of exact `(f(x),∇f(x))` calls.

**Complexity (paired value–gradient calls).** For `d ≥ 1` and `L₀,L₁,R,ε > 0`,

`N = O( (1 + (L₀R²/ε)^{1/3} + (L₁R)^{2/3}) · (1 + log(2d) + log(2 + L₀R²/ε + L₁R))² )`.

Here `L₀,L₁` are the generalized-smoothness constants, `R` is the ℓ₁ radius of the initial distance, `ε` is the objective accuracy, `d` is the dimension, and `f⋆` is the optimal value supplied to the method. This order is the exact budget `⌈2³⁶ Q ℓ²⌉`. Selector computation, an exact average of projections over a ball, is free in the model, and no efficient implementation is proved. Below, `A = L₀R²/ε` and `B = L₁R` abbreviate parameters only.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Rudomanov–Fomin–Gasnikov–Stonyakin, [arXiv:2610.21461v1](https://arxiv.org/abs/2610.21461) (15 Oct 2026, preprint), Thm 3.7. It applies because `‖·‖₂ ≤ ‖·‖₁`, so the target class is a subclass of theirs | `5√A + 240(1+B)log₂(64(1+B)) + 2` gradient calls → `O((1+A^{1/3}+B^{2/3})(1+log 2d+log(2+A+B))²)` | Exponents `A^{1/2}→A^{1/3}` and `B→B^{2/3}`, up to `log²`. Gain when `max(√A, B) ≫ (A^{1/3}+B^{2/3})(log(2d)+log(2+A+B))²`, e.g. `A = B²`, `d ≤ B`, `B→∞`: `Θ(B log B) → O(B^{2/3} log² B)` | None: the ℓ₁-prior class is a **subclass** of their ℓ₂-radius class | None (both are fixed-budget, last-point outputs) | Needs known `f⋆`, function values, and an ℓ₁ prior. Given only an ℓ₂ radius `R₂`, `R ≤ √d R₂` makes `A` grow by `d`. **Worse** by `log² d` when `A,B = O(1)` and whenever `log²(2d) ≳ max(A^{1/6}, B^{1/3})` |
| Martínez-Rubio–Bullins–Guzmán–Molina, [arXiv:2609.21880v1](https://arxiv.org/abs/2609.21880) (18 Sep 2026, preprint), Thms 1, 6, eq. (26), at `κ=2, p=1, q=2`. It needs uniformly `L`-Lipschitz gradients near the ℓ₁ ball | Smooth overlap (`L = L₀`, `B ≤ 1`): `Õ(1+A^{1/3})` with `log⁸(2d…)` → `O((1+A^{1/3}) log²(2d(2+A)))`. For `B > 1`, the uniform `L` on the ball can be `≈ L₀e^{Θ(B)}` (e.g. `cosh`), giving `Õ(A^{1/3}e^{Θ(B)})` | Overlap: none (same order; fewer log powers in a stated upper bound only). For `B ≫ 1`: exponential → `B^{2/3}` | Global Lipschitz gradient near the ball → `(L₀,L₁)`-smoothness with polynomial cost | None. Their method needs no `f⋆`, and its randomized version has probability `1−δ` | Needs `f⋆`. Theirs is polynomial-time, but no implementation is given here |

**Reduction check and proof ancestry.** I found no published composition giving `B^{2/3}` with `A^{1/3}`. Everest's `B^{2/3}` (App. B, Thm B.7) needs `f(x₀)−f⋆ ≤ 4ε` and keeps `√A`. Running MR26 after an Everest-style warmup is not immediate, because the warmup controls ℓ₂ distance but not the ℓ₁ distance that MR26 needs. The note's reconstructed restart composition, `Õ(A^{1/3}+B^{3/4})`, is plausible, but I did not verify it. The new mechanism is a persistent cut body across target-halving phases, with curvature-weighted failure counts charged to one global selector movement. This pays `√(Bq)` rather than `√B·q`. The proof ancestry is the movement-to-acceleration coupling of MR26 (Thm 4), the movement selectors of [Martínez-Rubio–Guzmán, arXiv:2609.20701](https://arxiv.org/abs/2609.20701), and Everest's generalized-smooth descent inequalities.

**Optimality.** Everest Thm 4.8 (hard instances in `ℝ^{2n}` with `min f = 0`) applied at Euclidean radius `R/√(2n)` gives a valid ℓ₁ instance. It yields a deterministic `Ω̃(B^{2/3})` bound when `d ≥ 2n` and `n log(1+L₁²ε/L₀) ≲ B/√n`; I checked this arithmetic. MR26 states that `A^{1/3}` matches Guzmán–Nemirovski lower bounds up to logarithmic factors. I did not check whether those bounds survive a known `f⋆`.

**Search coverage (2026-10-29).** I searched arXiv and the web for `(L₀,L₁)` acceleration, ℓ_p/ℓ_q nondual methods, and known-value level methods. I read the Everest theorems, MR26 Thms 1, 4, and 6 with eq. (26), and the MG26 abstract. I did not verify MG26's "Fact 7" or Deng–Lan–Lin. The theorem was introduced in commit `93028ae` on 2026-10-29, after every cited preprint. The note's citations match what I checked. These are fresh, unrefereed preprints, and MR26 calls itself an unpolished draft.

## Conclusion

**Yes. For ℓ₁-bounded initial distance with a known `f⋆`, the proved bound is polynomially better than the best checked baselines.**

The strongest applicable baseline is Everest Thm 3.7, which applies because the ℓ₁ ball lies inside the ℓ₂ ball. On the full class, MR26's ℓ₁/ℓ₂ smooth method pays a uniform smoothness constant that can be exponential in `L₁R`.

| | paired calls |
|---|---|
| Everest Thm 3.7 | `O(√(L₀R²/ε) + (1+L₁R)log(2+L₁R))` |
| this result | `O((1+(L₀R²/ε)^{1/3}+(L₁R)^{2/3})·log²(2d(2+L₀R²/ε+L₁R)))` |

For example, with `L₀R²/ε = (L₁R)²` and `d ≤ L₁R`, the cost drops from `Θ(L₁R log L₁R)` to `O((L₁R)^{2/3} log²(L₁R))`. The result loses when `L₀R²/ε` and `L₁R` are small or `d` is astronomically large, because of the `log² d` factor. It also requires `f⋆`, function values, and an ℓ₁ rather than ℓ₂ prior. At `L₁R ≤ 1` it only matches MR26's smooth rate, and selector computation is not shown to be efficient.

The comparison proves this gain, and lower bounds suggest both exponents are near-optimal for deterministic methods. Priority is less certain because the field moves fast and an unpublished restart composition might reach `B^{3/4}`, though I found no `B^{2/3}` result. The claim that can be made is the first checked near-`Õ(A^{1/3}+B^{2/3})` oracle bound for generalized-smooth convex minimization under an ℓ₁ prior with known optimal value.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
