# Novelty assessment: SlidingStochasticCompositeLowerBound

The [theorem](../../LongTails/Theorems/SlidingStochasticCompositeLowerBound.lean) proves `NonConvergence` for the class in [setup](../../LongTails/Setups/HighDimensionalSlidingStochasticComposite.lean) (which reuses [SlidingStochasticComposite](../../LongTails/Setups/SlidingStochasticComposite.lean)). The class is `F = f + h` on `ℝ^d`, with `f` `ℓ`-smooth and nonconvex, `h` convex and `L`-smooth, exact `∇f` (oracle 0) and IID unbiased `∇h` with variance `σ²` (oracle 1, sample space `Bool`). Success means `E Γ(x̂) ≤ ε²/(8ℓ)`, where `Γ` is the Moreau gap at scale `ℓ`. The theorem shows that every randomized algorithm fails at every componentwise budget `b ≤ budget`, using a seed-independent hard instance.

**Proved necessary budget.** Here `ℓ` is the smoothness of `f`, `L` the smoothness of `h`, `Δ` the initial gap, `σ²` the variance and `K` the free allowance for the other oracle. Success requires:

- more than `⌊ℓΔ/(2⁶⁰ε²)⌋` calls to `∇f`, for any number `K` of `∇h` calls;
- more than `⌊(ℓΔ/ε²)(1 + σ²/ε² + √(L/ℓ))/2⁶⁰⌋` calls to `∇h`, for any number `K` of `∇f` calls.

So the bounds are `Ω(ℓΔ/ε²)` and `Ω(ℓΔσ²/ε⁴ + √(ℓL)Δ/ε²)`. The result is valid for `0 < ℓ ≤ L`, `σ ≥ 0` and `2⁶²ε² ≤ ℓΔ`, with dimension `d ≥ 2²⁰⁰(1 + K + ℓΔ/ε²·(1 + σ²/ε² + √(L/ℓ)))(1 + ℓΔ/ε²)³(1 + √(L/ℓ))⁹`. Choosing `d` large enough makes this regime nonempty.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Carmon–Duchi–Hinder–Sidford, *Lower bounds I*](https://arxiv.org/abs/1710.11606), Thm 2 at p=1 (randomized; Math. Prog. 2020). It applies here with `h = 0`. | `Ω(ℓΔ/ε²)` → `Ω(ℓΔ/ε²)` `∇f` calls | None: same order | None. The `∇h` oracle carries no information when `h = 0`. | `E‖∇F‖ ≤ ε` → `E Γ ≤ ε²/(8ℓ)`. Up to constants, the Moreau-gap version is the stronger lower-bound statement; the transfer is routine. | Constant `2⁻⁶⁰`; polynomial dimension requirement. |
| [Arjevani et al. 2023](https://arxiv.org/abs/1912.02365), Thm 3 (randomized; cite v2, which corrects the dimension). It applies via the reduction below. | `Ω(ℓΔσ²/ε⁴)` → `Ω(ℓΔσ²/ε⁴)` `∇h` calls | None: same order | None. The reduction already places all noise in convex `h` while `∇f` is exact. | Same Moreau-gap transfer. | Also requires `ε ≲ √(ℓΔ)` and high dimension. |
| [Zhou–Gu, ICML 2019](https://arxiv.org/abs/1901.11224), Thms 4.5/4.7 specialized to n=1. This covers only linear-span algorithms (special-case baseline). | `Ω(√(ℓL)Δ/ε²)` (linear-span) → `Ω(√(ℓL)Δ/ε²)` (all randomized algorithms) | None in order | Algorithm class: linear-span → arbitrary randomized | Gradient norm → Moreau gap | Needs `ℓ ≤ L`, `2⁶²ε² ≤ ℓΔ`, and high dimension. |

**Standard-reduction check.** Take the known function `f = −(ℓ/2)‖x‖²` and set `h = G + (ℓ/2)‖x‖²`, where `G` is any single-oracle hard function that is at most `ℓ/2`-smooth, or `ℓ`-weakly convex and `(L−ℓ)`-smooth.

- Then `h` is convex and `L`-smooth, and `f + h = G`.
- `∇f` calls reveal nothing, so any `K` is harmless.
- A stochastic `∇G` oracle shifted by `ℓx` is an admissible `∇h` oracle with the same variance. Arjevani's Bernoulli-masked oracle fits the `Bool` sample space.
- A small `Γ` yields a prox point `y` with `∇F(y) = 2ℓ(x̂ − y)` close to `x̂`. Against chain instances with rescaled accuracy, this transfers the gradient-norm failure at constant cost.

So both "two-oracle" `∇h` terms follow from single-oracle lower bounds. The note's instance B uses exactly this device. The masked-frontier coupling (noise only on a convex link) and the Robin-wire chain are new constructions, but the stated bound does not need them. They are proof mechanism, not extra strength. The only ingredient I did not find in refereed form is the `√(ℓL)Δ/ε²` bound for *arbitrary randomized* algorithms. Extending Zhou–Gu's linear-span bound to it with random-rotation methods (Carmon I) is the expected route but not automatic. Carmon et al. II (§6.2) leave some randomized first-order bounds open.

**Search coverage (2026-11-27).**

- Searched arXiv/web for two-oracle, complexity-separation and sliding lower bounds, and for weakly convex/lower-curvature stochastic lower bounds.
- Read the cited theorems in Carmon I/II, Arjevani et al. v2, Zhou–Gu, Han–Xie–Zhang (JMLR 2024, no weakly convex minimization bound found) and Lan–Li–Xu 2412.14291v3 (upper bounds only; about 28% unread).
- Also checked Liu–Lin–Xu 2502.17770, a two-oracle lower bound for affinely constrained problems that is not comparable.
- Could not access or verify Zhang et al. arXiv:2610.00245v2, which the note cites for the randomized `√(ℓL)` term.
- The theorem was introduced in commit `0ef763ac` (2026-11-27).
- The note's own "Relation to prior work" agrees that the single-oracle content is not new. It understates that the two-oracle form reduces to it.

**Conclusion**

**No new hardness beyond known single-oracle lower bounds is established; the two-oracle form is a reduction.** Freezing `f` as a known concave quadratic and moving its curvature into `h` turns any single-oracle hard instance into a two-oracle one where `∇f` calls are useless. So the `∇h` bound is the union of two known bounds: Arjevani et al.'s randomized `ℓΔσ²/ε⁴` and the `√(ℓL)Δ/ε²` weakly convex term. The `∇f` bound is Carmon et al.'s randomized `ℓΔ/ε²` with `h = 0`.

| Oracle | Prior | This theorem |
|---|---|---|
| `∇f` | `Ω(ℓΔ/ε²)` (randomized) | `Ω(ℓΔ/ε²)` |
| `∇h` | `Ω(ℓΔσ²/ε⁴)` (randomized) and `Ω(√(ℓL)Δ/ε²)` (linear-span) | `Ω(ℓΔσ²/ε⁴ + √(ℓL)Δ/ε²)` (randomized) |

The comparison establishes one real but modest gain. The `√(ℓL)Δ/ε²` term now holds for arbitrary randomized algorithms rather than only linear-span ones, under a Moreau-gap criterion. Whether that extension is already in the literature is unresolved, because Zhang et al. 2610.00245 could not be checked. Either way, it is a single-oracle statement the note itself does not claim as new. The value of the claimed Θ characterization comes from the paired upper bound, not this theorem.

What can be claimed is a formal randomized lower bound that certifies tightness of the sliding upper bound, with constructions that differ from but do not strengthen known ones.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
