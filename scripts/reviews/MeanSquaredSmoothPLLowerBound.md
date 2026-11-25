# Novelty assessment: MeanSquaredSmoothPLLowerBound

The [theorem](../../LongTails/Theorems/MeanSquaredSmoothPLLowerBound.lean) is a lower bound. On the [high-dimensional setup](../../LongTails/Setups/HighDimensionalMeanSquaredSmoothPL.lean), which restricts the [general setup](../../LongTails/Setups/MeanSquaredSmoothPL.lean), every randomized adaptive algorithm with a free output rule fails `𝔼[f(X)] − f⋆ ≤ ε` at every budget `b ≤ ⌊(κ + s² + min{κs², κ̄s})/2²⁰⁰⌋`. Each query is a same-sample pair `(g(x,ξ), g(y,ξ))`. The objective is `L`-smooth and globally `μ`-PŁ, and the oracle is unbiased with variance at most `σ²` and `L̄`-mean-squared smooth. Algorithms are unrestricted (`allowedAlgorithm` is trivial), and the hard instances come from [the proof modules](../../LongTails/Proofs/MeanSquaredPLLowerBound.lean).

**Proved bound** (`L`: smoothness, `L̄`: mean-squared smoothness, `μ`: PŁ constant, `σ²`: variance, `Δ`: initial gap, `d`: dimension):

  N ≥ Ω( L/μ + σ²/(με) + min{ Lσ²/(μ²ε), L̄σ/(μ^{3/2}√ε) } ) pair queries.

The constant is `2⁻²⁰⁰`. The bound needs `L ≥ 2⁷³μ`, `Δ ≥ 64ε` and `d ≥ (L/μ)⁴(1 + σ²/(με))`. The [companion upper bound](../../LongTails/Theorems/MeanSquaredSmoothPLUpperBound.lean) is `O(κ log(1+Δ/ε) + s² + min{κs², κ̄s})`. The two differ only by `log(Δ/ε)` on the `κ` term. Here `κ = L/μ`, `κ̄ = L̄/μ` and `s = σ/√(με)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yue–Fang–Lin, [arXiv:2212.13551](https://arxiv.org/abs/2212.13551) Thm 3 (COLT 2023), plus the folklore two-point statistical bound `Ω(σ²/(με))` (strongly convex quadratics with additive noise, which lie in this class). These were the prior lower bounds valid on this class. | `Ω(L/μ·log(1/ε) + σ²/(με))` → `Ω(L/μ + σ²/(με) + min{Lσ²/(μ²ε), L̄σ/(μ^{3/2}√ε)})` | Larger necessary budget when `min{κs², κ̄s} ≫ κ log(1/ε) + s²`. With `L̄ ≥ L` this holds whenever `√(με)·log(1/ε) ≪ σ ≪ L̄√(ε/μ)`. Example: `L̄ = L`, `σ² = Lε` gives `κ log(1/ε)+κ` → `κ^{3/2}`. | Yue–Fang–Lin covers deterministic algorithms only → randomized algorithms (for the `κ` term, but without its log) | None | Loses `log(1/ε)` on the noiseless term. Needs `κ ≥ 2⁷³`, `Δ ≥ 64ε` and `d ≥ κ⁴(1+s²)`. Constants are astronomical. |
| Masiha–Kiyavash–Thiran, [arXiv:2606.28278](https://arxiv.org/abs/2606.28278) Thm 4.3 (preprint, v1 26 Jun 2026, v3 11 Aug 2026). Restriction: bounded-variance, single-point oracle that is **not** mean-squared smooth. | `Ω(Lσ²/(μ²ε))` on a larger class (not comparable) → the same term on the smaller class with `L̄`-MSS pair oracle when `L̄ ≥ Lσ/√(με)`; `Ω(L̄σ/(μ^{3/2}√ε))` otherwise | Not comparable as classes. The new bound shows that the `κs²` term survives mean-squared smoothness exactly when `L̄/L ≥ s`, and is replaced by `κ̄s` otherwise. | Arbitrary bounded-variance oracle → mean-squared-smooth same-sample oracle (a smaller class, so hardness is stronger) | None | None beyond row 1's restrictions |
| Bai–Liu–Luo, [arXiv:2402.02569](https://arxiv.org/abs/2402.02569) Cor. 3.6 (preprint, Feb 2024). Restriction: finite sum, linear-span IFO algorithms. | `Ω(n + κ̄√n·log(1/ε))` with exact components; it does not transfer (see below) | Not comparable: no bounded-variance online instance | Finite-sum linear-span → online, all randomized algorithms | None | Has no `σ` parameter |

**Upper-bound baselines.** PAGE ([arXiv:2008.10898](https://arxiv.org/abs/2008.10898), Thm 6/Cor. 7, ICML 2021) gives `O((s² + κ̄s)·log(1/ε))` (roughly, for `s ≥ 1`), and SGD gives `O(κ log + κs²)`. So the `min{κs², κ̄s}` term was already achievable up to logarithms. The selected theorem proves that it is necessary.

**Reduction check.** Simple reductions do not give this bound:
- Bai–Liu–Luo's hard components live on disjoint blocks, so their variance grows like `‖∇f‖²` and is not uniformly bounded by `σ²`. Their class is also linear-span only.
- Masiha et al.'s oracles are not mean-squared smooth. They are discontinuous in `x`, according to the companion note; I did not check this in their proof.
- The rescaling `L = L̄√q` is only a heuristic.

The mechanism adapts Arjevani et al.'s mean-squared-smooth probabilistic chain ([arXiv:1912.02365](https://arxiv.org/abs/1912.02365), Thm 3) to a globally PŁ zero-chain. This is proof ancestry, not a competing bound. The new step is a Lipschitz-masked "secret field", in which only the frontier edge carries noise. This keeps the oracle globally mean-squared smooth through the guard and cut-off regions, and coordinate hiding handles randomized queries. The proof was not rebuilt and no axiom audit was run for this report. I did check that there are no `sorry`, `admit` or `axiom` occurrences in the proof modules.

**Search coverage** (2026-11-24). I searched arXiv and the web for lower bounds on stochastic, PŁ and mean-squared-smooth problems and found no prior cross-term lower bound. I read the theorem lists of Masiha et al. (only partly verbatim; Section 5, cited by the companion note, was not read) and of Bai–Liu–Luo. I also checked the algorithm class of Yue–Fang–Lin and the PL rate of PAGE.
- **Not checked:** the body of Ou–Wang ([arXiv:2609.03990](https://arxiv.org/abs/2609.03990); the PDF and HTML could not be read), PAGER, and OpenReview submissions.
- **Companion-note discrepancy:** the note says Yue–Fang–Lin supplies the missing `log` "on paper". That holds only for deterministic algorithms ("We only focus on deterministic algorithms"). For randomized algorithms the log rests on the unverified Ou–Wang preprint.
- **Chronology:** the theorem was added on 2026-11-24 (commit `3f7c10e3`), so no later work exists.

**Conclusion**

**Yes: the theorem proves that the variance-reduction cross term is necessary, which no checked prior lower bound shows for this class.** For PŁ objectives with a mean-squared-smooth, bounded-variance pair oracle, the strongest applicable prior lower bounds were the deterministic-algorithm bound `κ log(1/ε)` (Yue–Fang–Lin) and the statistical bound `s²`. The new result raises the necessary budget for all randomized algorithms:

  Ω(κ log(1/ε) + s²)  →  Ω(κ + s² + min{κs², κ̄s}).

The gain holds when `log(1/ε) ≪ s ≪ κ̄`. For example, at `L̄ = L` and `σ² = Lε` the bound grows from about `κ` to `κ^{3/2}`. Together with SGD/PAGE-type upper bounds, this determines when variance reduction helps under PŁ (`L̄/L < σ/√(με)`), up to a `log(Δ/ε)` factor on `κ`.

The limitations are real but do not undo the gain. Constants are astronomical (`2⁻²⁰⁰`, `κ ≥ 2⁷³`), and the dimension must be polynomially large. The hard oracle is a general unbiased vector field, not the gradient of sampled losses. The noiseless `log` is not proved for randomized algorithms. The proof combines known chain and probabilistic-zero-chain tools, but adding the masked field to keep global mean-squared smoothness is a genuine extra step.

The comparison proves a strictly larger necessary budget than the checked prior lower bounds. Priority rests on searches that could not read Ou–Wang's body or OpenReview submissions. The contribution that can be claimed is the first verified lower bound showing that the `min{κs², κ̄s}` term is necessary for stochastic PŁ optimization under mean-squared smoothness.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
