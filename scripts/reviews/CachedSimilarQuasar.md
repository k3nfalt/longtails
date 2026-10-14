# CachedSimilarQuasar: novelty assessment

[`result`](../../LongTails/Theorems/CachedSimilarQuasar.lean) ([setup](../../LongTails/Setups/SimilarFiniteSumQuasar.lean), [algorithm](../../LongTails/Algorithms/CachedQuasarOracle.lean), [iteration](../../LongTails/Algorithms/CachedQuasar.lean)) proves a pathwise objective-gap bound `F(x̂) − F* ≤ ε` for the final `x`-iterate. Here `F = (1/n)Σfᵢ`, and the method is deterministic. It runs S epochs; each epoch takes one full gradient at an anchor `w`, then m fixed-parameter Nesterov steps (step `1/L`, `θ = √(μ/L)`) using the estimator `∇f₀(y) − ∇f₀(w) + ∇F(w)`.

**Hypotheses** (Hilbert space; exact component-gradient oracle; no function values):
- ∇F is L-Lipschitz.
- F is (γ,μ)-strongly quasar-convex around a global minimizer x*.
- F has lower curvature ≥ −γ√(μL).
- Every `∇fᵢ − ∇F` is δ-Lipschitz, and `384δ² ≤ γ³μ²`.
- `F(x₀) − F* ≤ Δ`.

The quadratic-growth hypothesis is implied by strong quasar-convexity. Tuning uses L, μ, γ, δ, Δ and ε.

**Complexity** (component-gradient calls). The exact budget `(n+m)·S` gives

`N = O( n + n·log(2+Δ/(γε)) / log(γ³μ²/(192δ²)) + γ⁻¹√(L/μ)·log(2+Δ/(γε)) )`.

The middle term is 0 when δ = 0, and N = 0 when Δ = 0. Here n is the number of components, L is the smoothness of F, μ and γ are the strong-quasar parameters, δ is the similarity constant, Δ is the initial gap and ε is the accuracy. The bound uses `2r ≤ 3/8`, so `m·S = O(γ⁻¹√(L/μ)·log(2+Δ/(γε)))`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hermant–Aujol–Dossal–Rondepierre, [arXiv:2405.19809](https://arxiv.org/abs/2405.19809) Thm 2 (preprint; v1 May 2024, v3 May 2026), run with full gradients | `n·γ⁻¹√(L/μ)·log(2Δ/(γε))`, from contraction `1−γ√(μ/L)`, bound `(2/γ)Δ` and n calls per gradient → N | Multiplicative `n·γ⁻¹√(L/μ)` → additive. Speedup ≈ `min(n, γ⁻¹√(L/μ)·log(γ³μ²/δ²))`, a gain whenever n ≥ 2 and `384δ² ≤ γ³μ²` | None: same F class, including the same curvature condition `ρ ≥ −γ√(μL)` | None: both are deterministic, last-iterate and use the same known parameters | Requires finite-sum structure with uniform similarity `δ ≤ γ^{3/2}μ/19.6`, plus knowledge of δ |
| Kovalev et al., [NeurIPS 2022](https://arxiv.org/abs/2205.15136) Thm 3 (Accelerated Extragradient sliding). **Overlap only:** γ = 1 and F μ-strongly convex. Uses `q = f₀` (convex since δ < μ), `p = F − f₀`, with `L_p := μ` | `(n + √(L/μ))·log(LΔ/(με))`, converting through `‖x−x*‖² ≤ 2ε/L` → `n + n·log(Δ/ε)/log(μ²/δ²) + √(L/μ)·log(Δ/ε)` | Log factors only: the n-term shrinks by `log(μ²/δ²)` when δ ≪ μ, and `log(L/μ)` leaves the logarithm | Strongly convex F → strongly quasar-convex F with curvature ≥ −√(μL); nonconvex F is covered. Also allows γ < 1 | None | Covers only `δ ≤ μ/19.6`. The baseline also handles `μ ≤ δ ≤ L` with `√(δ/μ)` rounds, so the overall classes are incomparable |
| Hinder–Sidford–Sohoni, [COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html) (strongly quasar-convex acceleration), run with full gradients | `n·γ⁻¹√(L/μ)·log(L/(γμ))·log(Δ/(γε))` function+gradient evaluations → N | Removes the n factor and the binary-search log on the subclass below; Hermant already removes that log | None: HSS needs no curvature bound, so the current class is narrower | None | Not comparable on HSS's full class. HSS needs a function-value oracle; this result does not |

**Reduction check.** At δ = 0, `∇F = ∇f₀ + const`, so Hermant's Thm 2 alone gives the bound. For δ > 0 there is no direct substitution: the shifted surrogate `f₀ − ⟨∇f₀(w)−∇F(w),·⟩` need not be quasar-convex. Instead, the proof adds two steps to Hermant's Lyapunov energy:
- an inexact-gradient perturbation, charged `3θ/(γμ)‖e‖²`;
- an SVRG/DANE-style anchor error `‖e‖ ≤ δ‖y−w‖`, controlled through quadratic growth.

Together these give epoch contraction `O(δ²/(γ³μ²))` in energy. This is the same mechanism behind DANE's quadratic-only contraction ([Shamir–Srebro–Zhang 2014](https://arxiv.org/abs/1312.7853), Thm 2 and Lemma 1). Each step is standard; I found no prior composition for a nonconvex class. Proof ancestry: Hermant (energy and parameters) and [Johnson–Zhang 2013](https://papers.nips.cc/paper/2013/hash/ac1dd209cbcc5e5d1c6e28598e8cbbe8-Abstract.html) (anchor correction).

**Search coverage.** Searched on 2026-10-07 across arXiv, PMLR, NeurIPS and ICLR. Topics: strongly quasar-convex acceleration, similarity/sliding/DANE (including [Jiang–Rodomanov–Stich, ICML 2024](https://arxiv.org/abs/2404.08447), whose strongly convex theorems need convex components and n local solves), and quasar-convex variance reduction. I read theorem statements in the Hermant, Kovalev, DANE and Jiang et al. PDFs. HSS's exact log factor was taken from Hermant's discussion (§3), not re-read. The search of 2025–2026 federated preprints was not exhaustive.

There is no companion note. Git introduces the result on 2026-09-24 (`f4295c4`), after Hermant v3. The later repository results [ContinuizedSimilarQuasar](../../LongTails/Theorems/ContinuizedSimilarQuasar.lean) (2026-09-25) and [MovementSimilarQuasar](../../LongTails/Theorems/MovementSimilarQuasar.lean) (2026-09-28) relax the similarity regime but give expected-gap guarantees instead of pathwise ones.

**Conclusion**

**Yes, but narrowly: for nonconvex quasar-convex finite sums it cuts the full-gradient cost, and only when the components are nearly identical.** The strongest same-class baseline is Hermant et al.'s fixed-parameter Nesterov method run with full gradients:

| | component-gradient calls |
|---|---|
| Hermant Thm 2 (full gradients) | `n·γ⁻¹√(L/μ)·log(Δ/(γε))` |
| This result | `n·[1 + log(Δ/(γε))/log(γ³μ²/δ²)] + γ⁻¹√(L/μ)·log(Δ/(γε))` |

This gain is real, roughly a factor `min(n, γ⁻¹√(L/μ))`, but it holds only when `δ ≤ γ^{3/2}μ/19.6`. On the strongly convex overlap, Kovalev et al.'s sliding already achieves `(n+√(L/μ))·log`, so the only gain there is a `log(μ/δ)` factor.

What is established is a verified complexity comparison, not historical priority. No earlier paper I found combines similarity-based gradient caching with quasar-convex acceleration. Still, the mechanism is a short composition of Hermant's energy argument, a standard inexact-gradient perturbation and an SVRG/DANE anchor correction. The similarity requirement is far stronger than the `δ ≥ μ` regime that motivates the similarity literature.

The claimable contribution is an end-to-end deterministic, last-iterate guarantee showing that fixed-component caching removes the multiplicative n from accelerated strongly quasar-convex optimization when the components are very similar. It is not a new acceleration analysis or a broadly useful similarity regime.

**Verdict: LIMITED OR INCREMENTAL NOVELTY** — **Confidence: medium**
