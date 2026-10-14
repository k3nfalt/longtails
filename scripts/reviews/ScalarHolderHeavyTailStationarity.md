# Novelty assessment: ScalarHolderHeavyTailStationarity

The [theorem](../../LongTails/Theorems/ScalarHolderHeavyTailStationarity.lean) proves that, for any differentiable, lower-bounded `f : ℝ → ℝ` with `ν`-Hölder derivative and an IID unbiased scalar gradient oracle with central `p`-th moment `≤ σ^p`, the randomized [search algorithm](../../LongTails/Algorithms/ScalarHolderSearch.lean) returns `X` with `Pr(|f'(X)| > ε) ≤ 1/3` using a deterministic number of oracle calls ([setup](../../LongTails/Setups/ScalarHolderStochastic.lean)).

**Proved budget.** The parameters are `H` (Hölder constant), `ν ∈ (0,1]`, `Δ ≥ f(x₀) − inf f`, `σ ≥ 0`, `p ∈ (1,2]`, and the target `ε > 0`. All are known to the algorithm. The proved budget is

  N = O_{ν,p}( 1 + H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε + (σ/ε)^{p/(p−1)} · log(2 + H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε) ),

with the explicit hidden factor `2^{200/(p−1)}(1+1/ν)`, which is at least `2^{200}`. Below, `A := H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε` and `Q := (σ/ε)^{p/(p−1)}` are shorthand only.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Chewi–Bubeck–Salim, [ALT 2023, Thm 3](https://proceedings.mlr.press/v201/chewi23a/chewi23a.pdf) (special case: exact gradients, ν=1) | `O(1+√(HΔ)/ε)` → `O(1+√(HΔ)/ε)` at σ=0, ν=1 | None: same order (optimal by their Thm 2) | exact derivative → unbiased oracle with p-th central moment, p∈(1,2]; L-smooth → ν-Hölder | None (both give a constant-probability point) | Constant factor ≥ 2^200 |
| Liu, [ALT 2026 full version, Thm 17 / Cor. 11](https://optimization-online.org/wp-content/uploads/2025/08/Online-Convex-Optimization-with-Heavy-Tails.pdf) (any d; specialized to d=1) | leading term `(H^{1/ν}Δ/ε^{1+1/ν})·(σ/ε)^{p/(p−1)}` → `1 + H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε + (σ/ε)^{p/(p−1)} log(2+H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε)` | Polynomial: speedup ≥ ⅓·min(A^{1/ν}Q, A^{1+1/ν}/log(2+A)) when σ ≥ ε and A ≥ 1 (other additive terms of Cor. 11 were only partly legible in the PDF text). For example, at ν=1, p=2: `HΔσ²/ε⁴` → `√(HΔ)/ε + (σ²/ε²)log(2+√(HΔ)/ε)` | None (same objective and noise class at d=1) | None: Liu bounds the expected gradient norm of a randomly chosen block average, and Markov's inequality converts this to the same Pr ≤ 1/3 criterion | Dimension one only; Liu covers every d, and his Cor. 12 runs without knowing (H,Δ,σ,p); this result needs all parameters |
| Derived routine composition (not published): random probing at dyadic accuracy scales with clipped estimation, then bisection with a union bound over O(log A) midpoint tests | `O(1 + A + Q log(2+A) log log(3+A))` → `O(1 + A + Q log(2+A))` | Factor `log log(3+A)`, only when `Q log(2+A) ≳ A`, e.g., fixed H,Δ,σ,p,ν and ε→0; none when `A ≳ Q log(2+A) log log(3+A)` | None | None | Same algorithmic information; same constant blow-up |

**Lower bound.** At ν=1, p=2 the result is order-optimal once A exceeds a universal constant (Chewi–Bubeck–Salim's Thm 2 requires normalized ε < 1/8) and ε < σ/2. In that regime, Foster et al., [COLT 2019, Appendix C, Thm 11](https://proceedings.mlr.press/v99/foster19b/foster19b.pdf), give `Ω((σ²/ε²) log(HΔ/ε²))` for 1-D convex instances. Chewi–Bubeck–Salim's Thm 2 gives the randomized `Ω(√(HΔ)/ε)`. I did not verify a lower bound for ν<1 or p<2.

**Standard reductions.** No reduction reaches the full bound. The published general-dimension methods pay a product `A^{1+1/ν}·Q`. Several ingredients come from known work: Chewi–Bubeck–Salim's random search plus bisection (proof ancestry), robust or clipped mean estimation, and probing at geometric accuracy scales. Probing at each scale `j` with `~2^j` probes needs only a sum-over-levels hitting argument. Combined, these give the routine composition in row 3. Only the `log log` factor needs the new ingredient: an occupation/charging argument for a backtracking noisy search over brackets with arbitrary sign changes. It descends Feige–Raghavan–Peleg–Upfal and [Karp–Kleinberg](https://www.cs.cornell.edu/~rdk/papers/karpr2.pdf) noisy search, which require ordered or monotone targets.

**Search coverage and chronology.** I searched on 2026-10-07: arXiv, PMLR (COLT/ALT), Optimization Online, and noisy-search, probabilistic-bisection, and heavy-tail nonconvex SGD literature. I found no published 1-D nonconvex stochastic stationarity upper bound with an additive `A + Q·polylog` form.
- **Introduction date.** Git places the result's introduction at 2026-09-29 (commit 8468457).
- **Ou–Wang.** [arXiv:2609.03990](https://arxiv.org/abs/2609.03990) (v1 2026-09-03, prior) has a 1-D robust bisection for PL objectives only, so it needs a monotone derivative order. The companion note derives a ν=1 comparator from their d≥2 trapping argument (Lemmas D.11–D.12). I confirmed those lemmas exist but did not verify that derived bound; it is weaker than row 3 anyway.
- **Zhou–Sugiyama–Suzuki.** [arXiv:2610.02791](https://arxiv.org/abs/2610.02791) (2026-10-02, subsequent) is deterministic and noiseless, so it does not compete.
- **Companion note.** Its citations and its own concession that the gain over the routine baseline is `log log` agree with what I checked.

## Conclusion

**Against published guarantees the gain is polynomial, but against a routine composition it is only a `log log` factor.**

The strongest published end-to-end guarantee covering this class is Liu's heavy-tailed Hölder method, in any dimension. Specialized to one dimension, it costs `(H^{1/ν}Δ/ε^{1+1/ν})(σ/ε)^{p/(p−1)}`; here the deterministic and statistical costs add instead of multiplying:

  `1 + H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε + (σ/ε)^{p/(p−1)} log(2 + H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε)`.

For smooth, finite-variance problems (ν=1, p=2), this matches the known lower bounds of Chewi–Bubeck–Salim and Foster et al. up to constants. So it pins down the 1-D smooth stochastic complexity.

However, most of that gain does not need a new idea. Known tools — random search, dyadic-scale probing, robust mean estimation, and bisection with a union bound — already give the same bound times `log log(H^{1/(1+ν)}Δ^{ν/(1+ν)}/ε)`. The genuinely new piece removes that factor, and only when the noise term dominates. The constants (≥ 2^200) are purely asymptotic.

What can be claimed is a dimension-one, known-parameter upper bound that is order-optimal for ν=1, p=2. Relative to a straightforward composition, its contribution is the removal of one iterated logarithm through an arbitrary-sign noisy backtracking analysis. I found no prior paper stating it, but a failed search does not establish priority.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
