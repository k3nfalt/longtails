# Novelty assessment: StochasticSmoothBanachFixedPoint

The [theorem](../../LongTails/Theorems/StochasticSmoothBanachFixedPoint.lean) covers a nonexpansive map `T : E → E` on a finite-dimensional space whose squared norm is `C`-smooth (`‖x+y‖² ≤ ‖x‖² + 2J(x)[y] + C‖y‖²`, `C ≥ 1`). The map has a fixed point within `R` of `x₀`, and its IID oracle is unbiased with variance `σ²` in the same norm everywhere. Under these assumptions, the theorem proves that the last point `Z` of the recursive-anchoring stochastic Picard method in [setup](../../LongTails/Setups/StochasticSmoothBanachFixedPoint.lean) and [algorithm](../../LongTails/Algorithms/SmoothBanachAnchoring.lean) satisfies `∫‖T(Z) − Z‖² dP ≤ ε²`.

**Complexity.** The number of oracle calls is

  N = O( (1 + R/ε + Cσ²/ε²) · (1 + log(1 + R/ε))⁴ ),

which follows from the exact budget `⌈2²⁰(1 + R/ε + Cσ²/ε²)(1 + log(1 + 16R/ε))⁴⌉`. Here `R` is the initial distance bound, `σ` is the oracle standard deviation, `ε` is the root-mean-square (RMS) residual target, and `C` is the smoothness constant of the squared norm. For finite `ℓ_p` with `2 ≤ p < ∞`, `C = p − 1`. The updates use `R`, `C`, `σ` and `ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lee, [arXiv:2610.26484v1](https://arxiv.org/abs/2610.26484v1) (19 Oct 2026, preprint), Thm 3. Prior; direct competitor on whole-space `ℓ_p`, using E‖residual‖ | `O(R/ε + (p−1)Rσ²/ε³)` → `O((1 + R/ε + (p−1)σ²/ε²) log⁴(2 + R/ε))` | The accuracy exponent of the noise term drops from 3 to 2, a speedup of order `(R/ε)/log⁴`. This holds when `R/ε ≫ log⁴(2+R/ε)` and `(p−1)σ²/ε² ≫ log⁴(2+R/ε)` | None for `2 ≤ p < ∞` | RMS bound, which implies E‖residual‖ ≤ ε | Does not cover `1 < p < 2` or `p = ∞`, which Lee covers. When `σ ≲ ε` it is worse by a `log⁴` factor |
| Diakonikolas–Guzmán–Martínez-Rubio, [arXiv:2609.09524v1](https://arxiv.org/abs/2609.09524v1) (8 Sep 2026, preprint), Thm 5 / Cor 6. Prior; covers only a compact `X` with `T(X) ⊆ X` and a retraction | Domain diameter `D ≥ R`, high probability: `Õ((D/ε + (p−1)Dσ²/ε³) log(1/δ))` → `Õ(D/ε + (p−1)σ²/ε²)` in RMS | On the overlap, at constant δ, the noise term drops by a factor of `D/ε`, up to logarithms | Incomparable: the selected result needs no invariant compact domain, but it requires `T` to be defined on the whole space | None | Gives only an RMS bound. Markov's inequality yields `Õ(D/(ε√δ) + Cσ²/(δε²))`, so polynomial δ-dependence replaces `log(1/δ)`. Does not cover `ℓ∞` or type-2 norms that are not 2-smooth |
| Diakonikolas, [arXiv:2607.09097](https://arxiv.org/abs/2607.09097) (10 Jul 2026, preprint), Cor 1 (Sec 4.3) and Cor 3 (Sec 4.5). Prior; whole space with a quadratically smoothable norm | Variance-only oracle: `Õ(ε⁻⁵)`. Samplewise-nonexpansive oracle: `Õ(ε⁻²)`. Both hide factors in `κ` and `‖x⋆−x₀‖+σ` → `Õ(R/ε + Cσ²/ε²)` | Under variance only, `ε⁻⁵ → ε⁻²`. Under samplewise nonexpansiveness the ε-exponent is the same; the parameter factors were not compared | Removes the requirement that every sampled map `τ(·;ξ)` be nonexpansive or Lipschitz in expectation; bounded variance alone suffices | None claimed | That paper's results are high-probability and anytime. They also allow equivalent smoothable norms (`κ = BC²`), which include `ℓ∞`; the selected result requires the native norm itself to be smooth |
| Chen–Luo, [RAIN, JMLR 25(387), 2024](https://jmlr.org/papers/volume25/22-1126/22-1126.pdf), Thm 4.2 and its monotone-VI remark. Special case: Hilbert spaces only (`C = 1`, `I − T` monotone and 2-Lipschitz) | `O(R/ε · log log + σ²/ε² · log³(R/ε))` → same order | None: same order | None | None (both are in-expectation) | None beyond extra log factors |

**Reductions and proof ancestry.** I looked for a reduction from earlier results and did not find a complete one:

- Norm equivalence to `ℓ₂` fails because `ℓ_p`-nonexpansiveness does not transfer; the note's `tanh` example shows this.
- A single regularization `(1−a)T + a x₀` combined with smooth-norm stochastic approximation (SA) costs `Cσ²R²/ε⁴`.
- Minibatching inside recursive anchoring, as in Diakonikolas–Guzmán–Martínez-Rubio, gives the `ε⁻³` term.

The new step is to solve each anchored contraction with single-sample SA in the smooth norm, rather than with median-of-means batches. This costs `Õ(1/a + Cσ²/(a r)²)` per stage, and the proof controls random warm starts within the anchor recursion. The proof ancestry is Allen-Zhu's recursive regularization and the recursive anchoring of RAIN and DGM, together with classical 2-smooth noise cancellation (Ben-Tal–Margalit–Nemirovski 2001). Those sources supply the ingredients but not this composite bound.

**Search coverage.** I searched on 26 Oct 2026 across arXiv, JMLR and Math. Programming, covering stochastic Halpern and Krasnoselskii–Mann iterations in normed spaces (Bravo–Contreras [2403.12338](https://arxiv.org/abs/2403.12338): `Õ(ε⁻⁵)`; their `Ω(ε⁻³)` lower bound, Thm 3.7, is for `ℓ₁`), plus Shehu [2610.00295](https://arxiv.org/abs/2610.00295) (`ε⁻⁴` in 2-smooth spaces). Several limits apply:

- I read Diakonikolas 2607.09097 and Shehu only through partial HTML extracts.
- The theorem was introduced in commit `3387725` (26 Oct 2026). All compared papers are prior preprints from the preceding few months, so concurrent work is plausible.
- The companion note omits Diakonikolas 2607.09097, which already obtains `ε⁻²` in smooth Banach spaces under samplewise nonexpansiveness. The note's "beyond Hilbert" framing therefore holds only for oracles with bounded variance alone.
- I did not run the build or the axiom checks.

## Conclusion

**Yes: for finite `ℓ_p` with `p > 2` (more generally, 2-smooth norms), the proved total complexity is better than every checked prior bound under bounded-variance oracles.** The strongest direct competitor is Lee's stochastic dual Halpern method:

| | Oracle calls for a residual of ε |
|---|---|
| Lee (2026), Thm 3 | `O(R/ε + (p−1)Rσ²/ε³)` |
| This theorem | `O((1 + R/ε + (p−1)σ²/ε²) · log⁴(2 + R/ε))` |

The gain is a factor of about `R/ε` (up to `log⁴`) when both `R/ε` and `(p−1)σ²/ε²` exceed `log⁴(2+R/ε)`. The new bound loses by `log⁴` when the noise is negligible. It also gives up the `ℓ∞` and `p < 2` cases, and the high-probability guarantees with `log(1/δ)` of Diakonikolas–Guzmán–Martínez-Rubio. Diakonikolas (Jul 2026) already reached `ε⁻²` in smooth Banach spaces, but only when every sampled map is nonexpansive; this result needs bounded variance alone. In Hilbert space it only matches RAIN.

The comparison establishes this gain over the checked bounds. The literature search supports, but cannot guarantee, priority: the competing preprints appeared within weeks of this result in a very active area, and three recent papers treat `ε⁻³` as the best known rate for finite `p` or `ℓ∞`. The ingredients are familiar, but I found no published composition that yields this bound.

What can be claimed is the first checked `Õ(R/ε + Cσ²/ε²)` RMS fixed-point residual bound for nonexpansive maps in 2-smooth non-Hilbert norms using only bounded-variance oracles.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
