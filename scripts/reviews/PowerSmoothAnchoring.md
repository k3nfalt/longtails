# PowerSmoothAnchoring: novelty assessment

[`result`](../../LongTails/Theorems/PowerSmoothAnchoring.lean) proves the following. Let `E` be a separable real Banach space that satisfies Xu's power-smooth inequality `‖x+y‖^s ≤ ‖x‖^s + s·j(x)y + K‖y‖^s`, with `1 < s ≤ 2` and `K ≥ 1`. Let `T` be nonexpansive on all of `E`, with a fixed point within distance `D` of `x₀`. Assume the IID oracle is unbiased and its `s`-th moment satisfies `E‖G(x,ξ)−Tx‖^s ≤ σ^s` ([setup](../../LongTails/Setups/StochasticPowerSmoothFixedPoint.lean)). Under these assumptions, recursive anchoring with single-sample stochastic KM stages ([algorithm](../../LongTails/Algorithms/PowerSmoothAnchoring.lean)) returns its last-stage point `x̂`, which satisfies `E‖x̂−Tx̂‖ ≤ ε`.

**Proved complexity.** The bound below comes from the public budget. Universal constants are suppressed; the factor `2^{16/(s−1)}` is not universal, so it is kept:

  **N = O( (1 + D/ε + (2¹⁶K)^{1/(s−1)}·(σ/ε)^{s/(s−1)}) · (3 + log₂(1+16D/ε))^{2+s/(s−1)} ).**

It holds for every `D, ε > 0` and `σ ≥ 0`. Throughout, `q = p/(p−1)`. For finite-dimensional `ℓ_p` with `1 < p ≤ 2`, the repository certifies `s = p` and `K = 4` ([`lp_power_smooth`](../../LongTails/Proofs/PowerSmoothLpGeometry.lean)).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lee, [arXiv:2610.26484v1](https://arxiv.org/abs/2610.26484) (19 Oct 2026, preprint), Thm 3, with `1<p<2` and `κ` replaced by its bound `D`. Prior direct competitor: whole-space `ℓ_p^d`, second-moment noise, E‖residual‖ | `O(D/ε + Dσ^q/ε^{2q−1})` → `O((1 + D/ε + 2^{16(q−1)}(σ/ε)^q)·log^{2+q}(2+D/ε))`. A second moment `σ²` implies the `p`-th moment bound with the same σ | Noise term loses its factor `D/ε`, so `ε^{−(2q−1)} → ε^{−q}` up to logs. Example: `p = 3/2`, `D = σ = 1` gives `ε⁻⁴ → ε⁻³log⁵(1/ε)`. The gain needs `min(D/ε, (σ/ε)^q) ≫ log^{2+q}(2+D/ε)` | `ℓ_p^d` → any `s`-power-smooth Banach space, including infinite-dimensional `L_p` (`p<2`) and Hilbert space. Second moment → `s`-th moment only | None: both give the expected last-iterate residual with known parameters | When `σ ≲ ε`, worse by a factor `log^{2+q}`. The constant `2^{16(q−1)}` is much larger than Lee's `(8(q+1)C_p)^q`. Excludes `p = ∞`, which Lee covers |
| Diakonikolas–Guzmán–Martínez-Rubio, [arXiv:2609.09524v1](https://arxiv.org/abs/2609.09524) (8 Sep 2026, preprint), Thm 5 / Cor 6. Prior. Applies only to a self-map of a bounded domain with a retraction | Unit `ℓ_p` ball, high probability: `Õ((σ log(1/ε))^q/ε^{2q−1} + (1/ε)log(1/δ))` → on whole-space maps that leave the ball invariant, `Õ(1/ε + (σ/ε)^q)` in expectation | The noise term improves by a factor `1/ε`, up to logs, when the comparison uses a constant failure probability δ | Incomparable classes: the selected result needs no invariant bounded domain, but it requires `T` to be nonexpansive on all of `E` | None. Markov's inequality turns this result into a high-probability bound with `1/δ` instead of `log(1/δ)` | Expectation only; noise measured in the native norm. DGM covers every weak type-`q` norm, including `ℓ∞` |
| Repository [RecursiveAnchorKmSmoothBanach](../../LongTails/Theorems/RecursiveAnchorKmSmoothBanach.lean), the `s = 2` case | `O((1+D/ε)log + Kσ²log³/ε²)` → at `s = 2`, `O((1+D/ε+2¹⁶Kσ²/ε²)log⁴)` | Worse at `s = 2`, by a log factor | `2`-smooth → `s`-smooth with `s < 2`; second moment → `s`-th moment | None | This is an extension within the repository |

**Reduction and mechanism.** The `ℓ₂` norm and the `q = log d` smoothing norm are equivalent to `ℓ_p` only up to factors depending on `d`. Even then, `ℓ_p`-nonexpansiveness does not transfer to the other norm. Both minibatched competitors pay `D/ε` epochs times `(σ/ε)^q` samples. The new step adapts the `s = 2` sibling's argument. It runs single-sample SA on each anchored `1/(1+a)`-contraction and tracks the `s`-th power error `a^s·E‖x−u‖^s`. That error contracts by `1−δ` and has a noise floor `Kδ^{s−1}σ^s` that does not depend on `a`.

**Proof ancestry, not baselines.** Allen-Zhu's recursive regularization supplies the doubling-anchor schedule, as do the anchoring schemes of RAIN and DGM. Xu's 1991 inequality supplies the power-smoothness step. Neither yields this bound without the stage analysis above. The checked 2026 preprints all work by minibatching or median-of-means.

**Search coverage.** The search ran on 3 Nov 2026 and covered arXiv and the web. It included stochastic KM and Halpern methods, anchoring, smooth Banach spaces and heavy-tailed noise. I read the full theorem statements of DGM's Thm 5 and Cor 6, and the statement of Lee's Thm 3 as extracted from the HTML. For Shehu [2610.00295](https://arxiv.org/abs/2610.00295) (`2`-smooth only), Diakonikolas [2607.09097](https://arxiv.org/abs/2607.09097) (smoothable norms with `p ≥ 2`; its §4.5 was not read), Yang et al. [2609.28543](https://arxiv.org/abs/2609.28543) (Hilbert space) and Bregman SKM [2506.08031](https://arxiv.org/abs/2506.08031) (no complexity extracted), I used abstracts or partial text. I did not check Hilbert-space baselines for heavy-tailed noise, such as clipped VI methods.

The theorem was introduced in commit `6b8c1c5` today, 3 Nov 2026. Every baseline is a 2026 preprint, so concurrent work is plausible. The companion note's rates for Lee and DGM agree with the sources. I ran no build or axiom check.

## Conclusion

**Yes: for `ℓ_p` with `1 < p < 2`, the proved total complexity beats every checked prior bound once the noise term matters.** The strongest direct competitor is Lee's minibatched dual Halpern method, compared on the same whole-space model with the same expected-residual criterion:

| | Oracle calls (`q = p/(p−1)`) |
|---|---|
| Lee (2026), Thm 3 | `O(D/ε + D·σ^q/ε^{2q−1})` |
| This theorem | `O((1 + D/ε + 2^{16(q−1)}(σ/ε)^q)·log^{2+q}(2+D/ε))` |

The gain is a factor of about `min(D/ε, (σ/ε)^q)/log^{2+q}`, which is large when both quantities exceed `log^{2+q}(2+D/ε)`. For example, at `p = 3/2` with `D = σ = 1` the count drops from `ε⁻⁴` to `ε⁻³` up to logs. The result loses a `log^{2+q}` factor when `σ ≲ ε`, and its constants grow quickly as `p → 1`. It gives up `ℓ∞` and DGM's high-probability bounds with `log(1/δ)`.

The scope also widens: any `s`-smooth space qualifies, and only an `s`-th noise moment is needed. The comparison establishes the gain. Priority is supported only by a search of very recent preprints.

What can be claimed: the first checked additive `Õ(D/ε + (σ/ε)^{p/(p−1)})` expected-residual bound for stochastic nonexpansive fixed points in `p`-smooth spaces with `p < 2`. It extends the repository's `2`-smooth result by the same mechanism.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
