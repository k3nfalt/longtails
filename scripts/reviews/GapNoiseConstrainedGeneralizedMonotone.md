# GapNoiseConstrainedGeneralizedMonotone: novelty assessment

The [theorem](../../LongTails/Theorems/GapNoiseConstrainedGeneralizedMonotone.lean) shows the following for a constrained VI with a monotone operator `F` that is `(L₀,L₁)`-generalized Lipschitz on the whole space, using exact projection onto `X` and an unbiased IID oracle with gap-dependent variance `E‖g(x)−F(x)‖² ≤ σ² + v⟨F(x)−F(x⋆),x−x⋆⟩` on `X`. The [algorithm's](../../LongTails/Algorithms/GapNoisePastExtragradient.lean) returned point is feasible and satisfies `dist(−F(x), N_X(x)) ≤ ε` with probability `≥ 1−δ` ([setup](../../LongTails/Setups/GapNoiseConstrainedGeneralizedMonotone.lean)).

**Complexity.** The budget is per channel, and the stochastic-operator and projection channels each receive it, so the total is at most twice this:

`O( [ (L₀+L₁G+v)R(1+L₁R)²/ε + (1+L₁R)⁴ + σ²(1+L₁R)/ε² ] · log⁵( e(2 + (L₀+L₁G)R(1+L₁R)²/ε + (1+L₁R)⁴)/δ ) )`

The parameters are:
- `R ≥ ‖x₀−x⋆‖`;
- `G ≥ ‖F(x⋆)‖`;
- `σ` is the additive noise level;
- `v` is the gap-noise coefficient;
- `0<δ<1` is the failure probability.

The constant is `2³⁵⁰`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ji–Lan–Zhu, [arXiv:2609.04188v2](https://arxiv.org/html/2609.04188v2) (v1 3 Sep 2026, preprint, prior), Thm 3.1, eq. (3.13), same noise model (1.12). **Applies only to the case `L₁=0` with `F` `L`-Lipschitz on `X`.** | Expected residual: `Õ(LR/ε + (vR/ε + σ²/ε²)log³(LR/ε))`. Converted to probability `δ` by Markov's inequality: `Õ((L+v)R/(ε√δ) + σ²/(ε²δ))`. → At `L₁=0`: `O(((L₀+v)R/ε + 1 + σ²/ε²)·log⁵((3+L₀R/ε)/δ))` | Confidence dependence improves from `δ^{-1/2}` and `δ^{-1}` to `polylog(1/δ)`. Same order at fixed `δ`, but this result carries `log⁵` rather than `log³`. | None: on the overlap, this class is narrower (see the last column). | A guarantee in expectation becomes a high-probability guarantee under second moments only. The bound does not convert back to an expected residual. | Monotonicity and Lipschitz continuity must hold on all of `E`, not only on `X`, and the result needs `G` once `L₁>0`. I did not verify the paper's own Thm 4.1 high-probability result, which the note says uses exponential tails. |
| Repository [StochasticConstrainedGeneralizedMonotone](../../LongTails/Theorems/StochasticConstrainedGeneralizedMonotone.lean) (commit cc147db, 24 Oct 2026, prior). **Applies only to the case `v=0`.** | `O([(L₀+L₁G)Q²R/ε + Q⁴ + σ²/ε²]·log³·log(·/δ))`, where `Q=1+L₁R` → the same terms, plus `vRQ²/ε`, with `σ²Q/ε²` and `log⁵` | Worse on the overlap: the `σ²` term gains a factor `Q=1+L₁R`, and there are two more logarithms. | Uniform variance `σ²` → `σ² + v·gap`. This covers noise that is unbounded on unbounded `X`. | None | The extra `Q` and the extra logarithms. |

**Covered example.** The companion note's example is `F(x)=Aᵀ((Ax−c)^{⊙3}+d)` on `X={Ax≥c}` with multiplicative noise `Z·AᵀB(u²)`. I checked it:
- `‖DF‖ ≤ 3‖A‖²(1+‖d‖+‖F‖/s_min(A))`;
- the gap equals `Σuᵢ⁴`;
- the noise variance is at most `E[Z²]‖AᵀB‖²Σuᵢ⁴`.

`F` is not Lipschitz on `X`, and the variance is unbounded there. Neither row above therefore applies, while this theorem does.

**Reduction check.** A Grönwall bound on a radius-`O(R)` ball gives a local Lipschitz constant of order `(L₀+L₁G)e^{O(L₁R)}`. Inserting it into Thm 3.1 would keep the inverse-linear `vR/ε` term but add exponential dependence on `L₁R`. That reduction also needs localization or projection onto `X∩ball`, which I did not verify. Absorbing `v·gap` into a uniform variance instead gives a term of order `vL_loc R²/ε²`, which loses the `ε` exponent. So the combination is not an immediate corollary. The new mechanism is the shifted comparison point, which keeps the original-solution gap usable inside regularized stages; I did not audit it beyond reading the statement and the proof outline.

**Proof ancestry.** These pieces are inherited and not credited here:
- accumulative regularization (Ji–Lan–Zhu);
- robust pilots and medoid amplification (also used by Novoselov et al., [arXiv:2610.12641](https://arxiv.org/abs/2610.12641), in a federated strong-growth/gap setting);
- the repository's projected clipped extragradient.

**Search coverage.** Searched on 30 Oct 2026: arXiv 2024–2026; generalized-smooth VIs, including Vankov et al. [2410.12334](https://arxiv.org/abs/2410.12334) (quasi-sharp, almost-sure only); state-dependent noise, including Alacaoglu–Kim [2602.05531](https://arxiv.org/abs/2602.05531) (`Õ(ε⁻⁴)`, weaker) and the expected co-coercivity work of Loizou et al. (NeurIPS 2021). I found no stochastic monotone-VI residual result that combines generalized smoothness with gap noise. Ji–Lan–Zhu's Section 4 and the NeurIPS 2026 papers the note lists were not read in full. The note's citation of Thm 3.1 matches the paper, apart from the omitted `log³` factor. The theorem was introduced on 30 Oct 2026 (commit 9fcb592), after both baselines.

## Conclusion

**This covers new instances by combining two recent relaxations; it does not improve complexity on either one.**

There are two strongest baselines:
- Ji–Lan–Zhu (Sep 2026) for gap noise with a Lipschitz `F`;
- the repository's own finite-variance generalized-smooth theorem (24 Oct 2026).

Each baseline covers only one relaxation, and the selected result specializes to roughly the same bound as each:

| Overlap | Baseline | This result |
|---|---|---|
| `L₁=0` | `Õ((L+v)R/ε + σ²/ε²)` in expectation | same order with high probability, `log⁵((L₀R/ε)/δ)` |
| `v=0` | `Õ((L₀+L₁G)Q²R/ε + Q⁴ + σ²/ε²)` | `σ²` term ×`Q`, two more logs |

Here `Q=1+L₁R`.

The real gain is scope. Operators that grow faster than linearly on an unbounded `X`, with noise proportional to the monotonicity gap (for example noisy cubic feature residuals), now get a polynomial, inverse-linear-in-`ε` bound. The obvious reductions give either `e^{O(L₁R)}` dependence or a `1/ε²` term. Against the Markov-converted Ji–Lan–Zhu bound, this result also has logarithmic rather than polynomial dependence on `1/δ`.

The gain is modest for three concrete reasons:
- it merges two extensions published weeks apart;
- the algorithmic machinery is inherited;
- the overlap costs an extra `Q` on the noise term, and the `Q`-dependence is not known to be optimal.

My literature search found no prior combination, but that does not establish priority, and the stage-drift argument was not independently audited. What can be claimed is a first checked high-probability residual bound that holds under generalized smoothness and gap-dependent noise at the same time.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
