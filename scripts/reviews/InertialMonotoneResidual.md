# Novelty assessment: InertialMonotoneResidual

The [theorem](../../LongTails/Theorems/InertialMonotoneResidual.lean) proves that, for a finite-dimensional monotone, globally `L`-Lipschitz mean operator `F` with a root within distance `R` of `x₀`, IID fresh-sample unbiased oracles with variance `≤ σ²` ([setup](../../LongTails/Setups/StochasticLipschitzMonotone.lean)), the batched inertial regularized extragradient method ([algorithm](../../LongTails/Algorithms/InertialRegularizedExtragradient.lean)) returns a last iterate `z_N` with `E‖F(z_N)‖² ≤ ε²`.

**Complexity** (from `budget`, all raw oracle calls counted, including batches and padding):

  O( 1 + LR/ε + (σ²/ε²) · log²(2 + LR/ε) ),  with L > 0, R ≥ 0, σ ≥ 0, ε > 0.

Here `L` is the Lipschitz constant of the mean operator only (sample maps may be discontinuous), `R` bounds the initial distance to a root, `σ²` bounds the oracle variance and `ε` is the RMS residual target. The parameters `L,R,σ,ε` are used both for tuning and for the stopping horizon.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Lee–Kim RRSEG, [arXiv:2609.35631v1](https://arxiv.org/html/2609.35631v1), Thm 6.1/Cor 6.2 (preprint, 28 Sep 2026; prior) | `E‖F‖² = O(L²R²/T² + σ² log³T/T)` gives `O(1 + LR/ε + (σ²/ε²) log³(2 + LR/ε + σ/ε))` → `O(1 + LR/ε + (σ²/ε²) log²(2 + LR/ε))` | Saves at least a factor `log(2+LR/ε)` when `(σ²/ε²) log²(2+LR/ε) ≥ LR/ε`. Otherwise same order | None: both need only mean monotonicity and Lipschitz continuity, with fresh samples | None (both bound E‖F‖² at a terminal point) | RRSEG covers composite inclusions `F + A` and makes two queries per update. This result uses growing batches and a finite horizon |
| Ji–Lan–Zhu accumulative regularization, [arXiv:2609.04188v2](https://arxiv.org/html/2609.04188v2), §2.3 Thm 2.2 (preprint v2, 17 Sep 2026; prior) | `Õ(LR/ε + (σ²/ε²) log³(LR/ε))`, with `(log log)²` hidden and requiring `ε ≤ LR` → this result | Saves `log(LR/ε)·(log log(LR/ε))²` on the statistical term | None on the unconstrained overlap | None | Their result covers constrained VIs (Thm 2.2) and state-dependent noise (Thm 3.1). This result does not |
| Yoon–Loizou S-Dual-OHM, [arXiv:2609.36033v1](https://arxiv.org/html/2609.36033v1), Cor 3.6 (preprint, 28 Sep 2026; prior) | `O((1+LR/ε) log(1+LR/ε) + (σ²/ε²) log²(1+LR/ε))` → this result | Saves `log(1+LR/ε)` on the deterministic term, which matters when `σ² ≲ εLR/log(2+LR/ε)`. Same statistical order | Every sample map monotone and uniformly `L`-Lipschitz → only the mean operator has these properties (nested, strictly larger class) | None | Same-sample multi-point queries are no longer needed (an oracle relaxation). Yoon–Loizou also use batches |

**Reductions and mechanism.** I found no way to obtain the bound by batching the log³ methods, since batching keeps their logarithm. Yoon–Loizou's resolvent inner loops reuse one sample, so they need samplewise monotonicity, and I did not verify a fresh-sample replacement with only `log²` overhead. The energy/root-transport algebra comes from the stochastic inertial KM analysis of [Yang et al., arXiv:2609.28543v1](https://arxiv.org/abs/2609.28543) (22 Sep 2026), which handles nonexpansive maps, i.e. cocoercive `F`. The new ingredient is an affine-corrected, fresh-batch extragradient step that satisfies that energy inequality without cocoercivity. On cocoercive operators, Yang et al. and Yoon–Loizou's §2.2 bound (reported in 2609.36033) already reach order `LR/ε + (σ²/ε²) log²`, and I checked only the abstract for the former. **Lower bounds:** [Lee–Kim Thm 5.1](https://arxiv.org/html/2609.35631v1) shows that a log-free `O(LR/ε + σ²/ε²)` is impossible: with `L=3`, `R=1`, `σ=1/M` and `ε=1/(16M²)` (squared target `1/(256M⁴)`), it requires `Ω(M² log M) = Ω((σ²/ε²) log(LR/ε))` calls. So one logarithmic factor remains between this result and the known lower bound. The deterministic `Ω(LR/ε)` comes from [Yoon–Ryu, ICML 2021](https://proceedings.mlr.press/v139/yoon21d.html). In the repository, [StochasticGeneralizedMonotone](../../LongTails/Theorems/StochasticGeneralizedMonotone.lean) (14 Oct 2026, `L₁=0`) gives a high-probability guarantee with `log³` factors. Its criterion is different, and Markov conversion of this result introduces a polynomial `1/δ`, so the two are not comparable.

**Search coverage.** The searches were run on 2026-10-28 UTC and covered arXiv (2024–Oct 2026), JMLR/PMLR/NeurIPS records and the citations of the papers above. I read the theorem statements for RRSEG, Ji–Lan–Zhu and Yoon–Loizou through extracted HTML. I did not read the explicit convex–concave bound in RAIN ([Chen–Luo, JMLR 2024](https://www.jmlr.org/papers/v25/22-1126.html)): its abstract says only "near-optimal", and both Lee–Kim and Yoon–Loizou describe it as cubic-log. Yang et al. was checked only at the abstract level. The companion note's citations and claims agree with what I verified. The theorem was introduced in commit `a003880` on 2026-10-28, about one month after all three competitors appeared. The search cannot rule out concurrent unpublished work.

## Conclusion

**Yes, but only by one logarithmic factor: it is the first mean-only bound with `log²` rather than `log³` on the noise term.**

The strongest baseline with the same assumptions and oracle is Lee–Kim's RRSEG, along with Ji–Lan–Zhu's accumulative regularization. Yoon–Loizou already reached `log²`, but only under stronger sample-level assumptions.

| | Total calls for `E‖F‖² ≤ ε²` |
|---|---|
| RRSEG / Ji–Lan–Zhu (mean-only) | `LR/ε + (σ²/ε²) log³(LR/ε)` |
| Yoon–Loizou (samplewise, same-sample) | `(LR/ε) log(LR/ε) + (σ²/ε²) log²(LR/ε)` |
| This result (mean-only, fresh samples) | `LR/ε + (σ²/ε²) log²(2+LR/ε)` |

For fixed `L,R,σ > 0` and `ε → 0`, the comparison gives a `log(1/ε)` speedup over the mean-only baselines. Compared with Yoon–Loizou, the gain is a larger instance class: sample maps can be non-monotone or discontinuous, and only fresh samples are needed. This result gives up composite/constrained problems, state-dependent noise and fixed per-iteration query counts.

The gain is modest for two concrete reasons. It is purely logarithmic, and the `log²` statistical exponent existed a month earlier under samplewise assumptions. The proof also reuses Yang et al.'s inertial energy, with a new extragradient step. A known lower bound still leaves one logarithmic factor open, so neither paper's exponent is shown to be optimal.

What can be claimed: an improved `O(LR/ε + (σ²/ε²) log²(LR/ε))` RMS-residual complexity for stochastic monotone Lipschitz equations under mean-only assumptions, one logarithm better than prior mean-only guarantees.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
