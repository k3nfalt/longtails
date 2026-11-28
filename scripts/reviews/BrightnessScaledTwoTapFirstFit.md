# Novelty assessment: BrightnessScaledTwoTapFirstFit

The [theorem](../../LongTails/Theorems/BrightnessScaledTwoTapFirstFit.lean) shows that constant-step full-batch logistic [GD](../../LongTails/Algorithms/BrightnessScaledTwoTap.lean) on a two-tap circular convolution and readout deterministically reaches strictly positive margin on all rows, for sufficiently large brightness scale `R` in the stated [setup](../../LongTails/Setups/BrightnessScaledTwoTap.lean).

**Assumptions.** Split each signed image `x_i` into its constant-direction part and the remainder `z_i`; the trained data are `z_i` plus `R` times the constant part. Here `d_i=√2⟨e,x_i⟩`, `|d_i|≤D`, and the averages of `(d_i)_+` and `(-d_i)_+` are at least `μ>0`. The contrast `(I−S)z_i/√2` has margin `γ>0` along some unit vector, and its norm plus that of `(I+S)z_i/√2` is at most `J`. `P,Q≠0` are the initial tap sum and difference over `√2`, and `v₀` the readout, before the prescribed `R`-dependent rescaling. The step is an explicit constant over `R`; it and the initialization use public bounds. `R≥1` must also pass the three `largeScale` inequalities. These hold for large `R`, and nonempty instances exist (`d=n=2`).

**Budget** in full-gradient calls (`n` rows each), including the final fit check:

```text
N = O(1 + n (1+D) (1+J(1+|P|+|Q|)) [1+log(1+|P|(1+J)/min{1,|Q|γ})] / min{1,|Q|γ}^2
      × { 1 + ||v0|| + J(1+|P|+|Q|) + (1+J(1+|P|+|Q|))/μ + (1+log n)/min{1,|Q|γ}
          + n^2 (1+D) J(1+|P|+|Q|) (1+J(1+|P|+|Q|))^3
            [1+log(1+|P|(1+J)/min{1,|Q|γ})] log(e(1+|P|)R) / (μ^2 min{1,|Q|γ}^3) })
```

From the Lean definition, `N` is also at least of order `n³(J/γ)⁵ log(e(1+|P|)R)`, using `J≥γ`, `μ≤D` and `min{1,|Q|γ}≤|Q|γ`.

## The decisive reduction

Freeze the zero-sum filter `(a,b)=(1,−1)`. The constant direction cancels, leaving features `φ_i=(I−S)z_i` with `||φ_i||≤√2 J` and margin `√2 γ`. The theorem's own oracle returns the readout gradient at this point. GD on the readout alone, from zero with step `2/J²`, therefore solves the same fitting problem.

The standard smooth-convex bound `f(w_T) ≤ f(u) + ||u||²J²/(4T)`, with `u` the separator scaled to margin `log(2n/log 2)`, gives average loss below `log 2/n`, hence strict fit, in `O(1+nJ²log²(2n)/γ²)` calls. This needs no `R,D,μ,P,Q,v₀`, two-sided brightness, large-`R` condition or knowledge of the separator; its updates use only `J`, whereas the selected tuning also uses `R,D,γ,Q`. It is below the selected budget's order on every admissible instance.

## Comparison

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fixed-filter logistic GD; elementary smooth-convex argument above, not a cited paper theorem; same oracle | `O(1+nJ²log²(2n)/γ²)` → `N` above, at least order `n³(J/γ)⁵log(e(1+\|P\|)R)` | Worse: at least polynomial factors in `n,J/γ`, plus `log R` | None | None; same strict-fit output | Baseline fixes the filter; selected result trains it and needs more assumptions |
| Normalized logistic GD, [Tyurin 2024, Thm. 6.1](https://arxiv.org/abs/2412.08424), at the fixed filter | `O(1+J²/γ²)` with large step parameter at least order `log(2n)/γ²` → same `N` | Worse | None | None | Baseline also needs the mean logistic vote for normalization, which this oracle does not return |
| Repository overlap: [FiniteScaleConvolutionalSgd](../../LongTails/Theorems/FiniteScaleConvolutionalSgd.lean), joint two-tap SGD, rows divided by `R` | `O(n³(D/min\|d_i\|)²max{J/γ,4}³ log(24·10⁶D²R²/min{γ,J/4}²)(1+log(1/q)))` component calls → `nN` row evaluations, at least order `n⁴(J/γ)⁵log(e(1+\|P\|)R)` | Not comparable overall; both logarithmic in `R`, earlier bound has smaller `n,J/γ` exponents | Every `\|d_i\|` nonzero → zero rows allowed, but both signs now required on average | High-probability → deterministic | Earlier: component oracle, IID sampling, own initialization and contrast condition, all `d_i≠0` |
| Ordinary raw linear logistic GD; same standard argument | `O(1+n(J²+R²D²)log²(2n)/γ²)` → `N` above | For fixed other parameters and `R→∞`: proved upper bound `R²→log R` | None | None | Selected method uses a convolution model and `R`-dependent initialization; no raw-GD lower bound follows |

Ancestry: [Tyurin, ICML 2026](https://arxiv.org/abs/2512.11587v2) motivates the model (Figure 1: about 330K raw versus 20K convolutional CIFAR-10 iterations); its Theorem 5.1, seen only through an extracted summary, concerns two-sample perceptron dynamics. [Ji–Telgarsky](https://arxiv.org/abs/1810.02032), Theorems 3.2–3.3, are asymptotic. [Zhang et al.](https://arxiv.org/abs/2504.04105), Theorem 2.1, needs `1/γ²` burn-in for adaptive-step logistic regression (unit-norm data), using the loss value.

**Reduction check and mechanism.** A fixed-filter reduction beats the guarantee; the changing-comparator ("transport") argument for joint GD may be new analysis, but I did not audit its proofs or settle priority.

**Companion note.** The [note](../../LongTails/Theorems/BrightnessScaledTwoTapFirstFit.md) admits that a zero-sum filter removes brightness and claims no algorithmic optimality, but does not quantify that baseline. It omits `FiniteScaleConvolutionalSgd` (added 30 October 2026; this theorem 28 November), which already gives finite-sample fitting for joint two-tap SGD with logarithmic contrast dependence. Its experiments lie outside the theorem's tuning; it reports a fixed difference filter fitting sooner (7,254 versus 18,868 updates). Experiments and CIFAR constants were not rechecked.

**Search coverage (28 November 2026 UTC).** Targeted, non-exhaustive searches covered two-layer, linear-convolutional and large-step logistic GD (pages retrieved through a web-fetch helper); PRs #258 and #279–#282 were not read (`gh` had no token), so the note's `O(R)` joint and `Ω(R²/log R)` raw/tangent claims are unverified. No build or axiom audit was run.

## Conclusion

**No: this does not improve the complexity of solving the stated classification problem.**

The assumptions guarantee that the fixed filter `(1,−1)` removes brightness and leaves separable data. Ordinary logistic GD on the readout then uses the same gradient oracle:

| Method | Full-gradient calls |
|---|---|
| Readout only, fixed filter | `O(1+nJ²log²(2n)/γ²)` |
| Joint GD (this theorem) | at least order `n³(J/γ)⁵log(e(1+\|P\|)R)` in its proved budget |

The first bound is independent of `R`, smaller on every admissible instance, and needs fewer assumptions. These are upper bounds, so they say nothing about how fast joint GD actually is.

What the theorem adds is a guarantee for one method: simultaneous GD on both layers fits in `O(log R)` calls at fixed data, whereas the standard bound for raw linear GD grows like `R²`. That holds only for very large `R` with a specially rescaled initialization (the note reports about `10⁶³` for its CIFAR example), and a simple preprocessing choice already does better. The method-specific analysis may be new, but the checked evidence does not show an independent optimization advantage.

The claimable contribution is a finite-time analysis of how this particular joint parameterization copes with large brightness, not a faster or broader solution of the problem.

**Verdict: NO IMPROVEMENT. Confidence: high.**
