# Novelty assessment: power-geometry acceleration under biased relative gradient error

[`result`](../../LongTails/Theorems/PowerGeometryRelativeErrorAcceleration.lean) proves the following. Take a finite-dimensional normed space whose squared norm `Ψ = ‖·−x₀‖²/2` has a scale-relative `p`-power Bregman modulus `c` (with `p > 2`). Let `f` be convex and `L`-smooth with respect to that norm, with a global minimizer `x*`, `‖x*−x₀‖ ≤ R`. Suppose every reply satisfies `‖g−Df(y)‖_* ≤ α‖Df(y)‖_*` with `α ≤ 1/4`; errors may be biased and may vary with the call and the seed. Then the last steepest-step iterate `x_K` of unconstrained [squared-norm dual averaging](../../LongTails/Algorithms/PowerDualAveraging.lean) satisfies `f(x_K) − f(x*) ≤ ε` for every seed ([setup](../../LongTails/Setups/PowerGeometryRelativeErrorConvex.lean)).

**Complexity.** Here `L` is the smoothness constant, `R` the initial distance, `ε` the accuracy, `α` the relative error, and `p, c` the geometry constants.

  K = O(1 + (C·LR²/ε)^{p/(p+2)} + α²LR²/ε),  C = max{1, 32^{(p−2)/2}/c}.

There are no logarithms, and each step makes one gradient call. The updates use `L, p, c, α` but not `R`, `ε` or the horizon; the budget uses `R` and `ε`. For `(ℝᵈ,‖·‖_p)`, the note's derivation (checked at sketch level) gives `c = 2^{2−p}/(p(p−1))`, so `C = p(p−1)2^{7(p−2)/2}`. This constant does not depend on `d`, but it is large: for p = 4 it equals 1536.

Below, `T₀ = LR²/ε` and `s = 1/2 − 1/p`; the comparisons are for ℓ_p with fixed p.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| d'Aspremont–Guzmán–Jaggi, [arXiv:1301.0465v3](https://arxiv.org/abs/1301.0465) (SIOPT 2018), Prop. 4.9, Cor. 4.10, §5.1.2. **Exact gradients only**; feasible ℓ_p ball, prox `‖x‖_p^p/p` | O_p(T₀^{p/(p+2)}) → O_p(T₀^{p/(p+2)} + α²T₀) | None at α = 0: same order | Exact oracle → biased relative error with α ≤ 1/4 | Prox domain built from R → R absent from the updates (still in the budget); the output in both cases is the final iterate | α ≤ 1/4; larger p-dependent constant |
| The same method with relative error treated as δ-inexactness (my reduction sketch, not a published theorem). On B(x₀,2R), δ ≤ 12αLR², assuming the standard O(Tδ) accumulation | O_p(T₀^{p/(p+2)}) only for α ≲ T₀^{−(2p+2)/(p+2)}; otherwise an error floor → O_p(T₀^{p/(p+2)} + α²T₀) | The admissible α for the accelerated rate grows from T₀^{−(2p+2)/(p+2)} to T₀^{−1/(p+2)}. Between these thresholds the baseline gives no ε-guarantee | None beyond row 1 | Same as row 1 | Same as row 1 |
| Euclidean relative-error acceleration ([repo theorem](../../LongTails/Theorems/AcceleratedRelativeErrorConvex.lean); Vasin–Gasnikov [arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376), Thm 7.2, gives a log-worse bound), via norm conversion `L₂ ≤ L`, `R₂ ≤ d^s R`, `α₂ = d^s α` | O(d^s√T₀ + α²d^{4s}T₀), valid only if d^sα < 1 → O_p(T₀^{p/(p+2)} + α²T₀) | Better whenever d ≳ T₀^{p/(p+2)}. The noise term is never worse, and the result also covers d^sα ≥ 1. Worse for d ≪ T₀^{p/(p+2)} | Euclidean-norm error → dual-ℓ_q relative error (in high dimension this tolerates larger errors) | None | Needs p > 2 and α ≤ 1/4 (the repo theorem allows α < 1) |
| Pethick, [arXiv:2606.15268v1](https://arxiv.org/abs/2606.15268) (June 2026; listed for NeurIPS 2026), Cor. 3.2: SODA with a p-uniformly convex prox | Overlaps only at α = 0: O_p(T₀^{p/(p+2)}) → same order | None on the overlap | Unbiased noise (Assumption 3) → arbitrary biased relative error. Pethick's noise model is incomparable: heavy-tailed, stochastic | η tuned with D⋆ (needs R) → R-free updates; expected accuracy → pathwise accuracy | No stochastic additive noise; α ≤ 1/4 |

**Reduction check.** Each direct substitution I tried (rows 2–4) either leaves an error floor, pays dimension factors `d^s`, or needs unbiasedness. Repeating or clipping queries does not remove an adversarial bias. The new mechanism combines two pieces:
- the Euclidean repo idea that the steepest step's slack absorbs the relative error;
- a squared-norm mirror whose curvature degrades only with the iterate scale, together with weights `β_n` that grow enough to absorb both the geometry defect and the α-error, without a bounded domain.

Proof ancestry: Nemirovski–Nesterov and d'Aspremont et al. supply the power-geometry acceleration. The drift identity for a growing regularizer is standard (e.g., Jacobsen–Cutkosky). The companion note also derives two comparators of its own: a mixed comparator O(d^s√T₀ + α²T₀) and a Frank–Wolfe comparator O(T₀). These are not published theorems, I did not verify them, and I did not use them in the table.

**Search coverage.** I searched on 2026-10-18 UTC: arXiv and proceedings for relative or inexact gradients in non-Euclidean, uniformly convex and Muon/LMO settings. Sources covered were Kornilov et al. 2310.00506 (abstract only), Vasin et al., Contreras et al. 2411.08987 (search result only), Qian–Richtárik 2606.21581 (not accelerated) and Shulgin 2510.19933 (search result only). I read d'Aspremont et al. and Pethick directly. I did not re-read Lezane et al. or Cohen–Diakonikolas–Orecchia; their quadratic-prox absolute-error analyses could give a stronger mixed comparator than row 3. The note's citations match what I checked. The result was committed on 2026-10-18 (f687252), so there is no later work to compare against.

## Conclusion

**Yes: for small relative error in high-dimensional ℓ_p geometry, this is the first accelerated guarantee I found that tolerates biased errors.**

The strongest exact-gradient baseline is d'Aspremont–Guzmán–Jaggi. Exact gradients are the α = 0 case, where the rate is matched and nothing is gained. With errors, the checked alternatives either stall or pay a dimension factor:

| α regime (fixed p, d ≳ T₀^{p/(p+2)}) | best checked baseline | this result |
|---|---|---|
| α ≲ T₀^{−(2p+2)/(p+2)} | O(T₀^{p/(p+2)}) | same |
| up to α ≲ T₀^{−1/(p+2)} | error floor, or Euclidean O(d^s√T₀ + α²d^{4s}T₀) if d^sα < 1 | O(T₀^{p/(p+2)}) |

For example, take p = 4, d = T₀² and α = T₀^{−1/6}. The Euclidean conversion then does not apply, while this result needs O(T₀^{2/3}) calls. It loses to Euclidean acceleration when d ≪ T₀^{p/(p+2)}. Its constants grow quickly with p, and it requires α ≤ 1/4.

Within the checked baselines this gain is established. Priority is less certain: the field is small, and analyses with quadratic prox and noise in general norms were not fully re-derived. The claimable contribution is an unconstrained, R-free-update, last-iterate accelerated rate in power geometry that withstands arbitrary relative gradient bias.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
