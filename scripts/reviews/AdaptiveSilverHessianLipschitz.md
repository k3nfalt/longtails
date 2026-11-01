# Novelty assessment: AdaptiveSilverHessianLipschitz

[`result`](../../LongTails/Theorems/AdaptiveSilverHessianLipschitz.lean) proves the following for every finite-dimensional `C²` function `f` with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian and `f(x₀) − inf f ≤ Δ` ([setup](../../LongTails/Setups/SmoothHessianLipschitzGd.lean)). The deterministic, gradient-only, momentum-free method [gradient-norm-gated silver GD](../../LongTails/Algorithms/AdaptiveSilverGd.lean) outputs a queried point with `‖∇f(x̂)‖ ≤ ε`. Each step is `x − h·∇f(x)`, with `h` chosen from the history using `L, ρ, Δ, ε`, and compliance with `adaptiveGdFamily` is proved.

**Complexity.** Here `L` is the gradient Lipschitz constant, `ρ` the Hessian Lipschitz constant, `Δ` the initial gap and `ε` the target gradient norm. The proved budget `⌈90LΔ(ρε/L²)^{1/22}/ε²⌉ + ⌈400(LΔ/ε²)^{4/5}⌉ + 8` gives

  N = O( (LΔ/ε²)·(ρε/L²)^{1/22} + (LΔ/ε²)^{4/5} + 1 ),  for L, ε > 0 and ρ, Δ ≥ 0.

When `ρε > L²`, the first term exceeds plain GD's order. The bound gives no gain there.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| GD with step `1/L`; best-gradient bound `min‖∇f‖² ≤ 2LΔ/N` (Nesterov, *Lectures on Convex Optimization*, 2018, §1.2.3) | `O(1 + LΔ/ε²)` → `O(1 + LΔ/ε²·(ρε/L²)^{1/22} + (LΔ/ε²)^{4/5})` | Asymptotically better by a factor `≍ min{(L²/(ρε))^{1/22}, (LΔ/ε²)^{1/5}}` when `ρε ≪ L²` and `LΔ ≫ ε²`. Example: fixed `L, ρ, Δ` and `ε→0` gives `ε^{-2} → ε^{-21/11}`. With the stated constants, a gain needs `L²/(ρε) > 45²² ≈ 10^{36.4}` and `LΔ/ε² > 200⁵`. | None: GD needs only `L`-smoothness. | None: both output the best queried point. | Needs a Lipschitz Hessian. Uses `ρ` and `Δ` in the updates, whereas GD needs only `L`. Its constants are much larger. |
| Restarted AGD, [Li–Lin, arXiv:2201.11411v4](https://arxiv.org/abs/2201.11411) Thm 1 (ICML 2022). It uses gradients only. Its proof requires `ρ>0` and `ρε ≤ L²/16`, and it guarantees `‖∇f(ŷ)‖ ≤ 82ε`. Rescale `ε` by 82, run it with `ρ' = max(ρ, ε³/Δ²)`, and fall back to GD otherwise. | `O(1 + min{LΔ/ε², ΔL^{1/2}ρ^{1/4}ε^{-7/4} + √(LΔ)/ε})` → selected bound above | Worse. The first-term ratio is `(L²/(ρε))^{9/44} ≥ 1` throughout `ρε ≤ L²`. The `ρ→0` term is `(LΔ/ε²)^{4/5}` versus `(LΔ/ε²)^{1/2}`. No regime favors the selected result. | None: same class. | None on the class. The selected output is a queried point, while Li–Lin's is an average of iterates. Both are deterministic gradient-norm guarantees. | The selected method has no momentum. That is its only distinguishing feature. |
| Repository [`WeaklyConvexSilver`](../../LongTails/Theorems/WeaklyConvexSilver.lean) (`ρ_w`-weakly convex, `L`-smooth) | Not comparable: it gives `O(LΔ(ρ_w/L)^{3/20}/ε² + (LΔ/ε²)^{4/5})`, and a Lipschitz Hessian gives only `ρ_w = L` | Not comparable | The classes are incomparable. This theorem covers strict saddles with `λ_min = −L`, provided the Hessian is Lipschitz. | None | None |

**Reduction check and mechanism.** I found no reduction from known theorems. Silver-step analyses ([Altschuler–Parrilo, arXiv:2309.07879](https://arxiv.org/abs/2309.07879), [arXiv:2309.16530](https://arxiv.org/abs/2309.16530)) need convexity, and exact constant-step GD analyses ([Rotaru–Glineur–Patrinos, arXiv:2406.17506](https://arxiv.org/abs/2406.17506)) give only `Θ(LΔ/N)`. The silver schedule and block-descent inequality are proof ancestry. What is new is the following machinery:
- the eigenspace split at the junction of two blocks;
- the Duhamel control of cubic Taylor errors;
- the gradient-norm abort rule.

**Search coverage.** On 2026-10-30, I searched arXiv and the web for long-step/silver/hedged GD on nonconvex, hypoconvex and Hessian-Lipschitz objectives. I also checked the 2026 hedging survey [arXiv:2605.31386v2](https://arxiv.org/abs/2605.31386), which does not treat nonconvexity, and Zhou's unreviewed `Ω(ε^{-7/4})` claim [arXiv:2606.05438v2](https://arxiv.org/abs/2606.05438). I found no prior `o(ε^{-2})` result for momentum-free GD on this class. However, I did not read journal versions, Cartis–Gould–Toint, or recent PEP preprints in full. Altschuler–Parrilo's §6 "Beyond convexity" does ask whether hedging gives accelerated rates to stationary points, as the note says. The companion note's comparisons are consistent with the Lean statement. The result was introduced in commit `43753e4` (2026-10-30).

## Conclusion

**No complexity advantage for the problem class; the possible novelty is that momentum-free GD provably beats `ε⁻²` here.**

Gradient-only restarted AGD (Li–Lin) is already faster on the identical class in every regime:

| Method | Gradient calls |
|---|---|
| Li–Lin RAGD (retuned) | `ΔL^{1/2}ρ^{1/4}ε^{-7/4} + √(LΔ)/ε` |
| This result | `LΔ(ρε/L²)^{1/22}ε^{-2} + (LΔ/ε²)^{4/5}` |

Relative to plain GD, the gain is an exponent improvement of about 0.045 in ε. It holds only when `ρε ≪ L²` and `LΔ ≫ ε²`, and with the stated constants it appears only for `L²/(ρε)` above about 10³⁶.

This is a method-specific result of the kind that matters only through independent significance. It partially answers an open question posed by Altschuler–Parrilo: GD steps alone can beat `ε⁻²` on Lipschitz-Hessian nonconvex functions. However, this is far from "GD almost as fast as AGD": the gap in the ε exponent is 0.16 out of the 0.25 that momentum gains. Moreover, the steps depend on gradient-norm tests and on `ρ, Δ`, so the method is not a fixed schedule. The comparison establishes the gain over GD. My search found no prior result of this kind, but that does not prove priority.

What can be claimed is the following: a qualitative first `o(ε⁻²)` guarantee for adaptive momentum-free GD on this class, with a tiny exponent gain and no improvement over accelerated methods.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
