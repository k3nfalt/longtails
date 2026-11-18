# Novelty assessment: DistributedCurvatureNormalized

[`result`](../../LongTails/Theorems/DistributedCurvatureNormalized.lean) builds an event-driven star-network algorithm ([DistributedNormalizedTraining](../../LongTails/Algorithms/DistributedNormalizedTraining.lean)). For every `L`-smooth function with `Q`-Lipschitz Hessian and every collection of independent unbiased worker oracles with variance `σ²` ([setup](../../LongTails/Setups/DistributedHessianLipschitzNonconvex.lean)), its actual execution returns, by a fixed deadline, a uniformly selected coordinator iterate `X` with `E‖∇f(X)‖ ≤ ε`.

**Parameters.** `d` is the dimension and `n` the number of workers. `H = maxᵢ hᵢ` is the per-gradient time. `ℓ` is the packet latency and `b` the time per bit. `Δ` bounds the initial gap. Write `A = 1 + LΔ/ε²`, `λ_s = 1 + log(1 + A√d)`, and `λ_u = 1 + log(1 + (d²A + d·min(σ²/ε², n))/√n)`. These come from `B(x) = size⌈2²⁰(1+x)⌉ + 66 = Θ(1 + log(1+x))`. The proved deadline is, up to universal constants:

```
T = A·[ ℓ + H + bλ_u + bλ_s + dbλ_u/n + dbλ_s/√n + (d³ b³ λ_u λ_s² / n)^{1/3}
        + Hσ²/(nε²) + √(d H σ² b λ_u / (nε²)) + d b λ_s · min{1, √(Qε)/L} ]
```

The elapsed time is deterministic and covers every `d ≥ 0` and `Q ≥ 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Inkheart SGD, Begunov–Tyurin, [arXiv:2605.07795](https://arxiv.org/abs/2605.07795) Thm 2.2 (v1 May 8 2026, v2 Oct 19 2026; [NeurIPS 2026 poster](https://neurips.cc/virtual/2026/poster/150535)); prior, direct competitor on the L-smooth superset | Run with target `E‖∇f‖² ≤ ε²` and `κ = bλ_s`, `τ = bλ_u` (per-coordinate costs). Its time is `max{h,τ,κ,dκ/√n,dτ/n,(d³τκ²/n)^{1/3},√(dσ²hτ/(nε²)),σ²h/(nε²)}·L_maxΔ/ε² + dκL_AΔ/ε²`. By its Prop. 1.9, `L_A ≤ 2√2·L`, and `L_A = Θ(L)` when the Hessian varies by `Θ(L)` over ℝᵈ. That gives a downlink term `dbλ_sLΔ/ε²` → `dbλ_s·min{LΔ/ε², √QΔ/ε^{3/2}}`, with the other terms matching up to `ℓ` and `1+` | Factor `L/√(Qε)` on the non-scaling downlink term when `√(Qε) < L` and that term dominates. Example: with `L,Q,Δ,σ,H,b` fixed, `ℓ = 0`, `d ≍ ε^{-7/4}`, `n ≍ ε^{-3/2}`, the time goes from `ε^{-15/4}` to `ε^{-13/4}log(1/ε)` | Inkheart's global Hessian-variation constant `L_A` → local `Q`-Lipschitz Hessian. The classes overlap but neither contains the other; this result assumes `Q < ∞` | Expected time → deterministic deadline. Latency, bit precision and packet padding are charged here, not in Inkheart | Weaker criterion: `E‖∇f‖ ≤ ε` instead of `E‖∇f‖² ≤ ε²`; Inkheart's guarantee implies this one by Jensen, not conversely. Worse when `L_A ≲ √(Qε)` (Inkheart's Prop. 1.8/Ex. 1.10: quadratic plus small-`L` perturbation). Common objective only; Inkheart's M4 also handles heterogeneous `fᵢ` |
| Synchronous minibatch SGD (Inkheart eq. (2)); repo [DistributedBatchedSgd](../../LongTails/Theorems/DistributedBatchedSgd.lean) | `(dκ + dτ + h)LΔ/ε² + hσ²LΔ/(nε⁴)` → `T` | Removes `d(κ+τ)LΔ/ε²`; the other terms match or improve | Needs Hessian-Lipschitz (narrower) | Same as above | Weaker criterion than squared norm |
| Serial NIGT, Cutkosky–Mehta, [ICML 2020](https://proceedings.mlr.press/v119/cutkosky20b.html) Thm 3 (one worker, same assumptions) | `O(H·ε^{-7/2})` at fixed `L,Q,Δ,σ`, plus `O(dbλ)` to return the output → `T` | Better when `d ≪ ε^{-2}` and `n` is large (exponent `13/4` vs `7/2` in the example) | None | None | Worse once `d ≳ ε^{-2}`, because `T ≥ dbλ_s√QΔε^{-3/2}` |

**Reductions and mechanism.** I found no substitution or reduction that gives the `√(Qε)` term. Inkheart's Prop. 1.9 needs a Hessian-variation bound over all of ℝᵈ, which a Lipschitz Hessian does not supply on an unbounded domain. Squaring the second-order Taylor remainder for Inkheart's `‖∇f‖²` criterion needs fourth moments of the worker model discrepancies. The new step is a norm-error normalized-descent analysis with conditional Taylor cancellation `‖avg ∇f(x+eᵢ) − ∇f(x)‖ ≤ L‖avg eᵢ‖ + Q·avg‖eᵢ‖²`. The proof ancestry is Inkheart (compressor structure and time frontier; every other term has the same shape) and NIGT (normalization under Hessian regularity). My own scaling check is consistent with this: the Carmon-type smooth hard functions behind Tyurin's [lower bound](https://arxiv.org/abs/2506.23836) have `Q ≍ L²/ε`, so that bound constrains only the regime `√(Qε) ≳ L`.

**Search coverage.** Searched 2026-11-18 (UTC): arXiv and NeurIPS/ICML/ICLR listings on bidirectional and downlink compression, MARINA-P and EF21-P, Shadowheart, and Hessian-Lipschitz distributed methods. I read Inkheart v2 Sections 1–5 from HTML; its appendices, the formal statement of Tyurin's lower bound, and the NIGT constants were not verified. The companion note's Inkheart citation is accurate. Its regime arithmetic checks out (`ε^{-13/4}` vs `ε^{-15/4}`). The result was added to the repository on Nov 17–18 2026, after both Inkheart versions.

## Conclusion

**Yes: under a Lipschitz Hessian, this result proves a polynomially smaller elapsed-time bound than the strongest prior one.**

The closest prior result, Inkheart SGD, scales every term with `n` except the downlink cost `dκL_AΔ/ε²`, and for general Hessian-Lipschitz objectives `L_A` can be as large as `L`. This theorem replaces that cost, keeping the other terms in the same shape:

```
dκ·LΔ/ε²   →   dκ·min{LΔ/ε², √Q·Δ/ε^{3/2}}      (κ ≈ b·log-precision)
```

For example, with `d ≍ ε^{-7/4}` and `n ≍ ε^{-3/2}` the time drops from `ε^{-15/4}` to `ε^{-13/4}log(1/ε)`.

There are tradeoffs. The accuracy criterion is weaker: expected gradient norm instead of expected squared norm. A Lipschitz Hessian must be assumed. Inkheart wins whenever its global Hessian-variation constant is below `√(Qε)`, for example on near-quadratic objectives. When `d ≳ ε^{-2}`, a single worker running NIGT is faster.

The comparison establishes the gain over the checked methods. Priority is less certain: no competing analysis turned up, but Inkheart's appendices and newer distributed second-order work were not fully checked.

The contribution that can be claimed is a new elapsed-time frontier for compressed downlinks, in which the non-scaling downlink cost uses local Hessian regularity instead of a global similarity constant.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
