# Novelty assessment: `AbcNoiseSgdUpperBound`

[`result`](../../LongTails/Theorems/AbcNoiseSgdUpperBound.lean) proves this. Take any real Hilbert space, an `L`-smooth `f` with `f(x₀) − inf f ≤ Δ`, and an IID, unbiased, jointly measurable oracle with variance at most `2A(f(x) − inf f) + B‖∇f(x)‖² + C` ([setup](../../LongTails/Setups/AbcNoiseNonconvex.lean)). Constant-step SGD then outputs a uniformly sampled iterate `x_τ` ([`sampledSgd`](../../LongTails/Algorithms/AbcSgd.lean)) with `E‖∇f(x_τ)‖ ≤ ε`.

**Complexity.** The proved budget is `⌈144LΔ(1 + B + AΔ/ε² + C/ε²)/ε²⌉ + 1` oracle calls, that is,

```
N = O( 1 + LΔ(1+B)/ε² + L A Δ²/ε⁴ + L C Δ/ε⁴ ).
```

Here `L` is the gradient-Lipschitz constant, `Δ` the initial gap, and `ε` the target accuracy. `A`, `B`, `C` are the ABC constants in variance form; this `B` equals Khaled–Richtárik's second-moment `B` minus 1. Valid parameters are `L, ε > 0` and `A, B, C, Δ ≥ 0`. At `Δ = 0` the budget is one call, and the proof covers that case.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Khaled–Richtárik, [arXiv 2002.03329v3](https://arxiv.org/abs/2002.03329) (24 Jul 2020; [TMLR 2023](https://mlanthology.org/tmlr/2023/khaled2023tmlr-better)), Thm 2 and Cor 1 | `K ≥ (12LΔ/ε²)·max{1+B, 12AΔ/ε², 2C/ε²}`, one call per step, i.e. `O(1 + LΔ(1+B)/ε² + LAΔ²/ε⁴ + LCΔ/ε⁴)` → the same `O(·)` | None: same order (constants 12/144 vs 144) | `ℝ^d` → any separable Hilbert space; the proof is dimension-free, so this adds no meaningful instances | `min_k E‖∇f(x_k)‖ ≤ ε` → `E‖∇f(x_τ)‖ ≤ ε` for uniform `τ`. KR's Lemma 2 already bounds a weighted average with weights `w_k ∝ (1+Lγ²A)^{−k}`, whose ratios stay within `e`. So uniform sampling follows with a factor ≤ 3, a standard conversion | None. Both need `L, A, B, C, Δ, ε` for the step size and the horizon |
| Ghadimi–Lan, SIAM J. Optim. 23(4), 2013, Cor 2.2, cited from memory and not re-read this session (special case `A = B = 0`, `C = σ²`) | `O(1 + LΔ/ε² + LΔσ²/ε⁴)` → the same order on this overlap | None: same order | Bounded variance → ABC (already done by KR) | Same randomized-output type | None on this overlap |

**Reduction and mechanism.** Setting the Lean variance bound equal to KR's second-moment Assumption 2 with `B_KR = 1+B` and substituting into Cor 1 reproduces the budget exactly. The proof follows KR's route: a one-step bound with factor `ρ = 1 + LAη²`, `ρ^{K+1} ≤ e ≤ 3`, and then Jensen. No new mechanism appears. One oddity: KR's printed Cor 1 step `ε/(2LC)` should read `ε²/(2LC)`, as their own proof (§11.4) derives. Their stated `K` matches the corrected step.

Some repository results also use ABC noise. [`NormalizedStormExpectedSmoothness`](../../LongTails/Theorems/NormalizedStormExpectedSmoothness.md) and [`RecursiveMomentumAffineVariance`](../../LongTails/Theorems/RecursiveMomentumAffineVariance.md) both assume mean-squared smoothness, which requires same-sample evaluations at two points. That oracle is stronger, so they are not baselines here. The paired [`AbcNoiseLowerBound`](../../LongTails/Theorems/AbcNoiseLowerBound.md) is a separate contribution and is not assessed here. Arjevani et al. (Math. Program. 2023; cited from memory, not re-read) already give the `A = B = 0` lower bound `Ω(LΔ/ε² + LΔσ²/ε⁴)`.

**Search coverage (2026-11-17).** I read KR v3 Theorem 2, Corollary 1, Lemma 2 and the §11 proofs, and searched for 2024–2026 work under ABC/expected smoothness. Kawamoto–Iiduka ([arXiv 2510.20608](https://arxiv.org/abs/2510.20608), Oct 2025, later than KR) studies step-size schedules. I saw only search-level information on it and did not use it as a baseline. The theorem was introduced in commit `4aa4d0f7` (17 Nov 2026), more than six years after KR. The companion note itself says the upper bound is "not claimed as new", and nothing I found contradicts that.

**Conclusion**

**No: this is a formalization of a known SGD bound, not a new complexity result.**

The strongest baseline is Khaled–Richtárik's Corollary 1 (2020, TMLR 2023). It covers the same objective class, the same unbiased ABC oracle, the same constant-step SGD, and the same first-moment stationarity criterion:

```
KR:   O(1 + LΔ(1+B)/ε² + LAΔ²/ε⁴ + LCΔ/ε⁴)
Here: O(1 + LΔ(1+B)/ε² + LAΔ²/ε⁴ + LCΔ/ε⁴)
```

The two differences are cosmetic. A uniformly sampled output replaces KR's "min over iterates", and KR's weighted-sum lemma converts to that output at a constant cost. Allowing any Hilbert space in place of `ℝ^d` changes nothing in a dimension-free proof. Neither side has a regime where its total complexity is better than the other's beyond constants. The proof also follows KR's own argument.

What can be claimed is a machine-checked version of the Khaled–Richtárik bound, a useful upper-bound partner for the repository's ABC lower bound. It is not new mathematics.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
