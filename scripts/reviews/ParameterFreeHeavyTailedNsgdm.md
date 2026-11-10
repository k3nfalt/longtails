# Novelty assessment: ParameterFreeHeavyTailedNsgdm

[`result`](../../LongTails/Theorems/ParameterFreeHeavyTailedNsgdm.lean) proves the following. Take an `L`-smooth `f` on a complete inner-product space with `f(x0) − inf f ≤ Δ`, and IID unbiased stochastic gradients with central `p`-th moment `≤ σ^p` for some `1 < p ≤ 2` ([setup](../../LongTails/Setups/ParameterFreeHeavyTailedSmooth.lean)). The [algorithm](../../LongTails/Algorithms/ParameterFreeNsgdm.lean) is built from `x0` alone. It runs a doubling-horizon grid search over normalized SGD with momentum (NSGDm), parametrized by momentum and step size, and picks a candidate by the norm of a fresh-sample gradient mean. After `N` oracle calls its output satisfies `∫‖∇f(x_out)‖ dP ≤ ε`.

**Complexity.** Parameters: `L` is the smoothness constant, `Δ` the initial gap, `σ` the noise scale, `p` the tail index, `ε` the accuracy, and `c` a universal constant. Simplifying the Lean budget exactly gives

```
N = O( ℓ² · [ LΔ/ε² + c^{1/(p−1)}·( LΔ σ^{p/(p−1)} ε^{−(3p−2)/(p−1)}
        + σ^{(5p−2)/(2p−2)} (LΔ)^{−p/(2p−2)} ε^{−(3p−2)/(2p−2)} + (σ²/(LΔ))^{p/(2p−2)}
        + (1+σ/ε)^{p/(p−1)} ((1+log(1+σ/ε))/(p−1))^{4/(p−1)} ) + √(L/Δ) + (Δ/L)^{1/3} ] ),
```

where `ℓ = log(2 + [bracket])`. This covers every run and every validation sample. The third and fourth terms are dominated by the main term when `σε ≤ LΔ` and `ε² ≤ LΔ`; `ε² < 2LΔ` holds in every nontrivial instance.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Zhou, [ICLR 2025, arXiv 2412.19529v4](https://arxiv.org/abs/2412.19529), Thm 3.6 (`L₁=σ₁=0`); Hübler–Fatkhullin–He, [AISTATS 2025, arXiv 2410.13849v3](https://arxiv.org/abs/2410.13849), Prop. 1 / eq. (4). Same class, `p` unknown | `(Δ⁴+L⁴)/ε⁴ + (σ/ε)^{2p/(p−1)}` → `ℓ²[LΔ/ε² + LΔσ^{p/(p−1)}ε^{−(3p−2)/(p−1)} + …]` | Accuracy exponent `2p/(p−1)` → `(3p−2)/(p−1)`. Speedup ≈ `(σ/ε)^{p/(p−1)}ε²/(LΔℓ²)` when `(σ/ε)^{p/(p−1)} ≫ (LΔ/ε²)ℓ²`; e.g. `p=3/2, L=Δ=σ=1`: `ε⁻⁶ → ε⁻⁵log²(1/ε)`. Deterministic part `(Δ⁴+L⁴)/ε⁴ → LΔ/ε²` | None (same class) | Baselines need the horizon `T` (removable by standard doubling). Here no parameter is needed. Same random-iterate `E‖∇f‖` criterion | Extra `ℓ²`. An additive `V`-term `≥ 64^{1/(p−1)}(22/(p−1))^{4/(p−1)}` (≈10¹¹¹ at `p=1.1`); baselines' `p`-constants unchecked. Initial-sample term. Grid of `Θ(k²)` restarted runs |
| Liu–Zhou Thm 3.2 (`L₁=0`), known `p,σ,L,Δ,T` (lower bound: Liu–Zhou Thm 3.3; Zhang et al. 2020) | `LΔ/ε² + (σ/ε)^{(2p−1)/(p−1)} + LΔσ^{p/(p−1)}ε^{−(3p−2)/(p−1)}` → same leading terms × `ℓ²` | None: same order up to `ℓ²` when `σε ≤ LΔ`. Worse when `σε > LΔ`, by about `(σε/(LΔ))^{p/(2p−2)}` | None | `p, σ, L, Δ, T` known → nothing known | Extra `ℓ²`, `V`-term, scale terms `√(L/Δ)+(Δ/L)^{1/3}` |
| Khaled–Jin, [ICML 2024, arXiv 2402.07793v2](https://arxiv.org/abs/2402.07793), Thm 6. Restricted to `p=2` with a.s. bounded noise and given hints | Hint-dependent polylog × `(LΔ/ε² + LΔR²/ε⁴)`, with high probability → expectation `ℓ²(LΔ/ε² + LΔσ²/ε⁴ + …)` | Not comparable: different confidence criterion, and the costs depend on the hints | Bounded noise → `p`-th moment only, any `p∈(1,2]` | Hints `L̄, Δ̄, R̄` → none | High probability → expectation only |

**Reduction check / proof ancestry.** The result is a composition of known pieces. The first is Liu–Zhou's fixed-`(β,η)` NSGDm bound, re-proved here as Lemma A. The second is Khaled–Jin's restart-over-a-step-grid with gradient-norm validation (FindLeader), with the grid extended to momentum. The third is the doubling trick. The model-selection idea also appears in Lawrence et al. ([JMLR 27, 2026](https://jmlr.org/papers/v27/25-2383.html)) for convex problems. The one new step is modest: the validation error is controlled in expectation using only `p`-th moments, via von Bahr–Esseen, which costs `C_k^{1/p}`. That cost is the source of the `log^{4/(p−1)}` term. I found no obstacle that the composition fails to overcome, and the Lean proof carries it out.

**Search coverage.** On 2026-11-10 I searched arXiv (API) and the web for unknown-tail-index, parameter-free and tuning-free heavy-tailed nonconvex work from 2020–2026. I read the theorem statements of Liu–Zhou (Thms 3.2, 3.3, 3.6 and the Conclusion), Hübler et al. (eq. (4), Thm 2 and the open question in Sec. 5) and Khaled–Jin (Thm 6), and checked the abstracts of arXiv 2512.18713, 2602.13413, 2605.18694 and 2505.03736. All of these report `2p/(p−1)` when `p` is unknown, or assume more. I found no prior or later result that reaches `(3p−2)/(p−1)` without knowing `p`. The result entered the repository on 2026-11-10 (commit `58b28b1c`). Two discrepancies with the companion note:
- It lists Liu 2026 AdaGrad-Norm as needing "nothing", but that paper's abstract states an extra assumption.
- It does not mention the size of the `p`-dependent constants. I did not check the theorem numbers it gives for Fradin et al. or He et al.

The Lean statement certifies the budget `N` only; the anytime property is proved internally (`main_success`) but is not exported.

**Conclusion**

**Yes: when the tail index is unknown, the proved complexity is better than every published guarantee I found.** The strongest unknown-`p` baselines are Liu–Zhou Thm 3.6 and Hübler et al. eq. (4). The leading term changes as follows:

| | `p` unknown, `σ`-dominated regime |
|---|---|
| Before | `(σ/ε)^{2p/(p−1)}` |
| After | `LΔσ^{p/(p−1)}ε^{−(3p−2)/(p−1)}·log²` |

This is a gain of `ε^{−(2−p)/(p−1)}` up to logarithms for fixed `L, Δ, σ` (for example, `ε⁻⁶ → ε⁻⁵log²` at `p=3/2`). It matches the known-`p` lower bound up to `log²` and lower-order terms. It answers the questions Liu–Zhou and Hübler et al. posed as open, up to those factors.

The costs are a squared logarithm and an additive term of order `(c/(p−1))^{4/(p−1)}(σ/ε)^{p/(p−1)}`, whose constant is astronomically large as `p → 1`. The guarantee is in expectation only, and the method is a grid search over restarted runs rather than a single adaptive run. Against methods that know `p`, it is no faster, and it is worse when `σε > LΔ`.

The comparison establishes the gain. Priority rests on a search that turned up no competing construction, and that is not proof that none exists. Technically, the result is a fairly routine composition of known NSGDm bounds with grid validation. What can be claimed is the first near-optimal oracle complexity, in expectation, for heavy-tailed smooth nonconvex optimization with no knowledge of `p`, `σ`, `L`, `Δ` or `ε`. It does not come with a new proof technique.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
