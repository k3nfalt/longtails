# QuasarAmortizedLMO: what is actually new?

The [theorem](../../LongTails/Theorems/QuasarAmortizedLMO.lean) ([setup](../../LongTails/Setups/QuasarAmortizedLMO.lean), [algorithm](../../LongTails/Algorithms/TwoCallFrankWolfe.lean), [proof](../../LongTails/Proofs/QuasarAmortizedLMO.lean)) proves the following. Frank–Wolfe with steps `η_k = 2/(τk+2)`, exact gradients, and an additive-error LMO returns a feasible **last iterate** with `f(x_K) − f(x★) ≤ (6LD²/τ² + 2Γ/τ)/(K+1) ≤ ε` for every oracle seed. The objective is `L`-smooth on a real Hilbert space and `τ`-quasar-convex on a convex set `C` with respect to a constrained minimizer `x★`.

**Complexity (gradient + LMO calls):**
\[
N = 2\max\{1,\lceil (6LD^2/\tau^2 + 2\Gamma/\tau)/\varepsilon\rceil\} = O\!\left(1 + \frac{LD^2}{\tau^2\varepsilon} + \frac{\Gamma}{\tau\varepsilon}\right).
\]
The parameters are:
- `L`: global gradient-Lipschitz constant.
- `D`: diameter of `C`, which contains `x₀`; `C` need not be closed.
- `τ ∈ (0,1]`: quasar parameter.
- `Γ`: bound on every prefix sum of the nonnegative LMO errors `δ_k`, where call `2k+1` returns a point of `C` that is `δ_k`-optimal for every direction.
- `ε`: target accuracy.

The updates need only `τ` and `x₀`. The stopping budget needs `L, D, τ, Γ, ε`. With `Γ = 0` the oracle is an exact LMO. With `τ = 1` the class contains every smooth convex problem.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Martínez-Rubio, *Smooth Quasar-Convex Optimization with Constraints*, [arXiv:2510.01943](https://arxiv.org/abs/2510.01943), Thm 9 with Alg. 3 line 6, and Prop. 12 (v1 2 Oct 2025; [v3](https://arxiv.org/pdf/2510.01943v3) 14 Jul 2026; arXiv lists no venue). Prior work. | Exact LMO: Thm 9 gives `2⌈6LD²/(τ²ε)⌉` with the identical step `(a_t/γ)/(A_{t−1}+a_t/γ) = 2/(γt+2)`. Prop. 12 (short step) gives `O(1+LD²/(τ²ε))`. → `O(1 + LD²/(τ²ε) + Γ/(τε))` | None. At `Γ=0` the bound is identical, constant included; `Γ>0` only adds cost. | Exact LMO → LMO with summable additive errors. This relaxes the oracle, not the objective class. Finite-dimensional compact `C` → bounded convex `C` in a Hilbert space; in the proof, compactness only guarantees that the exact LMO exists. | None. Both give the last iterate and both need `τ` in the updates. Prop. 12 is `τ`-free but needs `L`. | Requires `Γ < ∞`, so a constant per-step error is excluded. |
| Freund–Grigas, *New Analysis and Results for the Frank–Wolfe Method*, Math. Program. 2016, [arXiv:1307.0873](https://arxiv.org/pdf/1307.0873), Thm 5.1 and Remark 5.1. Convex overlap (`τ=1`) only. | Arbitrary `δ_k`, curvature `≤ LD²`, steps `2/(k+2)`; the weighted error sum is `≤ kΓ`. This gives `O(1+(LD²+Γ)/ε)` → `O(1+(LD²+Γ)/ε)` | None: same order. The constant `6` here is no smaller than the convex constant. | Convex → `τ`-quasar-convex. The classes are nested, and Martínez-Rubio already covers the quasar extension for an exact LMO. | None: both give last-iterate gaps. | The prior result is broader in its error model (non-summable or constant `δ`). |

**Reduction check.** In Martínez-Rubio's proof of Thm 9 (App. C.2), step ② uses LMO optimality. Replacing it with `⟨∇f(x_i),v_i⟩ ≤ ⟨∇f(x_i),x★⟩ + δ_i` adds `(a_i/γ)δ_i = 2(i+1)δ_i/τ` to each `E_i`. Summing and dividing by `A_{t−1} = t(t+1)` gives exactly the extra term `2Γ/(τ(t+1))` in the Lean recurrence. This is the Freund–Grigas weighted-error accounting. The quasar step at `x_{t+1}` with the `LD‖x_{t+1}−x_t‖` correction (Lean `shifted_support`) is Martínez-Rubio's device. I found no new mechanism. These two papers are both proof ancestry and the direct competitors.

**Search coverage (2026-10-07 UTC).** I searched arXiv and the web for Frank–Wolfe under quasar-, star-, and weak-star-convexity with inexact LMOs. I read the theorem statements and proofs of Martínez-Rubio v3 Thm 9 and Prop. 12, and Freund–Grigas v2 §5. I checked the following from abstracts only, and none combines quasar-convexity with an inexact LMO:
- Díaz Millán–Ferreira–Ugon, [arXiv:2507.17272](https://arxiv.org/abs/2507.17272): star-convex, exact LMO.
- Hu, [arXiv:2601.11548](https://arxiv.org/abs/2601.11548): constant-`δ` errors, convex and nonconvex objectives.

I did not check Jaggi (ICML 2013) or the journal versions directly. There is no companion note. The local reference catalog lists "None" and misses Martínez-Rubio. The result was introduced in commit `b754121` on 2026-09-23, after both key sources. I found no later work on the identical setup. I ran no build or axiom check.

**Conclusion**

**No: this is a known Frank–Wolfe analysis plus routine error bookkeeping, and it improves no complexity.** The strongest baseline is Martínez-Rubio's Theorem 9, which uses the same algorithm, the same `2/(τk+2)` step, and the same last-iterate output for smooth quasar-convex problems over a convex set:

| | Oracle | Calls |
|---|---|---|
| Martínez-Rubio Thm 9 | exact LMO | `2⌈6LD²/(τ²ε)⌉` |
| This result | LMO, `Σδ_k ≤ Γ` | `2⌈(6LD²/τ² + 2Γ/τ)/ε⌉` |

At `Γ = 0` the two bounds coincide exactly. For `Γ > 0` the extra term follows from the prior proof by carrying the LMO error through one inequality. That is the weighted-error accounting Freund–Grigas already did for convex Frank–Wolfe.

The comparison shows that no regime gives better complexity, and no new class of objectives is covered. The only extensions are summably inexact LMOs and Hilbert-space domains, and both are routine. Separately, the literature search found no paper that states this exact combination. That shows only that the bookkeeping has not been written down, not that it is novel.

What can be claimed is an explicit inexact-LMO corollary of Martínez-Rubio's quasar Frank–Wolfe theorem, together with a Lean formalization.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
