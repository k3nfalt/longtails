# Novelty assessment: NonEuclideanWeakMintyExtragradient

[`result`](../../LongTails/Theorems/NonEuclideanWeakMintyExtragradient.lean) proves the following. Let `E` be a finite-dimensional space with an arbitrary norm, and let `F : E → E*` be `L`-Lipschitz (primal norm to dual norm). Assume `F` has a root `x⋆` satisfying `⟨F(x),x−x⋆⟩ ≥ −ρ‖F(x)‖*²` for every `x`, with `0 ≤ ρ ≤ 1/(20L)`, and fix a differentiable mirror `h` with `D_h(u,x) ≥ (μ/2)‖u−x‖²` (no gradient-Lipschitz assumption) ([setup](../../LongTails/Setups/NonEuclideanWeakMinty.lean)). The [norm-steepest predictor / Bregman-corrector method](../../LongTails/Algorithms/NonEuclideanExtragradient.lean) uses exact `F` calls and returns the queried base point with the smallest residual, which satisfies `‖F(x_out)‖* ≤ ε`.

**Complexity.** Here `L` is the Lipschitz constant, `μ` is the mirror's strong-convexity modulus, `D ≥ D_h(x⋆,x₀)` bounds the initial Bregman distance, and `ε` is the dual-norm residual target. The Lean budget is exactly `2+2⌈400L²D/(με²)⌉` operator calls, that is,

  `O(1 + L²D/(με²))`, valid for `ρL ≤ 1/20`.

I checked the step lemma by hand. With `a=‖F(x)‖*`, the predictor gives `⟨F(y),x−x⋆⟩ ≥ 11a²/(80L)` and `‖F(y)‖* ≤ 3a/2`, and the step `η=μ/(10L)` then gives `D_h(x⋆,x⁺) ≤ D_h(x⋆,x) − μa²/(400L²)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Zhang–Dai, arXiv:2108.12070v2](https://arxiv.org/abs/2108.12070), Thm 2 with Lemma 3 (`λ=L/μ₀`). Prior. Requires a mirror that is both `μ₀`-strongly convex and `L₀`-smooth. Their `ρ` is twice ours. | Halving their threshold, `ρ ≤ μ₀²/(16LL₀)`: `O(1+L₀L²D/(μ₀³ε²))` → `O(1+L²D/(μ₀ε²))` | Factor `L₀/μ₀`, i.e. the mirror's condition number. Euclidean conversion of a norm with distortion `A` (`‖x‖≤\|x\|≤A‖x‖`, `ω=½\|x−x₀\|²`) gives `L₀/μ₀=A²`. Example: spectral norm on `m×n` matrices with the Frobenius mirror gives `A²=r=min(m,n)`, so the bound improves from `rL²‖X⋆−X₀‖_F²/ε²` to `L²‖X⋆−X₀‖_F²/ε²`. The gain survives constants once roughly `A² ≳ 13`. | Allowed `ρL`: `≤ μ₀²/(16L₀)` (i.e. `1/(16A²)`) → `1/20`, independent of geometry. Mirror: smooth → merely differentiable and strongly convex (e.g. `½‖·−x₀‖_p²` for `1<p<2`). | None (both best iterate, same residual) | In the Euclidean case (`A=1`) the range is narrower: `ρL ≤ 1/20` vs `<1/8` for both Zhang–Dai and DDJ. Larger constants (`800` vs `64`). |
| [Diakonikolas–Daskalakis–Jordan, AISTATS 2021 / arXiv:2011.00364](https://arxiv.org/abs/2011.00364), Thm 3.2 (EG+). Prior. Euclidean special case only. | With `R=‖x⋆−x₀‖₂`, `ρL ≤ 1/20` (their `ρ=2ρ`): `O(1+L²R²/ε²)` → `O(1+L²R²/ε²)` | None: same order | None on the overlap | None | DDJ allow `ρL<1/8` in our convention. [Pethick et al., ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf) allow a still wider Euclidean range. |
| Same paper, Thm 4.2(i). Prior. `ℓ_p`, `1<p≤2`, **ρ=0 only**. | With `R_p=‖x⋆−x₀‖_p`, `h=½‖·−x₀‖_p²` (`μ=p−1`, `D=R_p²/2`): `O(1+L²R_p²/((p−1)²ε²))` → `O(1+L²R_p²/((p−1)ε²))` | Factor `1/(p−1)` at `ρ=0` | `ρ=0` → `ρL ≤ 1/20`. Remark 4.3 there calls `ρ>0` "significant technical obstacles". | None | None found beyond constants |
| Cutting-plane reduction (center of gravity on the predictor's separating halfspace; derived in the companion note and rechecked here). Not a published theorem. | `O(1+d·log(1+LR/ε))` (ambient dimension `d`, `‖x⋆−x₀‖≤R`) vs `O(1+L²D/(με²))` | Worse when `L²D/(με²) ≫ d·log(LR/ε)`. Better in high dimension at moderate accuracy. | None | None | Cutting planes need `R` and heavy arithmetic per step, but they win on oracle calls in low dimension. |

**Reduction check and mechanism.** Every route I checked loses something. A Euclidean change of norm, or plugging into Zhang–Dai/Dang–Lan, loses the factor `A²` (or `L₀/μ₀`) in both the rate and the allowed `ρ`. [Dang–Lan, COAP 60 (2015), Thm 4.3(b)](https://arxiv.org/abs/1311.2776) covers only `ρ=0` and also needs a smooth mirror to control the dual residual. [Song et al.'s OptDE, arXiv:2103.04410](https://arxiv.org/abs/2103.04410), Thm 1, also covers only `ρ=0` and uses `½‖·‖²` as the mirror.

The new step is to measure alignment in the native dual norm, using the norming direction `J(F(x))`, before the mirror correction. This avoids converting displacement into residual, which is exactly the obstacle described in DDJ Remark 4.3. The descent/telescoping argument afterwards is the classical hyperplane-projection argument.

**Search coverage.** On 2026-10-20 (UTC) I read the theorem statements of DDJ, Dang–Lan, Zhang–Dai, OptDE, and [Alizadeh et al., arXiv:2405.10735v3](https://arxiv.org/abs/2405.10735), whose Assumption 5 also requires a Lipschitz mirror gradient. I also ran arXiv/proceedings searches through 2026. [Vyas–Bullins, arXiv:2603.13491](https://arxiv.org/abs/2603.13491) (March 2026) still describes first-order `ℓ_p` weak-MVI guarantees as limited to `ρ=0`. I did not read Lee–Kim SA-MGDA in full. The companion note cites DDJ "Remark 4.2" (it is 4.3 in the arXiv version) and Zhang–Dai "Theorem 5.2" (Theorem 2 in arXiv v2). The result entered the repository in commit `865fd38` (2026-10-20). I found no repository result in the same setting; `FullRangeSecondOrderWeakMinty` is Euclidean and second-order.

**Conclusion.**

**Yes. Outside nearly Euclidean norms, this is a better first-order weak-Minty guarantee: it allows a geometry-independent `ρ` and has a smaller complexity.** The strongest applicable prior result is Zhang–Dai's mirror extragradient. It needs a smooth mirror, and its bound and allowed `ρ` both degrade with the mirror's condition number `L₀/μ₀`:

| | allowed `ρL` | residual calls |
|---|---|---|
| Zhang–Dai (smooth mirror) | `≤ μ₀²/(16L₀)` | `O(1+(L₀/μ₀)·L²D/(μ₀ε²))` |
| this result | `≤ 1/20` | `O(1+L²D/(με²))` |

For the spectral norm on `m×n` matrices with the Frobenius mirror, `L₀/μ₀=min(m,n)`. The result therefore saves a factor `min(m,n)` in calls and covers `min(m,n)` times larger `ρ`. It also covers mirrors without Lipschitz gradients, such as `ℓ_p` with `1<p<2`, where earlier first-order results required `ρ=0`.

The result gives nothing new in the Euclidean case: there it matches DDJ's `O(L²R²/ε²)` with a narrower `ρ` range. In low dimension, cutting planes need fewer oracle calls. I did not verify that every smooth mirror for spectral geometry must have condition number of order `min(m,n)`, and I did not exhaustively check the non-Euclidean weak-MVI literature, so priority rests on a search, not a proof.

What can be claimed is the first checked dimension-free, first-order ordinary weak-Minty residual guarantee in a general norm with a non-smooth-gradient mirror. It removes the geometry-dependent restriction on `ρ`, using a simple native-norm predictor.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
