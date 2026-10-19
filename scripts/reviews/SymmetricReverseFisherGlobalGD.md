# SymmetricReverseFisherGlobalGD: novelty assessment

[Theorem](../../LongTails/Theorems/SymmetricReverseFisherGlobalGD.lean) · [Setup](../../LongTails/Setups/SymmetricGaussianReverseFisher.lean) · [Algorithm](../../LongTails/Algorithms/SymmetricReverseFisherGD.lean)

Given exact gradients of the population reverse Fisher divergence `F_μ(θ) = E_{X∼p_θ}‖s_θ(X) − s_μ(X)‖²`, where `p_θ = ½N(θ,I) + ½N(−θ,I)` in `ℝ^d`, constant-step GD `θ⁺ = θ − ∇F_μ(θ)/(48+20B)`, started from a normalized uniform-cube point, has a last iterate satisfying `min ‖θ_K ∓ μ‖² ≤ ε` with probability `≥ 1−δ`.

**Proved budget.** `d` is the dimension, `s ≤ ‖μ‖ ≤ B` are the supplied signal bounds (`s = 0` allowed), `ε ∈ (0,1]` is the squared-distance accuracy, and `δ ∈ (0,1]` is the failure probability:

  K = O( (1+B)(1+s²)/max(s², ε) · log(d(1+B)/(δε)) )  exact-gradient calls  (the leading constant is 10¹⁵).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Two-call method in the setup's own `gdFamily`, using the same oracle (standard reduction, derived below) | `2` → `O((1+B)(1+s²)/max(s²,ε) · log(d(1+B)/(δε)))` | **Worse** for every admissible parameter value, by a factor of at least `(1+B)/max(s²,ε) · log(d(1+B)/(δε))`. | None | None. Both methods return the last iterate. The two-call method recovers `±μ` exactly with probability 1 and needs only `d`. | The selected method uses a constant step and must know `B`, `s`, `ε`, and `δ` to set its budget. The two-call method uses state-dependent steps and exact evaluation of known 1-D Gaussian integrals. |
| Tyurin, [arXiv:2606.19876v1](https://arxiv.org/abs/2606.19876) (18 Jun 2026; preprint), Thm 3.2/E.1. **Restriction:** untied student means and teacher separation `≳ √log(…/ε)` | `Õ(n²/ε) = Õ(1/ε)` for `n = 2` (large-sphere initialization, step `Θ̃(n)`) → this result's `O((1+B)(1+1/s²) · log(d(1+B)/(δε)))` when `s² ≥ ε` | Not comparable: different student parameterizations. Within the separated overlap, the dependence on accuracy is `log(1/ε)` instead of `1/ε`. | Separation `≳ √log(1/ε)` → none, including `μ = 0`. Untied means → tied `±θ`, which is narrower. | Tyurin's guarantee holds at all `k ≥ K̃`. This result covers one fixed last iterate. | Two equal-weight, antipodal components only. Tyurin allows `n` students and `m` teachers. |
| Tyurin, same paper, Thm 2.1/Cor 2.5 (single-Gaussian teacher, arbitrary initialization). **Restriction:** covers only `μ = 0` | `O(log n · max{log(nR₀²/ε), n·min(n,d)/ε}) = O(1/ε + log(R₀²/ε))` for `n = 2` → `O((1+B)/ε · log(d(1+B)/(δε)))` at `s = 0` | Worse at the overlap `μ = 0`, by the factor `(1+B)·log(d(1+B)/(δε))`. | Single teacher → all `μ` with `‖μ‖ ≤ B` | None | Tied student; deterministic guarantee → probability `1−δ` with `log(d/δ)` cost |

**Reduction check.** The proof's own lemmas give `∇F_μ(θ) = α(‖θ‖)θ − ridgeForce(‖μ‖,⟨θ,μ⟩)μ` with the following properties:
- The coefficient `α ≥ min(r²,1)/120` is a known function, independent of `μ`.
- The ridge force has the sign of `c`, and `radialForce(a,r) = a·ridgeForce(a,ar)` is strictly increasing in `a` (`radialForce_increment_lower`).
- On the ray `u·e`, the gradient is `alignedForce(a,u)·e`, with sign `sign(u−a)`.

With the start at `‖θ₀‖ = 1` and step `1/α(1)`, one call yields `v = ridgeForce·μ`. This identifies `e = v/‖v‖ = ±μ/‖μ‖` and moves the iterate onto the ray. Solving `radialForce(a,⟨θ₀,e⟩) = ‖v‖` gives the norm `a = ‖μ‖`. A second positive step `(t₁−a)/alignedForce(a,t₁)` lands exactly on `±μ`. The case `a = 0` gives `θ₁ = 0`. This satisfies `gdFamily`, because each step depends only on the stored state. I checked this sketch against the Lean lemmas but did not formalize it. The selected proof's genuine technical content (`∂ₐK ≥ min(a,1)min(r,1)/60` via a sign-changing kernel, cone invariance, and escape from small radius) is proof ancestry for the *dynamics of constant-step GD*. It is not a better oracle complexity. Tyurin's Lyapunov analysis is the closest ancestor. Shah–Chen–Klivans ([NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/hash/3ec077b4af90f2556b517b556e186f64-Abstract-Conference.html)) use the forward DDPM objective with sample access. Population EM ([Daskalakis–Tzamos–Zampetakis, COLT 2017](https://arxiv.org/abs/1609.00368)) and [Wu–Zhou](https://doi.org/10.4171/MSL/29) use different oracles. Neither is a table baseline.

**Search coverage (2026-10-19 UTC).** I searched arXiv and the web for reverse/model-based Fisher divergence, score matching on Gaussian mixtures, and GD/EM for symmetric two-component mixtures. I read the Tyurin v1 theorem statements in HTML and confirmed Shah et al.'s NeurIPS status, but did not re-read their supplementary theorems. The search found no prior separation-free analysis of reverse-Fisher GD in the tied model. The companion note correctly disclaims any problem-class improvement. However, it implies that the `gdFamily` restriction makes the GD analysis the relevant competitor, and it omits that this same family already admits a two-call solution.

## Conclusion

**No optimization advantage: the same oracle, even restricted to the setup's GD family, solves this problem in two calls.** The decisive comparison is with an adaptive-step GD method built from the proof's own gradient identities:

| Method (same exact-gradient oracle, `gdFamily`) | Calls for `min‖θ∓μ‖² ≤ ε` |
|---|---|
| Two-step adaptive GD (this review) | `2`, exact recovery with probability 1 |
| Selected constant-step GD | `O((1+B)(1+s²)/max(s²,ε) · log(d(1+B)/(δε)))` |

Because a single exact gradient reveals both the direction and the norm of `μ`, the selected budget is worse in every regime. Against Tyurin's June 2026 constant-step analysis, the result removes the `√log(1/ε)` separation requirement and gives logarithmic accuracy dependence. That gain holds only for a tied two-component student, so the parameterizations differ and no rate comparison is valid.

What can be claimed is a new, apparently unpublished description of the *dynamics* of constant-step GD on this reverse-Fisher objective for weakly separated symmetric mixtures, which is relevant to understanding score training. That is an analysis of a fixed method. It is not a better complexity, a broader solvable problem class, or an improved output guarantee. My literature search found no competing analysis, but it does not prove priority.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
