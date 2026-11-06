# Novelty assessment: SpikedSubGaussianSoftCutConvex

[`result`](../../LongTails/Theorems/SpikedSubGaussianSoftCutConvex.lean) proves the following. Take a convex, globally `G`-Lipschitz `f` on `ℝ^d` (`d=m+1`) with a global minimizer `‖x⋆‖≤R`. Give it an unbiased, fresh-IID stochastic subgradient oracle whose directional MGF has proxy `v_rest‖u‖² + (v_top−v_rest)u₀²`, with `0≤v_rest≤v_top` and a known spike direction `e₀` ([setup](../../LongTails/Setups/SpikedSubGaussianConvex.lean)). Under these assumptions the [soft-cut/outer-bisection method](../../LongTails/Algorithms/SpikedSoftCutMethod.lean) returns `x̂` with `P{f(x̂)−f(x⋆)>ε} ≤ 1/3`.

**Proved complexity.** The calls are deterministic. Here `G` is the Lipschitz constant, `R` the minimizer radius, `ε` the accuracy, and `v_top`, `v_rest` the spike and background proxies:

  N = O( (d + (v_top + (d−1)v_rest) R²/ε²) · [1 + log(16d(1+GR/ε))]⁵ ),

valid for `G,R,ε>0`. The exact budget has the constant `2^51`, and `v_top+m·v_rest` is the proxy trace `τ`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Marsden–O'Carroll–Sidford–Zhang, [arXiv:2510.20745v1](https://arxiv.org/abs/2510.20745), NeurIPS 2025, Cor. 3 (ESGO). Applies via directional sub-exp scale `σ_E≍√(d·v_top)`. | `Õ(d + d·v_top R²/ε²)` → `O((d + (v_top+d·v_rest)R²/ε²)·log⁵(d(1+GR/ε)))` | Factor `≈ d·v_top/(v_top+d·v_rest)` on the noise term. It survives when `v_rest ≪ v_top`, `v_top R²/ε² ≫ log⁵(·)·polylog`, and the noise term dominates `d`. | Isotropic directional bound → one known spike plus background. On their common class the new result is an extension, not a relaxation. | None: both give a probability-2/3 point guarantee and need the noise parameters. | Spike direction must be known. Needs a subGaussian MGF (MOSZ needs only a sub-exp tail). Explicit `log⁵`. At `v_rest=v_top` the order is the same. |
| SGD / mirror descent, [Nemirovski et al. 2009](https://doi.org/10.1137/070704277) §2.2, plus Markov. Uses `E‖g‖² ≤ G²+τ`. | `O((G²+v_top+(d−1)v_rest)R²/ε²)` → same bound as above | Removes the `G²R²/ε²` term, at the price of an additive `d`. Wins when `G²R²/ε² ≫ max(d, τR²/ε²)·log⁵(·)`. | None (SGD covers this class and more: finite variance, no spike). | None | SGD needs only finite variance and costs no `log⁵`. It wins when `G²R²/ε² ≲ d`. |
| Repository [CovarianceSoftCutConvex](../../LongTails/Theorems/CovarianceSoftCutConvex.lean) (2026-10-29). Applies via covariance `≼ v_top I`, i.e. `σ²=d·v_top`. | `O((d + d·v_top R²/ε²)·log⁵(16d(1+LR/ε)))` → above | Same factor and regime as the MOSZ row. | Same as the MOSZ row. | None | That result needs only finite covariance, with no MGF condition. |

The example from the note checks out: `G=R=1`, `ε=1/d`, `v_top=1/d`, `v_rest=d⁻³`. The new bound is `O(d log⁵d)`; SGD and MOSZ both give `Θ̃(d²)`.

**Reduction check.** Whitening `e₀` turns the spike into isotropic noise but stretches the domain to a cylinder `[−cR,cR]×B(R)` with `c²=v_top/v_rest`. The directional accuracy MOSZ cuts need then scales with that long axis, so their batch size goes back to `v_top R²/ε²` per cut. Plain volume-based cutting planes do not control width along `e₀`. Nesting MOSZ inside a 1-D search also fails: an approximate section minimizer gives no reliable outer slope for nonsmooth coupled `f`. The new mechanism is a noise-robust certificate built from data-selected weights. It bounds the weighted true-subgradient average `Σwᵢ⟨vᵢ,xᵢ−y⟩ ≤ ε/16` over the ball, and fresh scalar sampling then certifies the outer slope. I did not find this step in prior work. Proof ancestry: the MOSZ / Sidford–Zhang stochastic cutting-plane idea (accurate only in the direction toward `x⋆`), the repository's soft-cut generator, minimax duality, and the certificate notions of Gladin–Gasnikov–Dvurechensky (JOTA 2025). None of these alone gives the bound.

**Search coverage (2026-11-06 UTC).**
- I read MOSZ's Defs. 3–5, Thm. 1, Cors. 3–4, Thm. 5 and Open Problem 1 from arXiv v1; v1 is the only version.
- I searched arXiv, NeurIPS, ICML and ICLR for anisotropic, spiked and low-rank noise and for follow-ups to MOSZ Open Problem 1 (`Õ(d+σ_V²R²/ε²)`). I found no prior or later work covering this setup.
- I did not verify the note's other recent preprints (Gladin 2610.11448, Grimmer–Wang 2607.20875, Zhang et al. 2610.00260, Bullins et al. 2609.20687).
- MOSZ's lower bound (Thm. 5) uses its own hard noise. I did not check that it applies to Gaussian background noise, so optimality is not claimed.
- The note's claims agree with the Lean statement.

**Conclusion**

**Yes: in an explicit anisotropic regime the proved complexity is polynomially better than every bound I checked, but only for a narrow noise model.** The strongest baselines are Marsden–O'Carroll–Sidford–Zhang's isotropic-noise cutting-plane bound (NeurIPS 2025) and SGD:

| | oracle calls (up to logs) |
|---|---|
| MOSZ / repo covariance method | `d + d·v_top R²/ε²` |
| SGD | `(G² + v_top + d·v_rest) R²/ε²` |
| this result | `(d + (v_top + d·v_rest) R²/ε²)·log⁵(d(1+GR/ε))` |

The gain is up to a factor `d` (in the example above, `d²` → `d log⁵ d`). It needs background noise far below the spike (`d·v_rest ≪ d·v_top`) and `G²R²/ε² ≫ d`. Under isotropic noise there is no gain. When `G²R²/ε² ≲ d`, SGD is better and needs only finite variance.

That comparison shows the gain. Separately, my search found no earlier or later paper with this bound, but that is not proof of priority.

The gain is limited because the model is narrow. It needs exactly one spike, in a direction known in advance, with subGaussian tails. It is a special case of the open trace-variance question, not a solution to it, and the motivation for a single known dominant direction is plausible but not tied to a concrete application. The solid claim is a new certificate-based method that achieves trace-scale noise cost with an additive `d` for known one-spike subGaussian noise.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
