# Novelty review: MeanSquaredSmoothPLUpperBound

[`result`](../../LongTails/Theorems/MeanSquaredSmoothPLUpperBound.lean) proves that restarted, stage-wise SARAH ([algorithm](../../LongTails/Algorithms/StagewiseSarah.lean)) outputs a last iterate with `E[f(X)] − f⋆ ≤ ε`. The setting is the [MeanSquaredSmoothPL](../../LongTails/Setups/MeanSquaredSmoothPL.lean) setup: any separable Hilbert space, an `L`-smooth global `μ`-PŁ objective with attained minimum and `f(x₀) − f⋆ ≤ Δ`, and an IID same-sample pair oracle `(x,y) ↦ (g(x,ξ), g(y,ξ))` that is unbiased, has variance at most `σ²`, and satisfies `E‖g(x,ξ) − g(y,ξ)‖² ≤ L̄²‖x−y‖²`. The algorithm needs `L, L̄, μ, σ, Δ, ε`.

**Proved budget (pair queries, deterministic).** The budget is `⌈640(κ log₂(1+Δ/ε) + s² + min{κs², κ̄s})⌉` with `κ = L/μ`, `κ̄ = L̄/μ`, `s = σ/√(με)`. In the original parameters:

  N = O( 1 + (L/μ)·log(1+Δ/ε) + σ²/(με) + min{ Lσ²/(μ²ε), L̄σ/(μ^{3/2}√ε) } ),  valid for 0 < μ ≤ L ≤ L̄, σ, Δ ≥ 0, ε > 0.

Here `L` is the smoothness of `f`, `L̄` the mean-squared smoothness of the oracle, `μ` the PŁ constant, `σ²` the variance, `Δ` the initial gap, and `ε` the target accuracy. I checked [`schedule`](../../LongTails/Algorithms/StagewiseSarah.lean) and [`cost_schedule_le`](../../LongTails/Proofs/StagewiseSarahCost.lean). Stage `j < ⌈log₂(Δ/ε)⌉` uses batch `b_j ≍ σ²2^j/(μΔ)` and runs either mini-batch GD or SARAH epochs, so it costs `O(κ + b_j + min{κb_j, κ̄√b_j})`. Summing over stages gives the bound. When `Δ ≤ ε` there are no stages and the output is `x₀`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| PAGE, Li–Bao–Zhang–Richtárik, ICML 2021, [Thm 6 / Cor 7](https://arxiv.org/abs/2008.10898) (online PŁ, average smoothness) | `O((1 + σ²/(με) + (L̄/μ)(1+σ/√(με))) log(2Δ/ε))` expected stochastic gradients (the batch is `⌈2σ²/(με)⌉`; smoothness is `L̄` throughout) → `N` | **Log factor.** When `σ/√(με) > L̄/L` and `σ²/(με) + L̄σ/(μ^{3/2}√ε) ≥ (L/μ)log(Δ/ε)`, the gain is a factor `≍ log(Δ/ε)`. When `σ/√(με) ≤ L̄/L`, the gain over PAGE comes from `κ̄ → κ`, but mini-batch SGD already achieves this (next row). | None | None (both are last-iterate). The cost here is deterministic; PAGE's is in expectation. | None |
| SGD, Khaled–Richtárik, [arXiv:2002.03329, Thm 3 / Cor 2](https://arxiv.org/abs/2002.03329) (A=0, B=1, C=σ²) | `O((L/μ)log(2Δ/ε) + Lσ²/(μ²ε))` single-point calls → `N` | When `σ/√(με) ≤ L̄/L`: None, same order. Otherwise the noise term drops from `κs²` to `s² + κ̄s`, which is the variance-reduction gain already known from PAGE. | None | None | Uses a pair oracle and needs mean-squared smoothness. SGD needs only single points and no MSS. |
| Stage-wise SMVR, Jiang–Wang–Wang–Zhang–Yang, ICML 2022, [Thm 2 / Lemma 1](https://arxiv.org/abs/2202.07530) (*special-case baseline*: Lipschitz `f`, `L`/`σ` suppressed) | `O(1/(με) + 1/(μ^{3/2}√ε))` in `μ, ε` only (requires `ε ≲ μ`) → `N` | Not comparable: the `L, σ` constants are unspecified. This baseline already has no log factor on the noise terms. | It removes the Lipschitz-`f` (bounded-gradient) requirement. | None | None |
| STORM, Jiang et al., [arXiv:2610.01599v1 (Oct 2026, preprint), Thm 2 two-phase](https://arxiv.org/abs/2610.01599) | `O((L̄/μ)² log((Δ+σ²/μ)/ε) + σ²/(με))` single-sample pairs → `N` | `κ̄² log → κ log + min{κs², κ̄s}`. This is never worse up to constants, since `κ̄s ≤ (κ̄²+s²)/2`. The gain is polynomial when `L̄σ/√(με) ≪ L̄²/μ`, i.e. `s ≪ κ̄`. | None | None (both are last-iterate). | It needs anchor batches up to `≍ σ²/(με)`. STORM uses no batches. |

**Standard-reduction check.** I composed known results stage by stage, with targets `ε_j = Δ/2^j`:
- In each stage, run either PAGE (Thm 6, initial-to-target gap ratio 2, batch `⌈2σ²/(με_j)⌉`), costing `O(κ̄ + b_j + κ̄√b_j)`, or Khaled–Richtárik SGD, costing `O(κ + κb_j)`, whichever is cheaper.
- Summing the geometric series gives `O(κ log(Δ/ε) + s² + min{κs², κ̄s})`. Whenever PAGE is the cheaper choice, its extra `κ̄` term is absorbed by `κ̄√b_j`.

This reproduces `N` up to constants. A Lean proof of this route would need PAGE's Theorem 6 applied from a random start, which I did not check line by line. This geometric-batch restart scheme is the standard one, used for example in PAGER ([Fatkhullin et al., NeurIPS 2022](https://arxiv.org/abs/2210.01748); its Thm 2 covers only `α < 2`) and stage-wise SMVR. The one-step potential `Ψ_t` is a proof device, not a new mechanism.

**Search coverage.** Searched on 2026-11-24. I read the theorem statements in: PAGE; PAGER; Khaled–Richtárik; SpiderBoost App. C; ProxSVRG+ §5; Geom-SARAH Thm 5 ([arXiv:2002.05359](https://arxiv.org/abs/2002.05359)); and both Jiang et al. papers. The ProxSVRG+, SpiderBoost and Geom-SARAH PŁ rates all carry `log(1/ε)` on every term. I did not read SNVRG under PŁ or RECOVER ([arXiv:2006.10138](https://arxiv.org/abs/2006.10138)) in detail. The result was introduced in commit `3f7c10e3` (2026-11-24). The companion note calls the bound "routine", which agrees with this assessment, but it omits the log-free stage-wise SMVR/STORM PŁ results. No repository result overlaps (GdPL is deterministic). I ran no build or audit.

## Conclusion

**No new complexity is established: the bound follows from restarting known methods.** The closest prior result is PAGE (ICML 2021), and the theorem's gain over it is a logarithm.

| | Complexity (pair queries / gradients) |
|---|---|
| PAGE | `(1 + s² + κ̄(1+s))·log(Δ/ε)` |
| This result | `κ·log(1+Δ/ε) + s² + min{κs², κ̄s}` |

When the noise is large (`σ/√(με) > L̄/L`) and the noise terms dominate `κ log(Δ/ε)`, the proved total is smaller by a factor of about `log(Δ/ε)`. When the noise is smaller, the bound matches SGD (Khaled–Richtárik) and is never worse.

The improvement comes from mechanical steps. Running PAGE or SGD with geometrically shrinking targets, picking the cheaper method in each stage, and summing gives the same formula up to constants. Removing the log factor from the noise terms by staging is already present in stage-wise SMVR (ICML 2022), although that result suppresses `L, σ` and assumes a Lipschitz `f`. I did not find this exact two-parameter formula stated anywhere, so the literature search does not show it is old. But the reduction shows it is a routine corollary.

What can be claimed is a clean, fully explicit, formally verified statement of the log-free PŁ rate with separate `L` and `L̄`. Its value lies mainly as the upper half of the companion lower bound.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
