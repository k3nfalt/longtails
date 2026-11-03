# Novelty assessment: accelerated nonconvex stationarity with a Hessian-similar auxiliary function

[`result`](../../LongTails/Theorems/AuxiliarySimilarityAcceleration.lean) proves the following. Take a finite-dimensional `f` that is `C²` with a `ρ`-Lipschitz Hessian, and an auxiliary `h` (possibly nonconvex) with `L`-Lipschitz `∇h` such that `∇(f−h)` is `δ`-Lipschitz. Let `f(x₀) − inf f ≤ Δ`. With exact oracles `O_f = (f,∇f)` and `O_h = (h,∇h)`, the guarded three-level method ([setup](../../LongTails/Setups/AuxiliarySimilarityNonconvex.lean), [algorithm](../../LongTails/Algorithms/AuxiliarySimilarity.lean)) deterministically returns `x̂` with `‖∇f(x̂)‖ ≤ ε` within an explicit per-oracle budget.

**Simplified budget.** This is derived from `K, T, J, N` in `tuning`, assuming `δ > 0` and `ρ, ε > 0`:

```
#O_f = O( (1 + Δ√ρ ε^{-3/2}) · √(1 + δ/√(ρε)) · log(2 + δ/√(ρε)) · log(2 + (L+δ)/√(ρε)) )
#O_h = O( #O_f · (1 + L/δ) · [log(2 + (L+δ)/√(ρε)) + log(1 + Δ√ρ ε^{-3/2})] )
```

The leading `O_f` term is `√δ ρ^{1/4} Δ ε^{-7/4} · log·log`. `L` enters `#O_f` only through one logarithm. The updates need `L, δ, ρ, Δ, ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Chayti–Karimireddy, AuxMOM, [arXiv:2206.00395](https://arxiv.org/abs/2206.00395) (TMLR 2024), Thm 4.3 / Cor 4.4, noiseless case | `O(1 + δΔε^{-2})` `f`-gradients with `O(1+L/δ)` `h`-calls each → `O((1+Δ√ρε^{-3/2})(1+√δ(ρε)^{-1/4}) log(2+δ/√(ρε)) log(2+(L+δ)/√(ρε)))` | Factor `≈ √(δ/√(ρε)) / [log(2+δ/√(ρε)) log(2+(L+δ)/√(ρε))]` when `δ ≫ √(ρε)·log²` and `Δ√ρ ε^{-3/2} ≥ 1`. **Worse** when `δ ≲ √(ρε)·log²`. | None. AuxMOM needs no Hessian-Lipschitz assumption, so its class is broader. | Random/best-iterate `E‖∇f‖²` → deterministic returned point. With exact gradients the best iterate is already identifiable, so the gain is minor. | Needs `ρ`-Lipschitz Hessian of `f`, knowledge of `ρ` and `Δ`, and extra log factors and large constants (`2¹⁹`). The `h` cost per `f` call is comparable, up to logs. |
| Li–Lin restarted AGD ignoring `h`, [JMLR 24 (2023)](https://jmlr.org/papers/volume24/22-0522/22-0522.pdf) (ICML 2022), Thm 1; `f` is `(L+δ)`-smooth | `O(√(L+δ) ρ^{1/4} Δ ε^{-7/4})`, valid for `ε ≲ (L+δ)²/ρ`, no `O_h` calls → `O((1+Δ√ρε^{-3/2})(1+√δ(ρε)^{-1/4}) log(2+δ/√(ρε)) log(2+(L+δ)/√(ρε)))` | `√(L+δ)` → `√δ·log·log` when `L ≫ δ·log⁴` and `δ ≥ √(ρε)`. Factor `√((L+δ)/√(ρε))/log²` when `δ < √(ρε)`. **Worse by logs** when `L ≲ δ`. | None (same class, with `h` ignored) | None: both return a stopped point with `‖∇f‖ ≤ ε` | Requires the `O_h` oracle, `Õ(L/δ)` cheap calls per expensive call, and two log factors where Li–Lin is log-free |

**Not a direct competitor.** The companion note credits Chayti–Doikov–Jaggi ([arXiv:2302.11962v7](https://arxiv.org/abs/2302.11962)) with `O(Δ(√ρε^{-3/2}+δε^{-2}))`. I could not find that bound in their theorems:

- **Thm 3.3** uses a *uniform* helper-gradient error `δ₁` and converges only to a `δ₁`-neighbourhood.
- **Thm 3.6** assumes a Lipschitz *Hessian* of `f−h` and uses `∇²f` at snapshots together with Hessians of `h`, so it relies on a second-order oracle.

So that row is not comparable as cited. The nonconvex similarity methods I checked (DANE+, SCAFFOLD/CE-LGD; see [arXiv:2610.35663](https://arxiv.org/abs/2610.35663), a later work, for a survey) all have the form `(L/K + δ)Δ/R`, which is `δΔε^{-2}`-type. Accelerated similarity methods ([Kovalev et al., NeurIPS 2022](https://arxiv.org/abs/2205.15136); TIGER, [arXiv:2610.25504](https://arxiv.org/abs/2610.25504)) need convexity or relative strong convexity of the objective.

**Reduction check.** The obvious composition fails. It would run a Catalyst/accelerated proximal point method with prox parameter `≈δ` and apply accelerated similarity solvers to `f + δ‖·−v‖²`. That subproblem is nonconvex whenever `h` has curvature below `−δ`, so the convex black boxes do not apply.

**Proof ancestry, not baselines.**

- Carmon–Duchi–Hinder–Sidford's "convex until proven guilty" (ICML 2017) supplies the guard-and-exploit dichotomy.
- DANE viewed as relative smoothness (Lu–Freund–Nesterov 2018) and an inexact accelerated proximal point potential supply the inner levels.

The new step is transferring each failed inner guard, using only (S), into a negative-curvature certificate of `f` inside a localization ball. I found no prior instance of this step.

**Lower bound.** The deterministic `Ω(ε^{-7/4})` first-order lower bound [arXiv:2606.05438](https://arxiv.org/abs/2606.05438) (June 2026) exists. I did not verify its explicit `√δ ρ^{1/4} Δ` scaling or the cited randomized version (arXiv:2610.00245), so "optimal up to logs" remains unverified.

**Search coverage.** I searched on 2026-10-31: arXiv and NeurIPS/ICML/TMLR/JMLR sources on auxiliary/helper information, Hessian similarity (nonconvex and accelerated), gradient sliding, and `ε^{-7/4}` methods. I read the theorem text of Chayti–Karimireddy, Chayti–Doikov–Jaggi v7 and Li–Lin. I read only abstracts or summaries of TIGER, arXiv:2412.16414 and Luo et al. 2025 (the last assumes weak convexity). Git history dates the result to 2026-10-30, after all of the cited prior work.

## Conclusion

**Yes: in a specific regime the proved expensive-oracle complexity is better than the two strongest applicable first-order baselines.** Those baselines are Chayti–Karimireddy's AuxMOM, which uses `h`, and Li–Lin's restarted AGD, which ignores `h`.

| | expensive `∇f` calls |
|---|---|
| AuxMOM | `δΔε^{-2}` |
| Restarted AGD | `√(L+δ) ρ^{1/4}Δε^{-7/4}` |
| This result | `(√ρΔε^{-3/2} + √δ ρ^{1/4}Δε^{-7/4}) · log(2+δ/√(ρε)) · log(2+(L+δ)/√(ρε))` |

The gain over both baselines requires `√(ρε)·log² ≪ δ` and `δ·log⁴ ≪ L`. In words, the similarity constant must exceed the Hessian-Lipschitz curvature scale, and the auxiliary must be much rougher than the discrepancy. For example, with `ρ = Δ = δ = 1` and `L = ε^{-1/2}`, AuxMOM pays `ε^{-2}`, restarted AGD pays `ε^{-2}`, and this result pays `ε^{-7/4}log²(1/ε)`.

The result loses outside that regime. When `δ ≲ √(ρε)`, AuxMOM is better. When `L ≲ δ`, log-free AGD is better. In every regime the method needs the Hessian-Lipschitz assumption, knowledge of `ρ` and `Δ`, and `Õ(L/δ)` cheap calls per expensive call.

These gains follow from the comparison itself. Separately, the search found no prior `ε^{-7/4}`-type guarantee under similarity with a nonconvex auxiliary, and the obvious reduction fails, but absence from the search is not proof of priority. The companion note misstates the Chayti–Doikov–Jaggi comparison, and its optimality claim is unverified in its parameter dependence. What can be claimed is the first checked accelerated expensive-oracle bound, `√δ` in place of `√(L+δ)` or `δ/ε^{1/4}`, for nonconvex stationarity with a cheap, possibly nonconvex, Hessian-similar auxiliary.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
