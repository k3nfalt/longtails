# Novelty assessment: DistributedWeightedInterpolation

[Theorem](../../LongTails/Theorems/DistributedWeightedInterpolation.lean) · [Setup](../../LongTails/Setups/DistributedWeakInterpolation.lean) · [Algorithm](../../LongTails/Algorithms/WeightedInterpolationSgd.lean). In a coordinator–worker star, worker `i` holds a convex, `L_i`-smooth function `f_i`. The functions share a minimizer set `S` within distance `R` of `x0`, and their average has quadratic growth `μ` relative to `S`. Each stochastic-gradient call at worker `i` takes `h_i` seconds and returns an unbiased gradient with variance at most `σ²`. Under these assumptions, speed-weighted batched SGD returns the fixed-index iterate `x_{2J}` with `E dist(x_{2J},S)² ≤ ε` within the stated elapsed time.

**Proved elapsed time.** The meanings: `n` is the number of workers, `d` the dimension, `ℓ` the per-message latency and `b` the per-bit time. Choose `c ≥ 0` with `Σ_i min(L_i, c h_i) = nμ`. This implicit threshold is needed because the active set depends on the sorted ratios `L_i/h_i`. Put `u_i = min(L_i, c h_i)`, `I = Σ_i u_i²/h_i` and `κ = 2·max_i(u_i L_i)·Σ_j h_j⁻¹ / I`. Then

  T = O( σ²/(Iε) + κ·(1+log(1+R²/ε))·[max_i h_i + ℓ + b·d·log(2+d+κ+(R²+σ²max_i u_i²/max_i(u_iL_i)²)/ε)] ).

The bound always satisfies `I ≥ n²μ²/Σ_i h_i` (Cauchy–Schwarz). It requires `nμ ≤ Σ L_i`, `h_i > 0` and `ε > 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, Tyurin–Richtárik, NeurIPS 2023; restated as [Tyurin 2026, Thm F.2](https://arxiv.org/abs/2609.17483) (global PL with convexity, uniform average, no interpolation needed, free communication) | `[max h·L̄/μ + σ²Σh_i/(n²μ²ε)]·log(R²/ε)` with `L̄ = (1/n)ΣL_i` → `σ²/(Iε) + κ·max h·log(1+R²/ε)` (ℓ=b=0) | Statistical term divided by `IΣh_i/(n²μ²)·log(R²/ε) ≥ log`. When smoothness caps bind, the gain is up to `Θ((max h/min h)·log)`. Example: `L_i=L`, `h=(1,1,s)`, `μ=L/2`, `σ² ≫ L²ε` gives `Θ(s·log(R²/ε))`. | None (it uses its own QG/PL; weak interpolation is extra) | None (both are fixed-index iterate distance bounds) | Requires weak interpolation and public `L_i`. Startup `κ·max h` can exceed `max h·L̄/μ` by factors up to `max h·mean(1/h)` or `max L_i/L̄`. Communication is charged. |
| Standard reduction: Malenia on the best worker subset `T`, with guaranteed curvature `(nμ−Σ_{j∉T}L_j)/|T|` derived from public `L_i` | `σ²(Σ_T h)/(nμ−L(T^c))²·log + startup` → `σ²/(Iε)+…` | In the example above, same order up to `log(R²/ε)`. The note's example gives a `Θ(log N)` gain over prefixes. I found no general gap larger than logarithmic, and none is proved. | None | None | Same as above |
| Tyurin 2026, Thm 3.8 (strong interpolation + local PL, `L_max`) | `min_m (mean_{≤m} 1/h)⁻¹(L_max/μ + σ²/(mεμ²))·log` → as above | Not comparable: the classes are incomparable. The local-PL class is reached only when `nμ > ΣL − L_i` for all `i`. | Local PL and equal argmin sets → global QG and shared minimizer | None | When local QG is forced, Thm 3.8's harmonic rate matches up to log |
| Tyurin 2026, Thm 3.2 (lower bound; weak interp., global PL, `L_i=L_max`, `μ<L_max/(2n)`) | `Ω(σ²Σh/(n²μ²ε))` → in this regime `u_i` is uncapped, so `σ²/(Iε)` equals it | None: in this regime the result matches the lower bound, and Malenia already matches it up to log | The new upper bound covers `μ ≥ L_max/(2n)` and heterogeneous `L_i`, where the lower bound is silent | None | The note's matching lower bound outside this regime is not formalized |

**Reduction check.** In the uncapped regime the result reduces to Malenia-style batching plus SGD under QG; removing the log factor is a routine two-phase step schedule. What is new is the capped-profile weighting: it gives the biased surrogate `Σ w_i f_i` curvature `I` and unit-time variance `I` at once, and it is only partly reproduced by the subset reduction. Proof ancestry: Rennala/Malenia batching and the PL/QG SGD recursion supply the scaffolding, not this bound.

**Search coverage (2026-11-19).** I searched arXiv and NeurIPS/ICML/ICLR 2023–2026 on asynchronous/heterogeneous SGD, interpolation and worker weighting. I read Tyurin 2609.17483v1 (15 Sep 2026; Sections 1–3, Table 1 and App. F read; Remark 3.9 and §3.3–4 seen only in summary) and Rescaled ASGD 2605.13434v1 (nonconvex stationarity only; frequency-weighted objective, no QG result). I did not check Inkheart/M4. The result was introduced in commit `75dc6376` (2026-11-19), after both papers. The note's claims are consistent with Thm 3.2/3.8, but its `Θ(log N)` prefix example and its two-point lower bound were not independently verified.

**Conclusion**

**Yes, but only in the statistical term, and the gain over the strongest simple alternative appears to be logarithmic.**

The strongest prior end-to-end guarantee is Malenia SGD (Tyurin 2026, Thm F.2), which uses the uniform average. Using speed-weighted local gradients that respect the per-worker smoothness caps improves its statistical term:

  σ²·Σh_i/(n²μ²ε)·log(R²/ε)  →  σ²/(Iε),   I = min{Σa_i²/h_i : 0≤a_i≤L_i, Σa_i ≥ nμ}.

This can be a factor `Θ(max h/min h)` faster when slow workers' smoothness caps bind. That happens with heterogeneous `L_i`, or when `μ ≥ L_max/(2n)`, which lies outside Tyurin's lower-bound regime. Inside that regime the bound coincides with the known lower bound and with Malenia up to a log, so there is no gain there.

The weakness is that a standard reduction gets most of the improvement. Running Malenia on a well-chosen worker subset, with curvature computed from the public `L_i`, matched the new rate up to logarithms in my example. The note's own example shows only a `Θ(log N)` advantage over such prefixes. The startup term can also be worse by `max h·mean(1/h)` or `max L_i/mean L_i`.

What can be claimed is a new, formally executed upper bound for a weighting rule that interpolates optimally between subsets under weak interpolation with global quadratic growth. It is a genuine improvement over the uniform-average baseline, but over subset reductions it is modest: in the checked examples it is only logarithmic.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
