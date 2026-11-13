# Safe stochastic KKT points under uniform near-active MFCQ

[`result`](../../LongTails/Theorems/SafeStochasticMfcqKkt.lean) ([setup](../../LongTails/Setups/StochasticMfcqInequalities.lean), [algorithm/output](../../LongTails/Algorithms/StochasticMfcq.lean)) proves this: for smooth nonconvex `min f` s.t. `c_i(x) ≤ 0` (`m ≥ 1`, any finite dimension), with IID same-sample paired oracles returning noisy `(∇f, c, J)`, the returned `(x, λ)` satisfies `λ ≥ 0`, `c(x) ≤ 0` exactly, `‖∇f + Jᵀλ‖ ≤ ε` and `Σ|λ_i c_i| ≤ ε`, all with probability `≥ 1−ρ`. A supporting lemma, `execution_guarantee` in [StochasticMfcqGuarantee](../../LongTails/Proofs/StochasticMfcqGuarantee.lean), proves on the same event that **every queried point is feasible**. The public `Convergence` statement asserts only output accuracy.

**Parameters.** `H ≥ 1` bounds the Lipschitz constants of `∇f` and `J` (global), and bounds `‖∇f‖` and `‖J_i‖` at feasible points. `μ ≤ H`, `τ` give the MFCQ: at every feasible `x` there is a direction `‖z‖ ≤ 1` with `⟨∇c_i, z⟩ ≤ −μ` whenever `c_i(x) ≥ −τ`. `Δ` bounds `f(x₀) − f` over the feasible set, and `x₀` may lie on the boundary. `σ²` bounds the joint variance at feasible points. `L` is the joint mean-square smoothness of paired differences. With `e = min{ε, 1, τ}`, the proved budget in paired requests is

```
O( [1 + (H³Δ + H²σ²)/(μ²e²) + σL/(μe) + H³ΔσL/(μ³e³)] · [1 + log((1 + H³Δ/(μ²e²))/ρ)] )
```

Each request costs ≤ 6 vector primitives (two each of `∇f`, `c`, `J`), or `(2+4m)` scalar rows. If `ε ≤ min{1, τ}`, the leading term is `H³ΔσL/(μ³ε³)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| LB-SGD, Usmanova et al., [JMLR 25 (2024)](https://www.jmlr.org/papers/volume25/22-0878/22-0878.pdf), Thm 8 (prior) | `O(ε⁻⁷)` one-point value+gradient calls; the constants in `β, ρ, l, M, L, σ` were not extracted → `Õ(H³ΔσL/(μ³ε³) + (H³Δ+H²σ²)/(μ²ε²))` | ε-exponent 7 → 3 where both theorems apply: paired mean-square-smooth sub-Gaussian oracle, start margin `β > 0`, bounded domain, and `ε ≤ min{1, τ}` | Start margin `max f_i(x₀) ≤ −β` → boundary start allowed. Sub-Gaussian noise → finite variance. Bounded diameter (Asm. 1) → not needed | Componentwise complementarity → sum complementarity. Both are high-probability and both guarantee safe iterates | Needs a **paired same-sample** oracle with mean-square smoothness `L`, which LB-SGD does not. Smoothness must hold globally, not just on `X`. All parameters must be known |
| SafePD, Usmanova–Levy, [arXiv:2505.09349v1](https://arxiv.org/abs/2505.09349) (May 2025, preprint), Thm 17. **Applies only to `m = 1`** | `O(1/(ε⁶θ))` samples (θ is its MFCQ band) → bound above | At `m = 1`, under the paired oracle: ε⁻⁶ → ε⁻³ | `m = 1` → any `m`, including redundant rows. Start margin `α > 0` → none | None beyond complementarity form | Same paired-oracle and global-smoothness requirements as the LB-SGD row. Its SafePD* (max-smoothing) multi-constraint variant is `Õ(ε⁻⁷)` |
| Shi–Wang, [arXiv:2511.03210v2](https://arxiv.org/abs/2511.03210) (Nov 2025, preprint), Thm 7. Covers `c(x) = 0, x ≥ 0`; inequalities reach it only via slacks | `Õ(ε⁻³)` gradients + `Õ(ε⁻⁵)` constraint values → `Õ(ε⁻³)` requests, values included | Value calls ε⁻⁵ → ε⁻³, on the slack overlap only (unverified) | Incomparable classes. The slack form needs its strong MFCQ at every bound-feasible point, including `s = 0`, i.e. a common descent direction for all rows at every `x`. Its noise is a.s. bounded with samplewise smoothness → here finite variance | Approximate feasibility `‖c‖ ≤ ε`, with failure probability tied to ε → exact feasibility, safe queries, separate tunable `ρ` | Covers no equality constraints. Needs known `H, μ, τ`. The slack reduction was not checked in full |
| Lu–Mei–Xiao, [SIOPT 36(1), 2026; arXiv:2409.09906v4](https://arxiv.org/abs/2409.09906), Cor. 1 (θ=1). Applies only with **deterministic constraints**; main text is equality-only | `Õ(ε⁻³)` samples → same order when constraint noise is 0 | None: same order | Deterministic constraints → stochastic `c` and `J`. Its inequality extension is only remarked on and was not checked | `‖c‖ ≤ ε` surely plus expected stationarity → exact feasibility, all queries safe, and a high-probability KKT certificate with complementarity | Assumes MFCQ instead of their error bound (θ=1). Not compared at the constant level |

Boob–Deng–Lan ([Math. Program. 2023, arXiv:1908.02734v4](https://arxiv.org/abs/1908.02734), Cor. 3.20) needs a strong-feasibility point `ψ_i ≤ −2μ_i D_X²`. It obtains an expected `(ε, δ)`-KKT point with squared residuals in `O(ε⁻³)` fully stochastic iterations, i.e. `O(ε⁻⁶)` at norm accuracy. Its ConEx inner queries need not be feasible, so it is a weaker baseline rather than a row. The level-constrained method ([arXiv:2205.08011v2](https://arxiv.org/abs/2205.08011)) has feasible iterates under uniform MFCQ, but only with deterministic constraints, and its guarantees hold in expectation. The repository's [SurjectiveStochasticInequalityKkt](../../LongTails/Theorems/SurjectiveStochasticInequalityKkt.lean) also has exponent 3, but it needs global Jacobian surjectivity and gives approximate feasibility at fixed confidence. Its class is roughly nested inside this one through `μ ≈ 1/(H√m)`; that is repository overlap, not literature priority.

**Reduction check.** A Zoutendijk/Topkis–Veinott-type ε-active feasible-direction method gives `O(H³Δ/(μ²e²))` steps. Mini-batch estimates with median-of-means would give ε⁻⁴. SPIDER-type recursion under the paired oracle gives ε⁻³ only if every estimate, *including constraint values*, holds to accuracy `O(μe/H)` at every step simultaneously, with finite variance and along an adaptive trajectory. The oracle moments are assumed only at feasible points, so safety and accuracy must be proved jointly. The proof handles this with a product-potential Markov bound over replicas and a first-exit induction. No published theorem supplies that step, but each ingredient is standard: feasible directions, Frank–Wolfe hull solves, SPIDER, and robust centers.

**Search coverage.** Searched 13 Nov 2026 UTC: arXiv, JMLR, SIOPT/Math. Program., and recent safe and stochastic-constrained preprints. 2609.23848 and 2511.19675 assume deterministic or norm-bounded errors with exact values; 2606.25355 is withdrawn. The theorem was introduced in commit `a7adce59` on 12 Nov 2026. Not verified: Shi–Wang Thm 7 verbatim, Lu–Mei–Xiao's inequality remark, and LB-SGD's full parameter dependence. The companion note's citations match the checked statements, but it omits Lu–Mei–Xiao and Boob–Deng–Lan.

**Conclusion**

**Yes: for safe stochastic optimization with nonlinear inequality constraints, the proved accuracy exponent drops from 6–7 to 3, provided the oracle supports paired same-sample queries.**

The strongest prior safe guarantees are LB-SGD and SafePD (the latter for one constraint). Both keep every query feasible with high probability:

| | safe queries | stochastic `c` | complexity |
|---|---|---|---|
| LB-SGD / SafePD | yes | yes | `O(ε⁻⁷)` / `O(ε⁻⁶)` (`m=1`) |
| this result | yes | yes | `Õ(H³ΔσL/(μ³ε³) + (H³Δ+H²σ²)/(μ²ε²))`, `ε ≤ min{1,τ}` |

It also needs no start margin and only finite variance, not sub-Gaussian noise.

The gain is not uniform. It requires a same-sample paired, mean-square-smooth oracle, which LB-SGD does not use, plus global derivative smoothness and known `H, μ, τ`. The baselines' parameter constants were not compared, and the exponent 3 is not proved optimal. Non-safe methods reach `ε⁻³` with deterministic constraints (Lu–Mei–Xiao), and Shi–Wang pays `ε⁻⁵` in constraint values with approximate feasibility. So the new combination is exact safety, stochastic constraint values and `ε⁻³`. The rate alone is not new.

No earlier safe `ε⁻³` theorem was found, but that does not prove priority. The claimable contribution is the first verified safe, high-probability ε-KKT bound of order `ε⁻³` for stochastic nonlinear inequalities under near-active MFCQ, assuming a paired variance-reduction oracle.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
