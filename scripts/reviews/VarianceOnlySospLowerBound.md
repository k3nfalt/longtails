# Novelty assessment: VarianceOnlySospLowerBound

[`result`](../../LongTails/Theorems/VarianceOnlySospLowerBound.lean) proves the following lower bound in the setup [`HighDimensionalVarianceOnlySecondOrder`](../../LongTails/Setups/HighDimensionalVarianceOnlySecondOrder.lean), which restricts [`VarianceOnlySecondOrder`](../../LongTails/Setups/VarianceOnlySecondOrder.lean). Take any measurable randomized algorithm and any budget `N ≤ ⌊dσ²√ρΔ/(2^703 ε^{7/2})⌋` of stochastic gradients. Then some instance exists on which the output fails to be an `(ε, √(ρε))`-SOSP with probability at least `1−δ`. The instance is `C²` on `ℝ^d` with `∇f` `L`-Lipschitz and `∇²f` `ρ`-Lipschitz. The oracle is unbiased, i.i.d., jointly measurable and has variance at most `σ²`. The instance may depend on the algorithm and on `N`, but not on the algorithm's seed. This is a lower bound, so there is no algorithm file; the hard instance is in `Proofs/EscapeChain*.lean`.

**Bound.** Let `D = √ρΔ/ε^{3/2}`. Then

`N_required = Ω(d σ² √ρ Δ / ε^{7/2})`,

valid when all of the following hold:
- `δ ≤ 1/2`;
- `L ≥ 2^130 √(ρε)`;
- `σ ≥ 2^200 ε`;
- `D ≥ 2^390`;
- `D² log(dσD/ε) ≤ 2^480 d`, which forces `d ≳ D² log` and in particular `d ≳ 2^300`.

The parameters are: `d` dimension, `L` gradient-Lipschitz constant, `ρ` Hessian-Lipschitz constant, `σ²` variance, `Δ` initial gap, `ε` accuracy, `δ` failure probability. The hidden constant is `2^{-703}`. The regime is nonempty because `d` is free.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani–Carmon–Duchi–Foster–Sekhari–Sridharan, [COLT 2020, arXiv:2006.13476v1](https://arxiv.org/abs/2006.13476), Thm 3 / eq. (10), gradient-only case (§1.1.1); prior | `Ω(Δσ²ε⁻³·min{√(ρ/ε), L/ε})`, which under `L ≥ 2^130√(ρε)` is `Ω(σ²√ρΔ/ε^{7/2})` → `Ω(dσ²√ρΔ/ε^{7/2})` | Factor `d` larger, whenever `d ≥ 2^{-480}D² log(dσD/ε)` and the other `valid` conditions hold | Formal proof for zero-respecting algorithms only (footnote 3 claims an extension) → all measurable randomized algorithms | None. Both use constant success probability. | Hard only for the SOSP criterion; the prior bound is already hard for ε-stationary points. Needs `d ≳ D² log` (the prior construction needs dimension `Θ(D)`), `σ ≥ 2^200ε` and astronomical constants. Covers no small-`d` regime and gives no `LΔσ²/ε⁴` term. |
| Repository upper bound [`GatedPerturbedEscapeSosp`](../../LongTails/Theorems/GatedPerturbedEscapeSosp.lean) (same base class, introduced 2026-11-13) | Upper bound `O(log⁸d · ℓ² · (LΔσ²/ε⁴ + dσ²√ρΔ/ε^{7/2}))`, with `ℓ = log(κ(1+D)log d/δ)` and `κ = L/√(ρε)` → lower bound `Ω(dσ²√ρΔ/ε^{7/2})` | Matches the upper bound up to `2^{797}·log⁸d·ℓ²` when `d ≥ L/√(ρε)` | Lower bound fixes `E = ℝ^d`, `Ω = ℝ`, `x0 = 0` and the `valid` regime (harmless restrictions for hardness) | Upper bound has `log(1/δ)` confidence; the lower bound uses fixed `δ ≤ 1/2` | For `d < L/√(ρε)` the upper bound's `LΔσ²/ε⁴` term dominates and the lower bound is not tight |

**Reduction check and proof ancestry.** I found no standard reduction that yields the `d·D` product:
- Rescaling the dimension-free chain of Carmon et al. and ACDFSS gives only the factor `D`.
- A single hidden saddle (a noisy-eigenvector problem) gives roughly `dσ²/ε²` and no factor `D`.
- Combining the two requires a direct-sum argument against adaptive algorithms.

The note provides this argument. It localizes masked saddles (`W_l`) so each stage's reveal rate stays `O(1/(dσ̂²))`, and counts each stage inside its own simulator. Proof ancestry:
- Carmon et al. (Math. Program. 2020) and Arjevani et al. ([arXiv:1912.02365v2](https://arxiv.org/abs/1912.02365), Thm 3) supply zero-chains and probabilistic reveal oracles.
- ACDFSS Thm 6 supplies chained saddles, but with Hessian-vector-product noise, so it does not apply to gradient-only oracles.

**Search coverage.** I searched on 2026-11-26 across arXiv, COLT/PMLR, Math. Program. and general web searches for dimension-dependent SOSP and saddle-escape lower bounds:
- I read ACDFSS 2020 (Thm 3, eq. (10), Table A) and Arjevani et al. 2019 v2 (Thm 3) in full text.
- I read Chen et al., [arXiv:2610.16832v2](https://arxiv.org/abs/2610.16832) (Oct 2026), Thm 4.2. It gives `Ω̃(ε⁻³+γ⁻³)` with no dimension factor, under per-sample smoothness, almost-sure noise and Hessian queries. That is a different and stronger oracle model, so it is not a baseline.
- Jin et al. JACM 2021 Thm 16 (a `d`-linear upper bound) I checked only through secondary text.
- I found no prior `d`-linear lower bound.
- The companion note's citations agree with what I checked. However, it discusses only ACDFSS Thm 6, which uses Hessian-vector-product noise, and omits the direct baseline: the dimension-free gradient-only `ε^{-7/2}` bound of ACDFSS Thm 3 / eq. (10).

I did not run the build or the axiom audit.

**Conclusion**

**Yes: this is a strictly stronger lower bound, larger by a factor `d`, in a very high-dimensional regime.** The strongest prior gradient-only bound is ACDFSS (COLT 2020). It is dimension-free and formally proved only for zero-respecting algorithms:

| | Necessary stochastic-gradient calls |
|---|---|
| ACDFSS 2020 (ε-stationary, so also SOSP) | `Ω(σ²√ρΔ/ε^{7/2})` |
| This result (SOSP, all measurable algorithms) | `Ω(dσ²√ρΔ/ε^{7/2})`, for `d ≳ (ρΔ²/ε³)·log` |

The gain is genuine because first-order stationarity needs no such factor. ACDFSS's Table A lists normalized SGD with momentum (Cutkosky–Mehta, ICML 2020) at `O(σ²√ρΔ/ε^{7/2})` under the same variance-only noise. The theorem therefore shows that, without per-sample smoothness, certifying curvature costs a linear factor of `d` over gradient stationarity. With the repository's upper bound, it pins down the `d`-dependent term up to polylogarithmic factors when `d ≥ L/√(ρε)`.

There are real limits:
- The constants (`2^{-703}`, `σ ≥ 2^200ε`, `d ≳ 2^300`) make the statement purely asymptotic.
- It says nothing for `d ≲ ρΔ²/ε³`.
- It does not capture the `LΔσ²/ε⁴` term.
- My search found no earlier dimension-linear bound, but it cannot establish priority conclusively.

The contribution that can be claimed is the first dimension-linear minimax lower bound I could find for SOSPs under variance-only stochastic gradients. It matches the leading dimension-dependent upper-bound term in high dimension.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
