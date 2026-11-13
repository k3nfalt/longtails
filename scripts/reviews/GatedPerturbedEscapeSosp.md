# Novelty assessment: GatedPerturbedEscapeSosp

[`result`](../../LongTails/Theorems/GatedPerturbedEscapeSosp.lean) proves the following. Let `f` be `C²` on a `d`-dimensional real Hilbert space (`d ≥ 1`), with an `L`-Lipschitz gradient, a `ρ`-Lipschitz Hessian, `f(x₀) − inf f ≤ Δ` and `ρε ≤ L²`. The oracle returns fresh IID stochastic gradients that are only unbiased, have variance `≤ σ²` and are jointly measurable ([setup](../../LongTails/Setups/VarianceOnlySecondOrder.lean)). Under these assumptions the [gated perturbed-escape algorithm](../../LongTails/Algorithms/GatedPerturbedEscape.lean) outputs its stopped point `x`, and with probability `≥ 1−δ` that point satisfies `‖∇f(x)‖ ≤ ε` and `∇²f(x) ⪰ −√(ρε) I`. All of `L, ρ, σ, Δ, ε, δ, d` are used as tuning inputs.

**Budget.** Write `A = L/√(ρε) + LΔ/ε²`. Expanding the proved product `N·b` gives

```
O( log²(A·log(2d)/δ) · log⁸(2d) · [ A·(1 + σ²/ε²) + dσ²/ε² + dσ²√ρΔ/ε^{7/2} ] ).
```

The additive terms `L/√(ρε)` and `dσ²/ε²` are a certification floor, paid even when `Δ = 0`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jin–Netrapalli–Ge–Kakade–Jordan, [JACM 2021 / arXiv 1902.04811v2](https://arxiv.org/abs/1902.04811), Thm 16 without Assumption C (perturbed SGD; norm-sub-Gaussian noise only, so a special-case baseline) | `Õ(LΔ/ε² · (1 + dσ²/ε²))` → `Õ(A(1+σ²/ε²) + dσ²/ε² + dσ²√ρΔ/ε^{7/2})` | When `Δ ≥ ε^{3/2}/√ρ`, the speedup is `(1+dσ²/ε²)/(1+σ²/ε²+dσ²√(ρε)/(Lε²))`, up to polylogs. If `σ ≥ ε`, this is `≍ min(d, L/√(ρε))`. Example: `d = L/√(ρε)` and `σ ≥ ε` give `dLΔσ²/ε⁴ → LΔσ²/ε⁴`. | Norm-sub-Gaussian noise → finite variance only | "Visits" an SOSP w.p. `1−δ`, and outputs one only as a uniformly random iterate with constant probability (Remark 14) → the stopped iterate is an SOSP w.p. `1−δ` | Worse when `Δ ≪ ε^{3/2}/√ρ`, because of the floor `L/√(ρε) + dσ²/ε²`. Has a `log⁸ d` factor (Jin's has `ι⁹`). Needs `σ, Δ, δ, d` for tuning, as Jin does |
| Vlaski–Sayed, [arXiv 1908.07023](https://arxiv.org/abs/1908.07023), Thms 1–3 (plain SGD) | No `(ε,√(ρε))` oracle budget; the guarantees are in terms of the step size `μ` → the bound above | Not comparable: no end-to-end call count | Their assumptions are a relative 4th-moment bound, a Lipschitz noise covariance and a noise lower bound at saddles → variance only, with no noise lower bound | Not comparable | No injected perturbation is needed there |
| Arjevani et al., [COLT 2020 / arXiv 2006.13476](https://arxiv.org/abs/2006.13476), Thm 4 (also Wu et al., [arXiv 2609.28238](https://arxiv.org/abs/2609.28238), Sep 2026, Thm 3.3) | `Õ(Δσ₁σ̄₂/ε³ + …)`, with only log-d dependence → the bound above | Not comparable: different oracle | None | None | Those results use stochastic Hessian-vector products (HVPs), and Arjevani et al. also need almost-surely bounded Hessian noise. This result uses gradients only |

The repository has no other gradient-only stochastic SOSP theorem. [DirectionalHeavyTailedSecondOrder](DirectionalHeavyTailedSecondOrder.md) uses HVPs.

**Reduction check and mechanism.** The result does not follow from Jin et al. by batching. Mean batching does not make the noise norm-sub-Gaussian, and median-of-means estimates are biased. Composing median-of-means with an inexact-gradient escape routine seems to need gradient error `≲ ε/√d` throughout the escape. That would cost `≍ dLΔσ²/ε⁴`, no better than Jin; I did not prove this. What appears new is that the escape phase uses unbiased block means. The variance accumulated over `T ≈ L/√(ρε)` steps then needs batch size only `∝ dσ²√ρ/(Lε^{3/2})`. A median-of-means "gate" accepts only steps that provably decrease `f`, which gives a stopping certificate. The proof ancestry is PGD/PSGD (Jin et al.) and median-of-means. Dimension-free gradient-only rates need per-sample Lipschitz stochastic gradients: restarted SGD of Fang et al. 2019, as listed in Arjevani et al.'s Table 2 (I did not read Fang et al. directly), and NEON/Neon2.

**Search coverage.** On 2026-11-13 UTC I searched arXiv and the web for SOSP and saddle escape under bounded-variance, heavy-tailed and median-of-means noise. I read Jin et al. v2 (Thm 16, Eq. 4, Remark 14) and Arjevani et al. (Thms 1–6, Tables 1–2) from primary text. I read Vlaski–Sayed, Wu et al. and Chen et al. ([2610.16832](https://arxiv.org/abs/2610.16832); per-sample smoothness, Hessians) only partly. All of these predate the result, introduced in commit `67990f1` (2026-11-13). The companion note's description of Jin's theorem is accurate. Its per-saddle `Ω(dσ²/ε²)` lower bound is unformalized, and I did not verify it.

## Conclusion

**Yes: on the common noise class the proved complexity is polynomially better than the strongest prior gradient-only SOSP bound, and it holds under weaker noise assumptions.**

The baseline is Jin et al.'s perturbed SGD, which needs norm-sub-Gaussian noise. On that overlap, with `Δ ≥ ε^{3/2}/√ρ` and up to polylogarithms:

| | Leading noise cost | Noise model | Output |
|---|---|---|---|
| Jin et al. Thm 16 | `dLΔσ²/ε⁴` | norm-sub-Gaussian | visits an SOSP; random iterate succeeds with constant probability |
| This result | `LΔσ²/ε⁴ + dσ²√ρΔ/ε^{7/2}` | finite variance | stopped point, w.p. `1−δ` |

When `σ ≥ ε`, this is a speedup of order `min(d, L/√(ρε))`. For tiny gaps `Δ ≪ ε^{3/2}/√ρ`, the result loses because of its certification floor `L/√(ρε) + dσ²/ε²`. The `ε⁻⁴` term remains above the `ε^{−3.5}` gradient-only first-order lower bound of Arjevani et al. (stated for zero-respecting algorithms), so optimality is not established.

The comparison proves the gain over Jin et al. Priority rests on a targeted search that found no prior gradient-only SOSP guarantee under variance-only noise; this search is not exhaustive. Methods that use HVPs or per-sample smoothness are dimension-free, but they use stronger oracles or assumptions.

The contribution that can be claimed is a certified high-probability SOSP guarantee from variance-only stochastic gradients, which reduces the dimension penalty from `d·LΔσ²/ε⁴` to `dσ²√ρΔ/ε^{7/2}`.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
