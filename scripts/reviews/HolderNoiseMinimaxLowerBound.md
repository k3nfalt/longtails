# Novelty assessment: HolderNoiseMinimaxLowerBound

[`result`](../../LongTails/Theorems/HolderNoiseMinimaxLowerBound.lean) proves the following for [`HolderNoiseNonconvexLower.spec`](../../LongTails/Setups/HolderNoiseNonconvexLower.lean). Assume L-smooth objectives on ℝᵈ with gap Δ, and unbiased paired common-sample gradients with variance σ² and centered increments `E‖e(x)−e(y)‖² ≤ M‖x−y‖^{2ν}`, where 0<ν≤1. Then **every** randomized algorithm (no `allowedAlgorithm` restriction) fails `E‖∇f(output)‖ ≤ ε` on some admissible instance, at every pair-call budget N ≤ ⌊B/2⁸⁰⌋, where

$$
B=\frac{L\Delta+\sigma^2}{\varepsilon^2}+\min\Big\{\frac{L\Delta\sigma^2}{\varepsilon^4},\ \frac{\Delta}{\varepsilon^3}\max\big\{M(L/\varepsilon)^{1-2\nu},\ M^{1/(2\nu)}\sigma^{2-1/\nu}\big\}\Big\}.
$$

Validity requires LΔ ≥ 64ε² and d ≥ ⌈2³⁰(1+LΔ/ε²)³(1+σ²/ε²)⌉. The instance may depend on the algorithm and on N, but not on the seed. The hard oracle is Bernoulli-sampled and is not claimed to be a sampled-loss gradient. The companion [upper bound](../../LongTails/Theorems/HolderNoiseMinimaxUpper.lean) matches B up to a factor (1+log₂(2+16LΔ/ε²))². For fixed parameters the fractional term scales as ε^{−(4−2ν)} for ν<1/2 and as ε⁻³ for ν≥1/2.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Arjevani et al., arXiv:1912.02365v2, Math. Program. 199 (2023)](https://arxiv.org/abs/1912.02365), Thm 3 eq. (24) (raw mean-squared smoothness L̄, K-query; applies only at ν=1, M≈L̄², L≥L̄ε/σ) | Ω(ΔL̄σ/ε³ + σ²/ε²) → Ω(Δ√Mσ/ε³ + σ²/ε² + LΔ/ε²), capped by LΔσ²/ε⁴ | None at ν=1: same order. The separate L/M parametrization adds the ΔM/(Lε²) branch and the S cap. | Lower bounds for ν=1 only → every 0<ν≤1 (a new class statement) | None (same expected-norm criterion, randomized algorithms) | Dimension D³A = L³Δ³σ²/ε⁸ versus Õ(KΔ²L̄²ε⁻⁴); requires LΔ ≥ 64ε²; constant 2⁻⁸⁰ |
| Same paper, Thm 3 eq. (23), bounded variance (superclass; indicator noise is discontinuous, so not in the Hölder class for finite M) | Ω(ΔLσ²/ε⁴) → recovered as the S branch when M is large | Not comparable: it is a superclass bound; the selected bound is weaker inside the subclass, as it must be | Bounded variance → bounded variance + spatial Hölder (a subclass where the hardness must be re-established) | None | None beyond row 1 |
| [Jin, arXiv:2608.09004v1 (Aug 2026)](https://arxiv.org/abs/2608.09004), Thm 4.1 (a.s.-bounded discontinuous noise, single-point queries; prior to this result) | Ω(ΔL/ε² + ΔLσ²/ε⁴), dimension-free → B above | Not comparable: different oracle (K=1, no Hölder condition); does not transfer to the paired Hölder subclass | None | None | Selected result needs polynomial dimension |

**Standard-reduction check.** I find the rate is a routine corollary of Arjevani et al.'s smoothed construction (§3.3, Lemma 4; randomized lift, §4/Lemma 7). Their noise has the form a(x)(z/p−1), where a is bounded by O(ε) and O(ℓ)-Lipschitz after scaling. Then min(ε², ℓ²t²) ≤ ε^{2−2ν}ℓ^{2ν}t^{2ν} gives Hölder constant M ≈ ε^{2−2ν}ℓ^{2ν}/p. Maximizing chain cost (ℓΔ/ε²)/p over ℓ≤L and 1/p ≤ min(σ²/ε², M/(ε^{2−2ν}ℓ^{2ν})) reproduces exactly D·min{A, max(U, U^{1/(2ν)}A^{1−1/(2ν)})}, the note's formula. The D and A terms are the standard deterministic and estimation bounds. I checked this at the scaling level. I did not check verbatim that their compression lemma preserves the pointwise bound.

**Proof ancestry.** The probabilistic zero-chain, its randomized lift, and the effective-smoothness tuning (Arjevani et al. Thm 2/3) are inherited. The repository proof re-implements them with C¹,¹ profiles, whole-edge masking and finite embeddings. Its own companion note concedes these are not new techniques.

**Search coverage.** On 17 Nov 2026 UTC I searched the web for lower bounds under Hölder or mean-squared-Hölder sample-gradient regularity. I read Arjevani et al. Thms 1–3 and Lemma 4 from the arXiv PDF, and Jin 2026 Thm 4.1 from the HTML (sections 8–10 were seen only in summary). I did not re-check Fradin et al. (AISTATS 2026) or Carmon et al.'s deterministic bound at theorem level. No prior lower bound stated for ν<1 was found; that is not proof none exists. The companion note's claims are consistent with the Lean statement. The result was introduced in commit `c870310f` (17 Nov 2026).

**Conclusion**

**It is a new statement, but obtained by a routine adaptation of a known construction; it adds no new hardness mechanism.** The strongest baseline is Arjevani et al.'s mean-squared-smooth lower bound, Ω(ΔL̄σ/ε³ + σ²/ε²), which covers only ν=1. This theorem extends the bound to every 0<ν≤1:

$$
\Omega\Big(\tfrac{L\Delta+\sigma^2}{\varepsilon^2}+\min\big\{\tfrac{L\Delta\sigma^2}{\varepsilon^4},\ \tfrac{\Delta}{\varepsilon^3}\max\{M(L/\varepsilon)^{1-2\nu},M^{1/(2\nu)}\sigma^{2-1/\nu}\}\big\}\Big),
$$

for all randomized algorithms, given LΔ ≥ 64ε² and polynomially large dimension. This bound also gives the companion upper bound's matching certificate up to a squared logarithm, including the rough regime ν<1/2.

The limitation is mechanism. Arjevani et al.'s smoothed noise is bounded and Lipschitz, so it is automatically ν-Hölder by interpolation. Re-optimizing their effective smoothness and revelation probability reproduces this exact formula. At ν=1 the bound has the known order and needs a larger dimension than theirs.

What is established is a correctly quantified, complete lower bound for the fractional class, and the matching it provides with the upper bound. What is not established is any new lower-bound idea. I also did not find a prior paper stating this exact Hölder-class bound, though the search was targeted, not exhaustive.

The claimable contribution is a formal, all-algorithm extension of the Arjevani et al. lower bound to spatially Hölder noise, valuable chiefly as the optimality certificate for the companion upper bound.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
