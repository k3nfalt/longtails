# Novelty assessment: `AcceleratedHeavyTailedMarkovConvex`

[`result`](../../LongTails/Theorems/AcceleratedHeavyTailedMarkovConvex.lean) covers an L-smooth convex f on a real Hilbert space whose minimizer lies within R of x₀ ([setup](../../LongTails/Setups/HeavyTailedMarkovSmoothAndConvex.lean)). The gradients g(x,ξₜ) are driven by a Markov chain started at its stationary law π. They are unbiased under π, with centered α-moment ≤ σ^α under π. The chain also satisfies ∫TV(κᵗ(z,·),π)dπ(z) ≤ (1+t/τ)^(−β) at every lag t. Under these assumptions, the [clipped, ball-projected similar-triangles method that uses every m-th sample](../../LongTails/Algorithms/AcceleratedMarkov.lean) returns its last accelerated iterate y_N with 𝔼f(y_N) − f* ≤ ε.

**Proved budget.** The budget is exactly N·m calls, where N = max{1,⌈√(32LR²/ε)+(256σR/ε)^{α/(α−1)}⌉} and m = max{1,⌈τ(256LR²/ε+64(256σR/ε)^{α/(α−1)})^{1/β}⌉}. Hence

  T ≤ (1 + √(32LR²/ε) + (256σR/ε)^{α/(α−1)}) · (1 + τ·(256LR²/ε + 64(256σR/ε)^{α/(α−1)})^{1/β}).

Here L is the smoothness constant, R ≥ ‖x₀−x*‖, σ is the noise level, α ∈ (1,2] is the moment order, τ>0 is the mixing scale, β>0 is the mixing exponent, and ε is the target expected gap. I keep the constants because they are not universal as α→1 or β→0. The updates require L, R, σ, α, τ, β and ε. The case R=0 is trivial.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Solodkin–Veprikov–Beznosikov, [arXiv:2408.01848](https://arxiv.org/abs/2408.01848) (v1 Aug 2024, v2 Nov 2025; I read v2), Thm 2 / Cor 2, accelerated mirror descent with Markov MLMC batching. **Overlap:** α=2, a.s. noise ≤ σ, sup_z TV ≤ 2^(−t/τ_mix), stationary start, domain B(x₀,R) so D=2R. | Õ(√(LR²/ε) + τ_mix σ²R²/ε²) → set β=1+ln(e+LR²/ε+σ²R²/ε²) and τ=βτ_mix/ln 2. This is admissible because (1+t/τ)^(−β) ≥ e^(−βt/τ) = 2^(−t/τ_mix). The result is O((1+√(LR²/ε)+σ²R²/ε²)·τ_mix·log(e+LR²/ε+σ²R²/ε²)). | **Worse:** an extra τ_mix·log factor on the deterministic term; the noise term has the same order up to logarithms. No regime gains. | Noise bounded a.s. → α-moment under π only, α∈(1,2] (infinite variance allowed). Uniform geometric mixing → π-averaged polynomial mixing. Classes are incomparable: Solodkin et al. also cover non-Euclidean ℓ_p geometry. | None: both give last-iterate expected gap and need σ and the mixing scale. | Hilbert space only. The mixing bound must hold with prefactor 1 at every lag. The m-skip is paid even when σ=0. |
| Duchi–Agarwal–Johansson–Jordan, ergodic mirror descent, [arXiv:1105.4681](https://arxiv.org/abs/1105.4681) (SIAM J. Optim. 2012), Thm 1 and bound (12). **Special case:** ‖g‖ ≤ G a.s., uniform mixing of any rate, compact domain, arbitrary start, smoothness not needed. | With sup_z TV ≤ (1+t/τ)^(−β), τ_TV(ε/(3GR)) ≤ τ(3GR/ε)^{1/β}, so O(τ(GR/ε)^{2+1/β}) for the averaged iterate. This result on the overlap (α=2, σ≤2G): O((1+√(LR²/ε)+(GR/ε)²)(1+τ(LR²/ε+(GR/ε)²)^{1/β})), with c^{1/β} constants. | **Mixed.** Worse by (GR/ε)^{1/β} when σ≍G and Lε ≤ G². Better when G² < Lε, β>1 and LR²/ε < (GR/ε)^{(4β+2)/(β+2)}, e.g. Huber functions with slope < G. That gain is acceleration versus a nonsmooth method. | Bounded stochastic gradients → α-moment under π; uniform mixing → π-averaged mixing. Classes are incomparable. | Averaged iterate → last iterate. | Requires smoothness and a stationary start. Polynomial-rate mixing only. |
| He–Lu–Li, [arXiv:2510.11676](https://arxiv.org/abs/2510.11676) (v1 Oct 2025, v2 21 Sep 2026; I read v2), Thm 2(i) and eq. (7a), accelerated stochastic proximal subgradient method. **i.i.d. special case,** h = indicator of B(x₀,R). | O(√(LR²/ε)+(σR/ε)^{α/(α−1)}) in expectation → if κ(z,·)=π, the mixing distance is 0 for t≥1, so take small τ and m=1: O(1+√(LR²/ε)+(256σR/ε)^{α/(α−1)}). | None: same order. | i.i.d. samples → stationary Markov samples. | None: both bound the last-iterate expected gap. | Clipping and knowledge of σ and α are required; He–Lu–Li need neither. |

**Reduction check and proof ancestry.** The proof is a composition of known pieces. Data dropping turns each used sample's conditional law into a lag-m TV error, as in the standard data-drop argument (e.g. Duchi et al.) Clipping at level C bounds that bias by 2C·TV and the clipping bias by σ^α/C^{α−1}, following clipped-SSTM (Gorbunov et al., NeurIPS 2020; Sadiev et al., [ICML 2023](https://proceedings.mlr.press/v202/sadiev23a.html), Thm 3.2, which is a high-probability bound). Projected similar triangles absorb bounded additive bias. I found no new mechanism.

**Instance check.** Let z=(s,w), where s is a two-state chain with flip probability p∈(0,½) and w is drawn i.i.d. from a symmetric law with finite α-moment and infinite variance. Set g(x,z)=∇f(x)+c(s)+w with E_π c=0. Then g is unbiased under π and has finite α-moment, so σ<∞, and the π-averaged TV equals ½|1−2p|ᵗ ≤ (1+t/τ)^(−β) for β=1 and τ=1/(2p). The a.s.-bounded-noise assumptions of Solodkin et al. and Beznosikov et al. fail on this instance, as does Duchi et al.'s bounded-subgradient assumption. The bias term forces TV ≲ ε/(RC) with C ≍ (ε/R)(σR/ε)^{α/(α−1)}, which is why the mixing exponent multiplies the whole noise term.

**Search coverage.** I searched on 2026-10-07 in arXiv, ICML, NeurIPS and PMLR for Markovian, heavy-tailed, clipped, accelerated and polynomial-mixing convex methods. I read the theorem statements of Solodkin et al., Duchi et al., He–Lu–Li and Sadiev et al. Beznosikov et al. (NeurIPS 2023) covers only strongly convex and nonconvex problems with a.s.-bounded noise. Doan et al. ([arXiv:2002.02873](https://arxiv.org/abs/2002.02873)) assume a finite-state chain and bounded gradients. Sarkar–Chakrabartty–Aggarwal ([arXiv:2606.26316](https://arxiv.org/abs/2606.26316), 24 Jun 2026, before this result) clip heavy-tailed Markov gradients with a stationary p-moment, but only for PL objectives under geometric mixing. That class is incomparable, and I checked only their abstract and the main theorem summary. Git history introduces the setup on 2026-09-21 (d6e69f0) and the theorem the same day (c876d4b). There is no companion note. Within the repository, `MarkovQuadraticLastIterate` treats a different, quadratic class.

## Conclusion

**The rate does not improve; the gain is scope: convex smooth optimization with infinite-variance Markov noise, which no checked theorem covers.**

The strongest direct baseline is Solodkin et al. (Cor. 2), on bounded noise with geometric mixing. There, this result is worse:

| | Total calls |
|---|---|
| Solodkin et al. | Õ(√(LR²/ε) + τ_mix σ²R²/ε²) |
| This result | O((√(LR²/ε) + σ²R²/ε²)·τ_mix·log(LR²/ε+σ²R²/ε²)) |

It never pays τ_mix on the deterministic term, and this result always does, even at σ=0.

What is new relative to the checked literature is coverage. Chains with gradient noise that has only an α-moment under π, α<2, are now handled. For example, a finite ergodic chain paired with an independent infinite-variance coordinate satisfies every hypothesis but violates all bounded-noise Markov assumptions. Polynomial, π-averaged mixing is also admitted. The only heavy-tailed Markov result I found requires PL objectives. Failing to find a competitor does not establish priority.

The extension follows by composing standard data dropping, clipping bias and projected acceleration. It is also worse wherever a comparison exists. The claimable contribution is a first expected-gap guarantee, by routine composition, for convex heavy-tailed Markov stochastic gradients.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
