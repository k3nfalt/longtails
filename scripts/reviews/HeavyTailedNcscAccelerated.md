# Novelty assessment: accelerated heavy-tailed NC–SC minimax

[`HeavyTailedNcscAccelerated.result`](../../LongTails/Theorems/HeavyTailedNcscAccelerated.lean) covers jointly L-smooth f(x,y) that is μ-strongly concave in y, on arbitrary finite-dimensional spaces ([setup](../../LongTails/Setups/HeavyTailedNcsc.lean)). The oracle returns IID, unbiased joint stochastic gradients whose central p-th moment is at most σ^p, with 1<p≤2. Under these assumptions the [algorithm](../../LongTails/Algorithms/HeavyTailSaddleEstimator.lean) (coarse proximal saddle solves, then one fine solve) returns a computable point X with P(‖∇Φ(X)‖>ε) ≤ δ, where Φ = max_y f.

**Proved budget.** Notation:
- Δ ≥ Φ(x₀) − inf Φ is the initial gap, and G ≥ ‖∇_y f(x₀,y₀)‖ bounds the initial dual gradient.
- κ = L/μ and r = p/(p−1).
- Q = log(2 + L⁴(Δ+G²/μ)/(μ³ε²)).
- ℓ = 1 + log(2 + κ + 1/δ + LΔ/ε² + (Lσ/(με))^r + Q).

The budget is

  N = O( (2⁸⁰r)^{r+2} ℓ^{2r+3} [ √κ(1 + LΔ/ε² + Q) + (LΔ/ε²·κ^{r/2} + κ^r)(σ/ε)^r ] ),   with 0<δ<1/2.

The constant and the log exponent blow up as p↓1; at p=2 the log factor is ℓ⁷.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Luo, N²-SGDA, [arXiv 2509.14952v3](https://arxiv.org/abs/2509.14952) Thm 4.2 (v1 Sep 2025, prior); [JMLR 27(233), 2026](https://jmlr.org/papers/v27/25-3100.html) | Õ(LΔκ^{r+1}σ^r/ε^{r+2} + LΔκ²/ε²) → N | Noise term: factor κ^{r/2+1}. Deterministic term: κ² → √κ. The extra κ^r(σ/ε)^r term is no larger than their noise term when LΔ ≥ ε²/κ. Ours carries an explicit ℓ^{2r+3} factor and an enormous constant; their log powers are hidden. | None (same smooth NC–SC + p-BCM class; they also treat bilevel problems) | Their output is an average over the trajectory, so no single point is certified; ours certifies one computably selected point. Both are high-probability. | Ours requires IID sampling; adds √κQ |
| Zhu–Xu–Ji, Stoc-TRGDAmax, [arXiv 2609.06064v1](https://arxiv.org/abs/2609.06064) Thm 4.3, Eq. 4.9 (5 Sep 2026, prior) | O(LΔκ^{1+r/2}/ε² + LΔκ^{r+1}σ^r/ε^{r+2}), case ε ≥ 2L‖y₀−y*(x₀)‖; Eq. 4.7 adds logs and distance terms → N | Noise term: factor κ^{r/2+1}. Deterministic term: factor κ^{(r+1)/2}. Applies for the same LΔ ≥ ε²/κ condition, up to ℓ^{2r+3} | Their lemmas assume compact sublevel sets; ours does not. Ours does not cover their composite regularizers r and h. | Theirs bounds E[(1/T)Σ‖∇Φ(x_t)‖], so Markov gives a random iterate at confidence δ with a (1/δ)^{r+2} factor. Ours gives log(1/δ) dependence, but no expectation bound. | IID sampling; no prox/composite scope |
| Wu et al., [arXiv 2610.00229v2](https://arxiv.org/abs/2610.00229) Thm 3.4 (v1 22 Sep 2026, prior; non-peer-reviewed, auto-generated preprint); **p = 2 only** | Õ(√κLΔ/ε² + κLΔσ²/ε⁴ + κ²σ²/ε² + √κ log₊(G/(ε√κ))) with success probability 2/3 → N at p=2 has the same terms | None: same order at p=2. Wu proves this order is tight at p=2. | Finite variance → p-th moment with p<2, which admits infinite-variance noise | Fixed confidence 2/3 → tunable δ, at the cost of ℓ⁷ polylog factors | Wu's oracle allows adaptive conditionally-unbiased kernels; ours assumes IID |

**Reduction check and proof ancestry.** The outer scheme follows Wu et al.'s design: T ≍ 1+LΔ/ε² coarse solves at accuracy ε²/L, then one fine solve at μ·ε²/L². That design together with clipping is the proof ancestry. Two natural reductions do not yield the additive inner cost √κ + (σ²/(μη))^{r/2}:
- Batch-clipping each oracle call of Wu's solver introduces bias, and Wu's analysis assumes unbiased gradients.
- Wrapping clipped acceleration ([Sadiev et al., ICML 2023](https://proceedings.mlr.press/v202/sadiev23a.html)) around an inexact dual gradient pays the robust-estimation cost at every accelerated step.

The new mechanism is a heavy-tailed accelerated saddle solver: clipped multilevel estimates with bias and second moment tracked separately, plus a joint-gap certificate. I verified the obstruction only at this level. I did not audit every proof module, and I did not run the build or the axiom audit.

**Search coverage (2026-11-07).** I searched arXiv, JMLR, ICML, NeurIPS and ICLR for heavy-tailed NC–SC/NC-PL minimax and accelerated heavy-tail methods.
- Read in full text: the Wu et al. theorem statements (HTML), Zhu–Xu–Ji Section 4 (HTML), and Liu–Luo Thm 4.2 (PDF text). Liu–Luo's criterion is ambiguous in the extracted text, though the T ≍ κLΔ/ε² schedule indicates norm-level ε.
- Reported only through Zhu–Xu–Ji's related work: Ha (2026, NC-PL) at κ^{(3p−2)/(p−1)}, and the federated NC-PL methods. Both are worse in κ.
- The theorem entered the repository in commit a8f18312 on 2026-11-07. I found no later competing work.
- **Note discrepancies:** the companion note cites Wu "Theorem 4.1", which is the inner-solver theorem; the end-to-end result is Theorem 3.4. Its Liu–Luo "Theorem 11" numbering (JMLR) is unverified; arXiv v3 calls it Theorem 4.2.
- No heavy-tail lower bound pins down the κ dependence. Zhu–Xu–Ji Thm 3.4 gives only Ω(LΔκ^{1/3}σ^r/ε^{r+2}), for zero-respecting methods and counted in iterations.

## Conclusion

**Yes: for p<2 the proved total complexity improves polynomially in κ over every heavy-tailed NC–SC guarantee I found.**

The strongest heavy-tailed baselines are Liu–Luo (N²-SGDA) and Zhu–Xu–Ji (Stoc-TRGDAmax). With A = LΔ/ε² and r = p/(p−1):

| | deterministic part | noise part |
|---|---|---|
| Liu–Luo / Zhu–Xu–Ji | Aκ² / Aκ^{1+r/2} | Aκ^{r+1}(σ/ε)^r |
| This result | √κ·A | Aκ^{r/2}(σ/ε)^r + κ^r(σ/ε)^r |

The gain survives the extra terms when LΔ ≥ ε²/κ, up to an ℓ^{2r+3} polylog factor and a huge p-dependent constant. For example, at p=3/2 the noise term improves from Aκ⁴(σ/ε)³ to Aκ^{1.5}(σ/ε)³. The guarantee is also for a selected point with log(1/δ) confidence, rather than for averaged or expected stationarity. It loses the composite scope of Zhu–Xu–Ji and needs IID sampling.

At p=2 the rate is exactly Wu et al.'s September 2026 bound, which is already tight there. The result is therefore the heavy-tailed extension of Wu's rate; its outer structure is inherited from Wu. I could not reduce the robust accelerated inner solver to known theorems. Priority rests on a fast-moving, two-month-old literature, and optimality in κ for p<2 is open.

What can be claimed is the first NC–SC guarantee under p-th-moment noise that combines the accelerated √κ·LΔ/ε² term with κ^{r/2} noise conditioning, extending Wu's rate to infinite-variance noise.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
