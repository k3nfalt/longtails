# Novelty assessment: AdaptivePairedZerothOrderConfidence

[`result`](../../LongTails/Theorems/AdaptivePairedZerothOrderConfidence.lean) proves the following for the [setup](../../LongTails/Setups/AdaptivePairedZerothOrder.lean) and the [two-branch clipped accelerated algorithm](../../LongTails/Algorithms/AdaptivePairedZerothOrder.lean). Take a convex, `M`-Lipschitz `f = E F(·,ω)` on a compact convex `Q` that has an exact projection, with queries allowed within `γmax` of `Q`. Paired same-sample value queries `F(x,ω)+δ(x)` then return a point `x̂ ∈ Q` with `Pr[f(x̂)−f* > ε] ≤ δfail`, using exactly `6T+4N` scalar evaluations.

**Complexity.** Here `d` is the dimension, `D` the diameter of `Q`, and `M2² ≥ E‖G(x,ω)‖²` the pointwise second moment of the sample weak gradients. `L` is the gradient-Lipschitz constant (smooth branch) and `Δ` the bound on the fixed bias. Taking the smallest admissible `T` and `N` gives

`O( (d + log(1/δfail))·(1 + M2²D²/ε²) + N )`, where `N = √(LD²/ε)` in the smooth case and `N = d^{1/4}MD/ε + d^{1/4}D√(M/(γmax ε))` in the nonsmooth case.

The bound requires `Δ ≤ εγ/(16384√d D)`, where `γ = min(γmax, D/N)` in the smooth case and `γ = min(γmax, d^{1/4}D/N)` in the nonsmooth case. The hidden constant is about `2^50`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kornilov et al., [NeurIPS 2023](https://arxiv.org/abs/2310.18763), Thm 1/Thm 3 (ZO-clipped-SSTM, direct two-point competitor), α=2 | `Õ(dM2²R²log²(K/δ)/ε² + d^{1/4}M2R log(K/δ)/ε)` (my substitution into (27)–(29)) → `O((d+log(1/δ))(1+M2²D²/ε²)+N)` | `d·log²(K/δ)` → `d+log(1/δ)`: a factor of order `log(1/δ)·min(d, log(1/δ))` | Lipschitz samples with `E Lip(ξ)² ≤ M2²` → pointwise weak-gradient second moment (strictly broader) | None (both high-probability, final point) | Needs a bounded `Q`, its diameter `D` and an exact projection (Kornilov: unconstrained, `R=‖x0−x*‖`); finite variance only (Kornilov allows α∈(1,2]) |
| Liu, [ICLR 2026 / arXiv v3](https://arxiv.org/abs/2512.23178), Thm 1, applied to the ball-smoothed `f_γ`, `γ=min(γmax, ε/2M)`. Applicability: Lipschitz-sample overlap, `Δ=0` | `O((d+√d log(1/δ))M2²D²/ε² + √d log(1/δ)·MD/ε)` → same as above | `√d·log(1/δ)` → `log(1/δ)`. The gain needs `log(1/δ) ≫ √d` and is at most order `√d` (attained at `log(1/δ)≈d`). None at `log(1/δ) ≲ √d` | None on the overlap | None | Worse when `γmax < √d·Mε³/((d+log(1/δ))²M2⁴D²)`, because the accelerated `γmax` term dominates. Liu's SGD needs no `γmax` term and no compactness |
| Zhang et al., [arXiv 2610.00260v1](https://arxiv.org/abs/2610.00260) (24 Sep 2026, prior), Thm 2.2, with the same reduction (`L²≍dM2²`, `s²≍M2²`) | `O((d+log(1/δ))M2²D²/ε² + log(1/δ)·MD/ε)`, δ<1/10 → same as above | None: same order (the selected bound adds an `N`/`γmax` term) | None on the overlap | None | Zhang's internal computation is unrestricted and its net may be exponential in `d` (§1, App. A.3). The selected method uses polynomially many exact-real primitive operations |

**Reduction check.** On samples with square-integrable Lipschitz constants, spherical smoothing gives an unbiased estimate of `∇f_γ` with `E‖g‖² ≲ dM2²` (Shamir 2017). Lévy concentration with Cauchy–Schwarz gives the directional bound `E⟨g,v⟩² ≲ M2²`. Feeding these into Liu or Zhang gives the rows above. The selected bound's `d+log(1/δ)` therefore does not follow from Liu alone, and its order is not new given Zhang. Two pieces are genuinely new. The first is scalar clipping of paired differences along a known direction, which yields `d+log(1/δ)` in polynomial time. The second is the directional moment lemma under the pointwise weak-gradient model. Neither Liu nor Zhang treats a biased oracle, so the `Δ>0` case is unchecked against them. Proof ancestry: accelerated similar-triangles weighting (Sadiev et al.; Kornilov et al.) and Shamir-type spherical moments supply the template, not this rate.

**Search coverage (16 Oct 2026).** I searched arXiv, NeurIPS, ICLR and OpenReview for zeroth-order and heavy-tailed high-probability results, and also checked 2605.17394 and 2606.20446 (both not comparable). The two NeurIPS 2026 OpenReview papers flagged in the companion note remain inaccessible. Dorn et al. ([2610.15202](https://arxiv.org/abs/2610.15202), 10 Oct 2026) already uses the weak-gradient model, so the setup is not new. I did not verify the note's claim about its Lemma B.2, and its Theorems T.3–T.4 were not re-checked. The note's comparisons with Liu and Zhang agree with my reading. The theorem was introduced in commit f6eb3de (16 Oct 2026). I did not run a build.

**Conclusion**

**The oracle-call rate is not new; what is new is reaching it with an efficient zeroth-order method, and that beats efficient methods only at extreme confidence levels.**

The strongest prior oracle-complexity result is Zhang et al. (September 2026). Through standard spherical smoothing it already gives the same order with a computationally unrestricted method. The strongest efficient baseline is Liu's clipped SGD (ICLR 2026) under the same reduction:

| | scalar evaluations |
|---|---|
| Liu + smoothing | `(d + √d·log(1/δ))·M2²D²/ε²` |
| this result | `(d + log(1/δ))·(1 + M2²D²/ε²) + N` |

The gain over Liu requires `log(1/δ) ≫ √d`, which means `δ < e^{-100}` when `d = 10⁴`. It saturates at a factor of about `√d`, and is lost when `γmax` is very small. Over Kornilov et al.'s zeroth-order method the gain is larger, roughly from `d·log²` to `d+log`. Against Liu, however, that gain shrinks to the regime above.

Beyond the rate, two modest points stand: sample regularity is weakened from Lipschitz samples to pointwise weak-gradient moments, and a polynomial-time method attains Zhang's oracle order in the paired zeroth-order setting. Two things remain unresolved: priority against the two inaccessible NeurIPS 2026 papers, and the `Δ>0` comparison.

What can be claimed is an efficient accelerated zeroth-order method with additive dimension and confidence costs. It is not a new oracle-complexity rate.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
