# Regularized prox-EG+ for stochastic composite cohypomonotone inclusions

[`result`](../../LongTails/Theorems/RegularizedProxExtragradientCohypomonotone.lean) proves the following. Let E be finite-dimensional, F : E → E L-Lipschitz (not necessarily monotone), and G maximally monotone with an exact resolvent oracle J(γ,·). Suppose F+G is ρ-cohypomonotone with 2ρL < 1, and some zero x\* satisfies ‖x₀−x\*‖ ≤ R. Each F-sample is IID, unbiased, and has variance at most σ² ([setup](../../LongTails/Setups/StochasticCohypomonotoneInclusion.lean)). Under these conditions, the [algorithm](../../LongTails/Algorithms/RegularizedProxExtragradient.lean) (accumulative regularization stages, each solved by mini-batched prox-EG+, then one final forward–backward step) outputs (x̄,u) with u ∈ G(x̄) on every sample path and **E‖F(x̄)+u‖ ≤ ε**. It uses a fixed number of calls, and both F-samples and resolvent calls are counted.

**Complexity** (directly from the Lean `budget`), with τ = 1−2ρL ∈ (0,1]:

  O( (1−2ρL)⁻⁸ · (1 + LR/ε + σ²/ε²) · [1 + log(2+LR/ε) + log(2/(1−2ρL))]⁴ ).

L is the Lipschitz constant of F, ρ the cohypomonotonicity modulus, R the initial distance, σ² the variance, and ε the target strong residual. The updates need L, ρ, R, σ and ε. The note's finer bound (log³·loglog on the σ² term) appears only in proof modules; I did not use it.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Alacaoglu–Kim–Wright (AKW), [arXiv 2402.05071](https://arxiv.org/abs/2402.05071) v3, ICML 2024, Cor. 4.1 / Cor. C.5 / Rem. C.7. **Direct competitor** (same constrained/composite stochastic class) | With η=(1+ρL)/(2L): Õ(L²R²σ²/((1−ρL)⁴ε⁴)) (Rem. C.7, ε and σ known) → O(τ⁻⁸(1+LR/ε+σ²/ε²)log⁴) on ρ<1/(2L) | ε⁻⁴ → ε⁻², up to logs. With σ ≥ ε and LR ≥ ε, the speedup is ≳ τ⁸·min(LRσ²/ε³, L²R²/ε²)/log⁴, which is large for small ε at fixed τ | None. AKW covers the broader range ρ < 1/L | Resolvent residual η⁻¹E‖(I−J_{η(F+G)})x_K‖ → strong residual with an exact certificate. Converting AKW's output costs one extra FB step with an O(σ²/ε²) batch | Range halved (ρ<1/(2L) vs <1/L). The factor τ⁻⁸ blows up as ρ→1/(2L), whereas AKW's (1−ρL)⁻⁴ stays bounded there |
| Chen–Luo RAIN++, [arXiv 2208.05925](https://arxiv.org/abs/2208.05925) v4, JMLR 2024, Thm 5.4 + Prop 5.3. **Special case G=0 only** (unconstrained) | Õ(σ²/ε² + LR/ε) *expected* SFO calls → O(τ⁻⁸(1+LR/ε+σ²/ε²)log⁴) | None: same order in ε, σ, L, R. Worse in ρ near 1/(2L) and in logs | G=0 → any maximally monotone G accessed via a resolvent (constraints, prox terms) | Random (MLMC) cost → deterministic budget; output criterion is the same | Excludes ρ=1/(2L), which Chen–Luo allow. Polynomial τ⁻⁸ loss |
| Ji–Lan–Zhu AR, [arXiv 2609.04188](https://arxiv.org/abs/2609.04188) v2 (Sep 2026), Thm 2.2; also Alacaoglu [2609.08380](https://arxiv.org/abs/2609.08380). **Special case ρ=0 only** (monotone) | Õ(LR/ε + (σ²/ε²)log³(LR/ε)) for √E res² ≤ ε → at τ=1, O((1+LR/ε+σ²/ε²)log⁴(2+LR/ε)) | Worse: one extra log on σ²/ε² and a log on LR/ε | Monotone F → nonmonotone F with F+G cohypomonotone; projection onto X → general resolvent | None. JLZ's RMS criterion is stronger than E‖·‖ | Same parameter knowledge (L, R, σ) |
| AKW deterministic, Thm 2.1 / Cor. 2.2. **Special case σ=0 only** | O(1 + LR log(e/(1−ρL))/((1−ρL)²ε)) → O(τ⁻⁸(1+LR/ε)log⁴) | Worse: log⁴ factor and τ⁻⁸ | None | None | Narrower ρ range |

**Reduction check and mechanism.** A plausible route is not established. That route would apply RAIN to the Yosida operator (I−J_{γ(F+G)})/γ, which is monotone and cocoercive for γ>ρ, with MLMC-debiased stochastic solves of the strongly monotone composite resolvent. However, Chen–Luo state their theorems only for unconstrained saddle gradients. The composite debiased inner solver and the final certificate are unproved, and AKW (Rem. 4.2, Conclusions) list the constrained ε⁻² case as open. The proof ancestry is the accumulative-regularization template of Allen-Zhu / Chen–Luo / Ji–Lan–Zhu. Its new ingredients are a regularized pairwise inequality, which makes H+Λ(·−c) Minty-strongly monotone and cohypomonotone, a fixed-step EG+ contraction for that operator, and stage-geometry lemmas that replace the monotone distance arguments. This is a real but moderate adaptation.

**Search coverage (2026-10-09).** I read the theorem statements of AKW v3 (Cor. 4.1, Rem. 4.2, Cor. C.5, Rem. C.7) and Chen–Luo v4 (Thm 5.4, Prop 5.3, Cor. 6.1). For Ji–Lan–Zhu (Thm 2.2), Lee–Kim [2609.35631](https://arxiv.org/abs/2609.35631), Tran-Dinh–Nguyen-Trung [2603.15576](https://arxiv.org/abs/2603.15576) and [2508.16791](https://arxiv.org/abs/2508.16791), and Alacaoglu 2609.08380, I relied on abstracts and partial HTML. Those works are monotone-only, or give ε⁻⁴ or worse under mean-square-Lipschitz oracles. AKW's Appendix D was not retrieved. The deterministic AKW row comes from the repository's [AdjointAnchored review](AdjointAnchoredCohypomonotone.md); I did not re-read it. The result entered the repository in commit 76e526f (2026-10-09 02:27 UTC), and I found no later work on this setup. **Note discrepancy:** the companion note presents Ji–Lan–Zhu only as a monotone result. In fact, its accumulative regularization (fixed schedule, mini-batched inner solver, log³ stochastic term) is the closest algorithmic template. My own Monte Carlo check (400k pairs) agrees with the note's constrained example (b) (β=ℓ=0.1, s=1, box Y): the empirical modulus 0.101 ≤ claimed 0.123, with 2ρL ≈ 0.27.

## Conclusion

**Yes. On constrained/composite cohypomonotone problems with ρ < 1/(2L), the proved complexity improves polynomially.** The strongest direct baseline is Alacaoglu–Kim–Wright (ICML 2024), whose stochastic last-iterate guarantee needs about ε⁻⁴ calls:

  AKW: Õ(L²R²σ²/((1−ρL)⁴ε⁴))  →  this result: O((1−2ρL)⁻⁸(1+LR/ε+σ²/ε²)·log⁴(…)).

For fixed ρL < 1/2, σ ≥ ε and LR ≥ ε, the gain is roughly a factor min(LRσ²/ε³, L²R²/ε²) up to logarithms. AKW explicitly posed this as an open question.

The result loses in three ways. It covers only half of AKW's ρ range, and its τ⁻⁸ factor blows up near ρ = 1/(2L). In the unconstrained case, it merely matches Chen–Luo up to logarithms, gaining only a deterministic budget. In the monotone case, it matches Ji–Lan–Zhu and is one log worse. So it beats the literature only where both G ≠ 0 and ρ > 0. A checked convex–nonconcave constrained bilinear game shows that this class contains genuinely nonmonotone instances.

The comparison establishes the gain over the checked baselines. Priority is less certain: the method adapts the accumulative-regularization template that Ji–Lan–Zhu published a month earlier for the monotone case. I could not rule out a short Yosida-plus-MLMC derivation of the same rate, although none is published and AKW calls the problem open.

What can be claimed is the first verified Õ(LR/ε + σ²/ε²) bound for stochastic constrained/composite cohypomonotone inclusions with ρ < 1/(2L), which answers half of AKW's open question.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
