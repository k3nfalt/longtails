# StochasticConstrainedGeneralizedMonotone: novelty assessment

The [theorem](../../LongTails/Theorems/StochasticConstrainedGeneralizedMonotone.lean) uses the [setup](../../LongTails/Setups/StochasticConstrainedGeneralizedMonotone.lean) and the [algorithm](../../LongTails/Algorithms/ProjectedClippedExtragradient.lean). It covers a continuous, globally monotone, (L₀,L₁)-Lipschitz operator F on a finite-dimensional space, a convex set X reached through exact projections, and unbiased stochastic evaluations of F with variance at most σ² drawn IID. Under these assumptions, the returned point Y is feasible and some η ∈ N_X(Y) gives ‖F(Y)+η‖ ≤ ε, all with probability at least 1−δ.

**Complexity.** Here R ≥ ‖x₀−x⋆‖ and G ≥ ‖F(x⋆)‖ refer to the same VI solution x⋆. Assume L₀>0, R>0 and 0<δ<1, and write Λ = 2+(L₀+L₁G+L₁ε)(1+L₁R)R/ε. The bound counts stochastic-operator calls plus projection calls:

  O( [ (L₀+L₁G)(1+L₁R)²R/ε + (1+L₁R)⁴ + σ²/ε² ] · log³Λ · log(Λ/δ) ).

This is read off the per-channel ceiling `budget` (2¹²⁸ constant), and it holds for both channels.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Ji–Lan–Zhu, [arXiv:2609.04188v2](https://arxiv.org/abs/2609.04188) (preprint, 3/17 Sep 2026), Thm 2.2, AR+SOE. **Special case L₁=0** (global L-Lipschitz). | Their bound guarantees √E[res²] ≤ ε with Õ(LR/ε + σ²/ε²·log³(LR/ε)). Converted by Markov to probability 1−δ: Õ(LR/(ε√δ) + σ²/(ε²δ)). This result at L₁=0: O((L₀R/ε+1+σ²/ε²)·log³Λ·log(Λ/δ)). | In expectation: none, same order. In high probability with finite variance: the δ⁻¹ᐟ² and δ⁻¹ factors become log(1/δ), compared only against this Markov conversion. | Global L-Lipschitz → (L₀,L₁)-Lipschitz, with polynomial dependence on L₁R. | Expected squared residual → high-probability residual at the returned point. | Requires the extra public bound G on ‖F(x⋆)‖. Uses log⁴ rather than log³ factors. The light-tailed high-probability result in their §4 was not read. |
| Vankov–Nedić–Sankar, [arXiv:2410.12334v2](https://arxiv.org/abs/2410.12334), TMLR. Thm 4.4: clipped projected/Korpelevich methods. | Their rates bound E[dist²] to the solution set under p-quasi-sharpness (Assump. 2.4, μ>0) for α ≤ ½. This result is a residual bound at α=1 under monotonicity. | Not comparable: different accuracy criterion and incomparable classes. | p-quasi-sharp (μ>0) → plain monotone (their μ=0 case is listed as open). Their α ≤ ½ → α = 1. | Distance in expectation → residual with probability 1−δ. | Global monotonicity. Their class includes non-monotone quasi-sharp operators. |
| Greenberg–Loizou, [arXiv:2610.16886v1](https://arxiv.org/abs/2610.16886) (12 Oct 2026). Thms 3.1–3.2: EG/PEG, **deterministic**. | O((L₀+L₁M₁)R²/ε) for an averaged restricted gap, where M₁ ~ G+R(L₀+L₁G)e^{L₁R}. Not converted to residual. | Not comparable: different criterion. Their constant is exponential in L₁R, this one polynomial. | Exact F → finite-variance stochastic F. | Averaged restricted gap → residual at the last returned point. | At σ=0 the repository's [exact constrained result](../../LongTails/Theorems/ConstrainedGeneralizedMonotone.lean) is better by a factor (1+L₁R) and drops the (1+L₁R)⁴ term. |

**Reduction check.** I checked three standard reductions; none gives the result.
- *Localizing to a ball and applying a Lipschitz theorem.* The local Lipschitz constant is of order (L₀+L₁G)e^{O(L₁R)}, so the reduction gives an exponential rather than polynomial dependence. It also needs projections onto X∩B, which the oracle does not provide.
- *Applying the [unconstrained stochastic theorem](../../LongTails/Theorems/StochasticGeneralizedMonotone.lean) to the projection normal map.* This fails because that map is not monotone. I verified the note's counterexample: X={x₂≥0}, F=(−x₂,x₁), points differing by (1,−γ/2), inner product −γ/4.
- *Accumulative regularization* is proof ancestry from Ji–Lan–Zhu (Prop. 1). The clipped stochastic-stage structure is inherited from the repository's unconstrained result. What is new is the stage contraction when projection cancels a saturated clipped step, with noise kept additive.

**Search coverage.** Searched on 2026-10-24 UTC: arXiv 2024–Oct 2026 work on (L₀,L₁)/generalized-smooth VIs, including Chu–Liu–Huang [arXiv:2610.14839](https://arxiv.org/abs/2610.14839) (quasi-sharp), Sadiev et al. [ICML 2023](https://proceedings.mlr.press/v202/sadiev23a.html) (Lipschitz) and stochastic Halpern work. I read the theorem statements cited above. Not verified: Ji–Lan–Zhu §4 (light-tailed high probability). No conference search was exhaustive. The companion note's citations and its claims about those papers match what I checked. The result entered the repository on 2026-10-24 (commit cc147db), so all three baselines predate it.

**Conclusion**

**Yes, the scope is broader. The rate is not better where earlier methods apply.** No checked paper gives a polynomial, residual-type guarantee for stochastic, constrained, monotone VIs under (L₀,L₁)-smoothness.
- Vankov et al. need quasi-sharpness.
- Greenberg–Loizou are deterministic, measure an averaged gap, and have constants exponential in L₁R.
- Ji–Lan–Zhu need global Lipschitzness.

The closest baseline is the Lipschitz case of Ji–Lan–Zhu:

| L₁ = 0 | Expected residual | Residual with prob. 1−δ |
|---|---|---|
| Ji–Lan–Zhu | Õ(LR/ε + σ²/ε²) | Õ(LR/(ε√δ) + σ²/(ε²δ)), via Markov |
| This result | same order | Õ((L₀R/ε + σ²/ε²)·log(1/δ)) |

On that overlap there is no gain in ε, and there is one extra logarithm. The δ gain is only against the Markov conversion; their own high-probability theorem was not checked. For L₁>0, the new instances include strictly convex objectives on a half-space with a nonzero boundary normal at the solution: generalized-smooth but not globally Lipschitz, with no quasi-sharpness.

The costs are an extra public bound G on ‖F(x⋆)‖, and the factors (1+L₁R)² and (1+L₁R)⁴. At σ=0 the method is worse than the repository's exact solver. Priority is plausible but rests on preprints from the last two months.

What can be claimed: the first checked polynomial high-probability residual guarantee for this stochastic constrained generalized-smooth class, matching the Lipschitz order up to logarithms.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
