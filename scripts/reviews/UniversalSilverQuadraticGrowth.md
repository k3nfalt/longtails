# UniversalSilverQuadraticGrowth: μ-oblivious, horizon-free silver-block GD under quadratic growth

[`result`](../../LongTails/Theorems/UniversalSilverQuadraticGrowth.lean) proves the following for an exact-gradient L-smooth convex f on a Hilbert space whose minimizer set has quadratic growth with constant μ. Gradient descent with one predetermined stepsize sequence that depends only on L reaches last-iterate accuracy f(x_K) − f(x⋆) ≤ ε at K = `budget`. The sequence uses fresh convex silver blocks in ruler (Luby) order ([setup](../../LongTails/Setups/SmoothConvexQuadraticGrowth.lean), [algorithm](../../LongTails/Algorithms/UniversalSilver.lean)). The proof lemma `UniversalSilverRate.accuracy` gives the same accuracy at every K above the internal threshold, so the guarantee is anytime; the exported theorem states only K = budget.

**Complexity.** L is the smoothness constant, μ the quadratic-growth constant, R ≥ ‖x₀ − x⋆‖, and ε the target accuracy. Writing p = log 2/log(1+√2) ≈ 0.7864, the proved budget is

  O( (1 + L/μ)^p · log(2 + LR²/ε) · [ log(2 + L/μ) + log log(2 + LR²/ε) ] )

gradient calls. Here 2 + LR²/ε ≥ 2, so the log log term is finite. No μ, R, ε or K enters the updates; they enter only the budget.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Fercoq–Qu, adaptively restarted AGD ([arXiv 1709.02300](https://arxiv.org/abs/1709.02300), Thm 2 / Table 1; IMA J. Numer. Anal. 2019) | O(√(L/μ)·log(L·LR²/(με))) after converting their gradient-mapping stopping test to objective gap via QG (f − f⋆ ≤ 2‖∇f‖²/μ) → the bound above | **Worse:** larger by roughly a (L/μ)^0.286 factor times the log κ / log log factor, for all large L/μ | None. Theirs needs QG only on the initial sublevel set, a weaker condition than this global QG | Both are μ-free in their updates. Theirs adaptively restarts AGD with a stopped output; this result uses predetermined GD with an anytime last iterate | This result restricts the algorithm to GD |
| Zhang–Lee–Du–Chen ([arXiv 2411.17668](https://arxiv.org/abs/2411.17668) v2, Thm 11; COLT 2025, PMLR 291) | O((L/μ)^0.893·log(LR²/ε)), anytime, strongly convex → the bound above | Exponent 0.893 → 0.786. The displayed bound wins only once (L/μ)^0.107 exceeds a constant times log(L/μ) + log log(LR²/ε). Zhang's constant is unspecified; at constant 1 the crossover is beyond L/μ ≈ 10¹⁵ | μ-strong convexity → QG (covers, for example, rank-deficient least squares) | Schedule depends on μ (Thm 11 picks τ(μ)) → depends on L only | Extra log κ + log log factor from universal interleaving |
| Altschuler–Parrilo silver schedule ([arXiv 2309.07879](https://arxiv.org/abs/2309.07879), J. ACM 2025); known-κ restart of convex long steps under PL (Grimmer–Shu–Wang, [arXiv 2403.14045](https://arxiv.org/abs/2403.14045), Remark 3) | O((L/μ)^p·log(LR²/ε)) at horizons fixed in advance → the bound above | **Worse** by the factor log(L/μ) + log log(LR²/ε) | Strong convexity → QG (Grimmer–Shu–Wang already allow PL) | κ and horizon needed → neither needed, anytime | None beyond the log factor |
| Constant step 1/L (textbook, QG/PL) | O((L/μ)·log(LR²/ε)), anytime, μ-free → the bound above | (L/μ)^0.214 gain up to logs. With explicit constants it pays off only for L/μ ≳ 10⁹–10¹⁰ | None | None (both μ-free and anytime) | Larger constants |

**Reduction check.** Evaluating the result only at block boundaries is a direct composition of three known pieces: the convex silver certificate (Altschuler–Parrilo II, [arXiv 2309.16530](https://arxiv.org/abs/2309.16530), Thm 1.1/3.4), QG-based halving, and Luby's universal restart sequence (scheduled restarts with unknown sharpness: Roulet–d'Aspremont, [arXiv 1702.03828](https://arxiv.org/abs/1702.03828), Prop. 2.4). Those pieces are proof ancestry, not complexity baselines. The genuinely new step for the anytime claim is the elementary lemma `SilverNonexpansive.nonexpansive`: every intermediate silver iterate stays within the block-start distance to every minimizer. I checked its key identity: (μ_k−1)² − (S_k+1)² = ρ^{2k−2} − ρ^{2k} ≤ 0. I did not find this lemma in Altschuler–Parrilo I/II, Zhang et al., or the 2026 survey ([arXiv 2605.31386](https://arxiv.org/abs/2605.31386)). The Ye–Liu lower bound ([arXiv 2609.26873](https://arxiv.org/abs/2609.26873), 22 Sep 2026) covers κ-dependent fixed-horizon schedules. It therefore applies to this schedule, so the exponent 0.786 is optimal up to κ^{o(1)} and logarithmic factors.

**Search coverage (2026-10-23).** I searched arXiv and PMLR for silver/long-step schedules, anytime GD, unknown-μ restarts, and 2026 lower bounds (2607.02053, 2609.02855, 2609.04032, 2609.09152, 2609.26873). The result was introduced on 2026-10-23 (commit 3f13d4d), so every cited work predates it. I found no μ-free or anytime silver-rate guarantee. The companion note says Kornowski–Shamir raised the strongly convex anytime question; they do mention it ([arXiv 2406.13888](https://arxiv.org/abs/2406.13888), §1), but without asking for μ-independence. The note's ~10²⁰ crossover against Zhang depends on Zhang's unspecified constant.

**Conclusion**

**No problem-class improvement; the gain is confined to predetermined-stepsize GD, where it is real but mostly asymptotic.** On smooth convex functions with quadratic growth, restarted AGD with unknown μ (Fercoq–Qu) is already faster for every large condition number:

| Method | Gradient calls |
|---|---|
| Fercoq–Qu restarted AGD | √(L/μ) · log(L·LR²/(με)) |
| This result (GD) | (L/μ)^0.786 · log(LR²/ε) · [log(L/μ) + log log(LR²/ε)] |

Within plain GD with fixed stepsizes, the result is the first I found that is μ-oblivious, anytime, valid under QG, and at the lower-bound exponent 0.786. The previous best anytime GD bound (Zhang et al.) had exponent 0.893 and required μ. Because of the universal schedule's log factor, the displayed bound beats Zhang's, and even the constant step 1/L, only for very large condition numbers (about 10⁹ or more).

The mechanism is a known restart composition plus one short non-expansion lemma. The faster known-κ anytime variant is not formalized. Priority looks plausible from my search, but this does not prove it.

What can be claimed is a sharp, condition-number-free anytime rate for silver-type GD stepsizes. It is not an optimization speedup over accelerated methods.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
