# Novelty assessment: StretchedExponentialMarkovConvexLowerBound

For every valid parameter choice, every randomized adaptive algorithm, and every budget `b ≤ B`, [the theorem](../../LongTails/Theorems/StretchedExponentialMarkovConvexLowerBound.lean) builds an admissible convex `L`-smooth instance on which the expected objective gap of the output is larger than `ε`. The instance has a stationary Markov gradient oracle whose stationary α-moment is bounded and whose π-averaged TV distance satisfies `∫‖κᵗ(z,·)−π‖_TV dπ(z) ≤ exp(−(t/τ)^γ)` ([setup](../../LongTails/Setups/StretchedExponentialMarkovConvex.lean), [hard model](../../LongTails/Proofs/StretchedExponentialLowerModel.lean)). The setup places no restriction on the algorithm, so this is a lower bound for the whole problem class.

**Proved necessary budget.** Write `k = α/(α−1)`, where `σ` is the α-moment scale, `R` bounds the initial distance, `τ` is the mixing scale, and `γ` is the stretch exponent. Then

  B + 1 > τ (σR/(8ε))ᵏ (k·log(σR/(8ε))/2)^{1/γ} / 32 ≥ c_{α,γ} · τ (σR/ε)ᵏ · log^{1/γ}((σR/ε)ᵏ),  with c_{α,γ} = 1/(32·8ᵏ·5^{1/γ}).

This holds on the domain `1<α≤2`, `0<γ≤1`, `τ≥1`, `32ε ≤ σR`, and `4ε ≤ LR² ≤ ε(σR/ε)ᵏ`, which is the noise-dominated regime. The regime is nonempty: the note gives the witness `L=R=σ=τ=γ=1`, `α=2`, `ε=1/1024`, and the setup's valid-parameter conditions confirm it. At the boundary the floor `B` can be zero. The hard instances are 1-D-embedded quadratics `(2ε/R²)‖x−x₀∓c‖²`, built in every dimension. They are driven by a "countdown" chain, which with small probability starts an excursion of length `H ≈ τ(log(1/q))^{1/γ}`. The rare state has stationary mass `q = (8ε/σR)ᵏ`. The sign of the instance depends on the algorithm but not on its seed.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Sarkar–Chakrabartty–Aggarwal, [arXiv:2606.26316v1](https://arxiv.org/abs/2606.26316) (June 2026, preprint), Thm 4: sticky-chain heavy-tail lower bound for PL quadratics against all estimators. *Applies only after reduction*: their uniform mixing `sup_z TV ≤ 2^{−⌊m/t_mix⌋}` implies the averaged envelope when `t_mix ≍ τ`, their constant-probability bound gives an expectation bound, and taking `μ ≍ ε/R²` turns it into an objective-gap bound | Ω(τ(σR/ε)ᵏ) → Ω(τ(σR/ε)ᵏ log^{1/γ}((σR/ε)ᵏ)) | Larger by a `(k log(σR/ε))^{1/γ}` factor, everywhere in the valid regime (the regime requires `σR/ε ≥ 32`) | None. Both use stationary moment conditions; the averaged-mixing class contains the uniformly mixing one | None. Both bound expected or constant-probability gaps for arbitrary algorithms | Their lower bound holds under the stronger *uniform* mixing assumption. The log factor here comes from the rare states having small π-mass, which only averaged mixing allows; it is not shown under uniform mixing. Their reduction constants were not rechecked |
| Beznosikov et al., [NeurIPS 2023 / arXiv:2305.15938v2](https://arxiv.org/abs/2305.15938), Thm 2. *Special case only*: α=2, strongly convex, distance criterion, uniform mixing | Noise term `Ω(τσ²/(μ²ε))`, with no log on τ (conversion to a convex gap at α=2 is not checked; it would give at most `τ(σR/ε)²`) → `τ(σR/ε)² log^{1/γ}((σR/ε)²)` at α=2 | At most a log factor, and only after an unchecked conversion | Allows heavy tails (1<α≤2) and averaged mixing | None | Their bound includes a `τ√(L/μ)log(1/ε)` initialization term; this result covers only the noise-dominated regime |
| Repo upper bound [StretchedExponentialMarkovConvexUpperBound](../../LongTails/Theorems/StretchedExponentialMarkovConvexUpperBound.lean), obtained by substitution into [AcceleratedHeavyTailedMarkovConvex](../../LongTails/Theorems/AcceleratedHeavyTailedMarkovConvex.lean). This is the gap to the upper bound, not a competitor | Upper `O_{α,γ}(τ(σR/ε)ᵏ log^{1/γ}((σR/ε)ᵏ))` ↔ the lower bound above | Tight up to constants depending on α and γ | – | – | The proved constant ratio is of order `2048ᵏ·(5(1+log(256+64·256ᵏ))/γ)^{1/γ}`, so the bounds are not uniformly tight as α→1 or γ→0 |

**Reduction check and proof ancestry.** Sticky refresh chains cannot reproduce the bound. A chain with refresh rate λ has averaged TV of about `2q e^{−λt}`, and fitting the envelope for all `t` forces `λτ ≳ 1` when γ=1, so it gives only `τ(σR/ε)ᵏ`. The new ingredient is calibrating finite deterministic excursions so that the averaged envelope holds at every integer `t` ([mixing](../../LongTails/Proofs/CountdownMixing.lean), [calibration](../../LongTails/Proofs/CountdownCalibration.lean)). Two pieces are inherited:
- **Two-instance identical-execution testing**, as in sticky-chain lower bounds (Sarkar et al.; repository PR #162, not in this tree and not checked).
- **Excursions forcing logarithms under geometric ergodicity**, from Adamczak ([arXiv:0709.3110](https://arxiv.org/abs/0709.3110), §3.3), whose setting is empirical-sum concentration, not optimization.

One observation sharpens the motivation: for a stationary chain, the π-averaged TV in the setup is exactly the β-mixing coefficient. The setup is therefore standard stretched-exponential β-mixing, not an ad hoc assumption.

**Search coverage (2026-11-14 UTC).** I searched the web for lower bounds on Markov, β-mixing and heavy-tailed stochastic optimization, and read the lower-bound sections of 2305.15938v2 and 2606.26316v1. For both papers I had partial and partly summarized access, so the theorem statements above are not verbatim-verified. Mulumudi et al. ([arXiv:2602.18053v1](https://arxiv.org/abs/2602.18053), Feb 2026) claim a CVaR minimax rate with an `n/log n` effective sample size under stretched-exponential β-mixing (Thm 3.4). I could not verify its statement, its γ-dependence, or the estimator class it covers; it is a different problem but the same log phenomenon. The classical IID heavy-tail lower bound `Ω((σR/ε)ᵏ)` (Nemirovski–Yudin) was not re-checked. The result was introduced in commit `89bcdaf8` on 2026-11-13. The companion note's claims match the Lean statement.

**Conclusion**

**Yes, but only by a polylogarithmic factor: the necessary budget rises from τ(σR/ε)ᵏ to τ(σR/ε)ᵏ·log^{1/γ}, which matches the known upper bound.**

The strongest prior all-algorithm lower bound I could connect to this class is the sticky-chain bound of Sarkar et al. (uniform mixing). After the reduction above, it gives Ω(τ(σR/ε)ᵏ). Here, with S = (σR/ε)^{α/(α−1)}:

| | Necessary oracle calls |
|---|---|
| Prior (via uniform-mixing reduction) | Ω(τ S) |
| This theorem | Ω_{α,γ}(τ S (log S)^{1/γ}) |
| Upper bound (repository) | O_{α,γ}(τ S (log S)^{1/γ}) |

The result therefore settles complexity up to constants depending on α and γ, for convex smooth heavy-tailed problems under stretched-exponential β-mixing in the noise-dominated regime `LR²/ε ≤ S`. It shows that the mixing-time logarithm in the upper bound is necessary, not an artifact of the proof.

The gain is modest for concrete reasons. It is a log factor, a large one only when γ is small. It depends on the averaged (β-mixing) model, and uniform-mixing lower bounds have no such factor. Its mechanism combines known excursion and two-point testing ideas. Priority is also uncertain: the CVaR paper claims a related log-n phenomenon under the same mixing condition, and I could not verify it. What can be claimed is a new, fully explicit tight lower bound that makes the logarithmic mixing cost necessary for this oracle class.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
