# Novelty assessment: LocalReferenceDuelingLowerBound

[Theorem](../../LongTails/Theorems/LocalReferenceDuelingLowerBound.lean) · [setup](../../LongTails/Setups/FlatTransferDueling.lean) (specializing [StronglyConvexDueling](../../LongTails/Setups/StronglyConvexDueling.lean)) · [hard family](../../LongTails/Proofs/DuelingSignFamily.lean), [link](../../LongTails/Proofs/DuelingFlatTransfer.lean), [minimax proof](../../LongTails/Proofs/DuelingReferenceLowerBound.lean). Here is what the theorem proves. Fix d ≥ 1, j ≥ 0 and 0 < ε ≤ 1/64. The loss is ½-strongly convex, 2-smooth and 4-Lipschitz on the unit ball B_d. The comparison oracle returns IID one-bit answers with mean ρ(f(x)−f(y)), where ρ is odd, C¹ and bounded, and (2j+1)|t|^{2j}/8 ≤ ρ′(t) ≤ (2j+1)/4 for |t| ≤ 1. Against this oracle, every randomized adaptive algorithm with any budget b ≤ budget fails to return a feasible point x̂ with E[f(x̂) − min_B f] ≤ ε. No algorithm restriction is imposed. The hard instance is f_θ(x) = Σᵢ ½xᵢ² − ¼θᵢh²sin((xᵢ−θᵢh/4)/h) with h² = 1024ε/d, together with the link ρ(t) = arctan(t^{2j+1})/4. It does not depend on the realized seed.

**Necessary comparisons (d = dimension, j = flatness index of the link, ε = accuracy):**

$$N \;\ge\; \Big\lfloor \tfrac{d^2}{65536\,(2j+1)^2\,\varepsilon^2}\Big\rfloor \;=\; \Omega\!\Big(\tfrac{d^2}{(2j+1)^2\varepsilon^2}\Big),\qquad 0<\varepsilon\le 1/64 .$$

The [paired upper theorem](../../LongTails/Theorems/LocalReferenceDueling.lean) uses C = 32, 4/μ = 8 and k = 2j. On the same class it gives O(d²·2^{52j}/((2j+1)²ε) + d²·2^{104j}/((2j+1)²ε²)). The two bounds match as Θ(d²/ε²) for each fixed j, with a gap of 2^{104j} in j (and about 10¹² in constants).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Kumagai, [arXiv 1711.07693v2, Dec 2017](https://arxiv.org/abs/1711.07693), Thm 14 (via Shamir Thm 7). Applies only to the probit link ρ(t)=2Φ(t/√2)−1, on the unit ball, for ½-strongly convex, 3.5-smooth losses. | E gap ≥ 0.004·min{1, d/√(2T)}, i.e. T ≥ 8·10⁻⁶ d²/ε² for ε < 0.004 → ⌊d²/(65536(2j+1)²ε²)⌋ | None at j=0: same order. Not comparable for j ≥ 1: the variance-2 probit link violates the j-envelope, and for j ≥ 2 no rescaled probit satisfies it. | Probit link only → every odd flat link order 2j+1 (ρ′(0)=0 allowed). The constants differ: ρ′(0)=1/√π vs M=1/4, and L=3.5 vs L=2. Neither class contains the other. | None: both give expected gap of any output against arbitrary randomized adaptive algorithms. | Uses the bounded-slope link family instead of a Gaussian-noise reduction. Lower bound shrinks by (2j+1)². ε ≤ 1/64. |
| Jamieson–Nowak–Recht, [NeurIPS 2012](https://proceedings.neurips.cc/paper_files/paper/2012/file/e6d8545daa42d5ced125a4bf747b3688-Paper.pdf) ([arXiv v1](https://arxiv.org/abs/1209.2434)), Thm 1 with κ−1 = 2j+1. Applies only to an ℓ∞ domain whose radius shrinks with T (Lemma 1). | T ≳ d/ε^{2(2j+1)} on shrinking domains → Ω(d²/((2j+1)²ε²)) on a fixed ball | Not comparable: different domain regime. Theirs has the larger ε-exponent; this one has d² instead of d. | Accuracy-dependent query cube → fixed unit ball. | None | Fixed constants (μ,L,G,r,c,M). Their reliability-margin class is wider. |

**Reduction check and mechanism.** For j = 0, the rate follows by composing two known results. Shamir's Thm 7 ([COLT 2013](https://proceedings.mlr.press/v30/Shamir13.pdf)) gives the value-query bound, and two Gaussian value queries simulate one probit comparison, which is exactly Kumagai's Thm 14. That composition gives the same d²/ε² order on an overlapping fixed-ball class. Only the constants (M, L) are not literally inside FlatTransferDueling.

For j ≥ 2 (and for exactly arctan-type links), the Gaussian simulation is unavailable, because a link bounded by 1/4 whose derivative vanishes at 0 is not 2F_{ξ−ξ′}−1 for any IID noise. The proof therefore repeats Shamir's mechanism (proof ancestry):

- a sign-hypercube family whose one-coordinate flips change f by O(h²) uniformly on the domain;
- Assouad averaging over the hypercube;
- per-query divergence O(M²h⁴), where Gaussian KL is replaced by a Bernoulli affinity bound and sup ρ′ ≤ (2j+1)/4.

No new information-theoretic step beyond this substitution was found.

**Search coverage (2026-11-18).** I read the theorem statements and proofs of Shamir 2013 (Thm 7, App. B.4), Jamieson et al. (Thm 1, Lemma 1), Kumagai 2017 (Thms 14–15) and Saha–Koren–Mansour ICML 2025 (Assumption 1, Thm 4). I also read the remark in Saha et al. ICML 2021 (Thm 7, Remark 3), which covers the sign link and so does not apply here. Web searches for later comparison-oracle lower bounds found no fixed-ball flat-link result. The NeurIPS camera-ready version of Jamieson et al. was not readable, so I used arXiv v1.

The theorem was introduced in commit b1eee6b6 (2026-11-18/19). The companion note cites Shamir but says his calculation "does not directly cover" one-bit comparisons. It omits Kumagai's Thm 14, which already gives Θ(d²/ε²)-type hardness for probit comparisons on the unit ball.

**Conclusion**

**No new rate: the Ω(d²/ε²) fixed-ball comparison lower bound was already known for linear-at-ties links, and the new part is a routine extension to flat links.** The strongest baseline is Kumagai (2017, Thm 14), which applies Shamir's Theorem 7 through a two-query Gaussian simulation:

| Class | Lower bound on comparisons |
|---|---|
| Probit link, unit ball, μ=½, L=3.5 (Kumagai) | ≥ 8·10⁻⁶ d²/ε² |
| Odd links of order 2j+1, unit ball, μ=½, L=2 (this) | ≥ d²/(65536(2j+1)²ε²) |

At j = 0 the order is identical, and only the class constants differ. For flatter links (j ≥ 1, where ρ′(0) = 0), the theorem covers links that the Gaussian reduction cannot produce. It shows that flatness at ties does not lower hardness below d²/ε² on a fixed ball. However, the proof is Shamir's uniform-perturbation Assouad argument with a Bernoulli divergence in place of Gaussian KL, and the guarantee gets weaker by (2j+1)² rather than stronger.

Its useful role is to pair with the repository's upper bound and certify Θ(d²/ε²) for each fixed j. Even so, the j-dependence is open by a factor of 2^{104j}, and no lower bound tracks μ, L, G, c, M or a shrinking window r. What can be claimed is an exact, seed-independent, machine-checked fixed-ball lower bound for the normalized flat-link dueling class, which extends a known probit-link result.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
