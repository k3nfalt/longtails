# GeneralizedMintyLowerBound: an (L₁R)² lower bound for generalized-Lipschitz Minty root finding

[`result`](../../LongTails/Theorems/GeneralizedMintyLowerBound.lean) proves the following on the [setup](../../LongTails/Setups/HighDimensionalGeneralizedMinty.lean) (which restricts [GeneralizedLipschitzMinty](../../LongTails/Setups/GeneralizedLipschitzMinty.lean)). Take any valid parameters, any randomized algorithm (no `allowedAlgorithm` restriction), and any budget `b ≤ ⌊(T/1024)²⌋`, including zero. Then some deterministic exact oracle and some continuous operator F fail the algorithm: F has a zero z with ‖x₀−z‖ ≤ R, satisfies ⟨F(x),x−z⟩ ≥ 0 for all x, and satisfies ‖F(x)−F(y)‖ ≤ (L₀+L₁ max_{[x,y]}‖F‖)‖x−y‖. The algorithm's returned point either has a non-integrable residual or E‖F(X)‖ > ε. The instance ([hard field](../../LongTails/Proofs/GeneralizedMintyChain.lean), [construction](../../LongTails/Proofs/GeneralizedMintyLowerBound.lean)) depends on the algorithm and b, not on the seed. The upper-bound counterpart is the [extragradient algorithm](../../LongTails/Algorithms/GeneralizedMintyExtragradient.lean).

**Necessary oracle calls.** L₀ is the base Lipschitz constant, L₁ the relative constant, R the initial distance, ε the residual accuracy and d the dimension:

  Ω( (L₀R/ε)² + (L₁R)² ),  valid when R(L₀/ε+L₁) ≥ 1024,  32·log(1+L₁ε/L₀) ≤ L₁R,  and d ≥ 8192·(1+⌊(R(L₀/ε+L₁)/1024)²⌋)³.

The second condition only matters when L₁ > 0. It means ε ≤ (L₀/L₁)(e^{L₁R/32}−1). The regime is nonempty: for example L₀=R=ε=1 and L₁ ≥ 1023.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository Lipschitz Minty lower bound [EuclideanWeakMintyLowerBound](../../LongTails/Theorems/EuclideanWeakMintyLowerBound.lean) (commit 98684e93, 2026‑11‑17, prior). Applied with L = L₀, since L₀-Lipschitz ⊂ (L₀,L₁) class | Ω((L₀R/ε)²), for d ≥ 257(L₀R/28ε)⁶ → Ω((L₀R/ε)² + (L₁R)²) | New (L₁R)² term. Gain factor ≈ (L₁ε/L₀)² when L₁ε ≥ L₀ and ε ≤ (L₀/L₁)(e^{L₁R/32}−1). None when L₁ε ≤ L₀ | None: same class (exact residual, Minty at ρ=0) | None | Worse constants (1/1024² vs 1/28²), dimension requirement of order T⁶ with a larger constant, and the log window on ε |
| Rudomanov–Fomin–Gasnikov–Stonyakin, [arXiv:2611.20296v1](https://arxiv.org/abs/2611.20296) Thm 2.8 lower bound (preprint, 15 Nov 2026, prior). Monotone operators with a zero, which is a subclass of Minty, so the bound transfers | Ω(1 + L₀R/ε + (L₁R)^{6/5}/log^{4/5}(2+L₁R)), for L₀R/ε ≥ 1 → Ω((L₀R/ε)² + (L₁R)²) | L₁R exponent 6/5 → 2, and the log is removed. Example: L₀=R=ε=1, L₁→∞ gives L₁^{6/5}/log^{4/5}L₁ → L₁² | Not comparable classes: the monotone hard class is narrower. The new bound needs non-monotone Minty instances, so it does not lower-bound monotone problems | None | It does not apply to monotone operators, where the upper bound O(1+L₀R/ε+(L₁R)^{6/5}) holds. Their dimension requirement was not verified |
| Upper bound for gap check: [Choudhury–Loizou](https://arxiv.org/abs/2510.22421) (NeurIPS 2025) EG analysis, via the repository's [GeneralizedMintyExtragradient](../../LongTails/Theorems/GeneralizedMintyExtragradient.lean) | O(R²(L₀/ε+L₁)²) upper, in any dimension | Closes the gap to a universal constant (≈ 64·1024²) inside the stated regime | — | — | The lower bound needs high dimension. For (L₀/L₁)(e^{L₁R/32}−1) < ε < (L₀/L₁)(e^{L₁R}−1) the bound remains open |

**Reduction check.** None of the standard reductions gives the (L₁R)² term:
- An L-Lipschitz instance with L ≈ L₀+L₁ε violates the generalized condition near the zero, where the local slope must be at most about L₀.
- Rescaling F → cF changes only L₀.
- An exponential residual remapping yields only about (L₁R/log(1+L₁ε/L₀))² links, which can stay bounded in the regime covered here.

The new mechanism multiplies the classical Minty chain by e^{min(log M, L₁D(x)/2)}, where D is a 1-Lipschitz deficit of a whole group of hidden tail coordinates. As a result, the multiplier sits on its plateau M = 1+L₁ε/L₀ at every unexposed probe, and the regularity bound is paid by a residual of at least κr/4. Proof ancestry is the random-embedding chain technique (Woodworth–Srebro; Carmon et al.) and the repository's Lipschitz Minty chain. Those supply the hiding argument and the base field. The amplification and its segment-regularity proof are the added work.

**Search coverage (2026‑11‑21).** I searched arXiv and the NeurIPS/ICLR/ICML pages for generalized-smooth VI and Minty lower bounds. I found no prior non-monotone (L₀,L₁) VI lower bound. The Rudomanov lower bound was confirmed from the verbatim Thm 2.8 display; the later sections were read only partially. I did not read Choudhury–Loizou Thm 3.6 verbatim. Outside the repository I found no literature source for the (L₀R/ε)² Minty term; Perseus (arXiv:2205.03202) calls Minty lower bounds largely unexplored. The companion note's "Θ(T²)" is accurate only up to a large universal constant, with the dimension and log-window restrictions.

## Conclusion

**Yes: the bound proves a new, larger necessary cost for Minty root finding when L₁ε ≫ L₀.** Before this result, two lower bounds applied to this class. The repository's Lipschitz Minty bound gives (L₀R/ε)². The monotone bound of Rudomanov et al. (Nov 2026) also transfers here, since monotone operators with a zero satisfy the Minty condition; it gives (L₁R)^{6/5} up to logs. Together they gave:

| | necessary calls |
|---|---|
| previous best | (L₀R/ε)² + (L₁R)^{6/5}/log^{4/5}(2+L₁R) |
| this result | (L₀R/ε)² + (L₁R)² |
| extragradient upper | (L₀R/ε)² + (L₁R)² |

The gain applies for L₀ ≪ L₁ε ≤ (L₀/L₁)e^{L₁R/32}. For example, L₀=R=ε=1 and large L₁ gives L₁² instead of L₁^{6/5}. The new bound matches extragradient up to a universal constant there. This separates the Minty class from monotone operators, where (L₁R)^{6/5} suffices. When L₁ε ≤ L₀ it adds nothing beyond the Lipschitz bound.

The limits are a dimension requirement of order T⁶, large constants, and an open window of moderately large ε. The comparison proves the gain. Priority rests on a search of very recent preprints that found no competitor, which is weaker evidence.

What can be claimed: the first tight (L₁R)² lower bound for generalized-Lipschitz Minty problems, obtained by a non-routine amplified hard instance.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
