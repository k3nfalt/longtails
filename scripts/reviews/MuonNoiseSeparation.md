# MuonNoiseSeparation: novelty assessment

The [theorem](../../LongTails/Theorems/MuonNoiseSeparation.lean) proves the following for momentum-free batched Muon ([algorithm](../../LongTails/Algorithms/BatchedDirection.lean), `muon`), run on the [setup](../../LongTails/Setups/BatchedSpectralSmooth.lean). The step is η = ε/(2L), the batch size is B = ⌈64s²/ε²⌉+1, and the output is a uniformly random iterate among T+1 = ⌈8LΔ/ε²⌉+1 iterates. For every m, n, and X₀, the output satisfies 𝔼‖∇f(X̂)‖_* ≤ ε.

**Complexity.** The proved budget is B(T+1):

  N = O((1 + s²/ε²)(1 + LΔ/ε²)) = O(1 + s²/ε² + LΔ/ε² + LΔs²/ε⁴).

The parameters mean the following:
- L: smoothness, ‖∇f(X)−∇f(Y)‖_* ≤ L‖X−Y‖_op.
- Δ: an upper bound on f(X₀) − inf f.
- s: an upper bound on Σᵢσᵢ. Here 𝔼‖(G−∇f)ᵀbᵢ‖² ≤ σᵢ² for some fixed orthonormal basis (bᵢ). The oracle is unbiased and IID.
- ε: the target nuclear-norm accuracy.

The constraints are L > 0, Δ, s ≥ 0 and ε > 0.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang, [arXiv 2605.06615](https://arxiv.org/abs/2605.06615) v1 (7 May 2026, preprint), Thm 4: the same Alg. 2, Muon with batch B and no momentum. Applicability: one-sided noise 𝔼[NNᵀ] ⪯ Σ² (Assump. 2b), with s = ‖Σ‖_*. | O(1 + LΔ/ε² + LΔ‖Σ‖_*²/ε⁴) → O(1 + s²/ε² + LΔ/ε² + LΔs²/ε⁴) | None: same order. The new bound is **worse** by an additive s²/ε² when s > ε and 2LΔ ≤ ε²; in that regime X₀ is already ε-stationary. | One-sided covariance → row profile. The row profile is implied by one-sided noise, using the eigenbasis of Σ and σᵢ = λᵢ(Σ). Example below: on some row-profile instances every admissible Σ has ‖Σ‖_* ≥ √r·s. | None. Both are uniformly random (averaged) iterates with the same inputs L, Δ, s, ε. | The smoothness hypothesis is the gradient-Lipschitz form. It implies TYZ's Assump. 3b with the same L. Samples are IID rather than only conditionally independent. Explicit constants are given. |
| Repository: [FiniteVarianceMuonHighProbability](../../LongTails/Theorems/FiniteVarianceMuonHighProbability.lean) (added 2026-10-21). Same smoothness and row-profile class, momentum Muon with one sample per step plus validation. | Zero calls if 2LΔ ≤ ε², else ⌈2⁴⁵A(R + √R·log²(2⁵⁶AR/δ))⌉, with A = 1+s²/ε² and R = 1+LΔ/ε². → Selected bound (expectation) | Not comparable: the criteria differ (probability vs. expectation). | None. It is the same class. | Not comparable. Applying Markov to the selected bound gives only confidence that is polynomial in 1/δ. | The selected result needs no confidence logarithms but gives only an expectation guarantee. |

**Row-profile example.** Take the standard basis and σᵢ = 1, so s = r = m ≤ n. Let N(X,ω) = ω·v_{ε(X)}e₁ᵀ, where ω is Rademacher and v_{ε(X)} ∈ {±1}^m is a measurable sign pattern that takes every value as X varies. Any Σ with Σ² ⪰ vvᵀ for all such v must satisfy tr Σ⁻² ≤ 1, by averaging vᵀΣ⁻²v ≤ 1. The power-mean inequality then gives ‖Σ‖_* ≥ m^{3/2} = √r·s. As stated, TYZ's theorem therefore loses a factor r in the s² term on such instances.

That loss belongs to TYZ's statement, not to their method. Their proof (App. D.1) uses only 𝔼‖N̄‖_* ≤ ‖Σ‖_*/√B. Under the row profile, the same bound with s in place of ‖Σ‖_* follows from ‖N‖_* ≤ Σᵢ‖Nᵀbᵢ‖ and Jensen. The rest of their argument is unchanged.

**Standard-reduction check and proof ancestry.** The proof is TYZ's three-line descent argument with this one-line noise bound, and I found no new mechanism. The proof ancestry runs as follows:
- Bernstein et al., signSGD ([arXiv 1802.04434](https://arxiv.org/abs/1802.04434), ICML 2018), Thm 1: the large-batch sign-descent template. Its rate has the same form in ℓ₁/ℓ∞ geometry with ‖σ‖₁.
- ASGO ([arXiv 2503.20762](https://arxiv.org/abs/2503.20762) v3, App. G): deterministic Muon under nuclear-norm stationarity. ASGO also supplies TYZ's one-sided noise model and Lemma 9.

**Search coverage.** I searched arXiv and the web on 2026-10-23 and read TYZ v1 (Thm 4, App. D.1) and ASGO v3 (Assump. 3, §6). I did not check the following:
- the statements of Hübler–Pethick–Sra ([arXiv 2606.14560](https://arxiv.org/abs/2606.14560), June 2026, heavy-tailed model);
- Chang–Liu–Yuan ([arXiv 2509.15816](https://arxiv.org/abs/2509.15816));
- general-norm LMO analyses such as Pethick et al. and Kovalev.

None of these would make the result more novel. The companion note itself says that the upper bound is TYZ Thm 4 and is not new, and I agree. Its claimed main novelty is the NSGD lower bound, which is a supporting lemma and not this `result`; I did not assess it.

**Conclusion**

**No: this is Tao–Yu–Zhang's existing Muon bound, restated with explicit constants.**

The strongest baseline is TYZ Thm 4 (May 2026, before this result's 2026-10-23 introduction). It covers the same algorithm, output rule, and criterion. On their one-sided noise class, with s = ‖Σ‖_*:

| | Oracle calls for 𝔼‖∇f(X̂)‖_* ≤ ε |
|---|---|
| TYZ Thm 4 | O(1 + LΔ/ε² + LΔs²/ε⁴) |
| This result | O(1 + s²/ε² + LΔ/ε² + LΔs²/ε⁴) |

The two bounds have the same order in every regime except when s > ε and LΔ ≲ ε². There the new bound is slightly worse, and that case is trivial.

The only broadening is replacing one-sided covariance with the row-profile condition. The example above shows that this widens what TYZ's *theorem statement* certifies with dimension-free constants. However, TYZ's own proof gives the identical bound once one triangle-inequality line is substituted, and the repository already used this noise class. The selected theorem therefore adds no complexity, scope, or output advantage beyond a routine restatement of known work.

What can be claimed is a formal, explicit-constant verification of TYZ's batched-Muon upper bound under a mildly relaxed noise condition.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
