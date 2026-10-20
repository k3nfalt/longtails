# Novelty assessment: HeterogeneousAdamFirstMoment

The [theorem](../../LongTails/Theorems/HeterogeneousAdamFirstMoment.lean) proves the following for the [setup](../../LongTails/Setups/HeterogeneousSymmetricFirstMoment.lean) and [algorithm](../../LongTails/Algorithms/HeterogeneousAdam.lean). The objective is L-smooth and nonconvex on ℝ^{b+h}. The stochastic gradient is unbiased and drawn IID; noise on the "body" coordinates is coordinatewise symmetric with finite first moment, and the body noise has an integrable samplewise Lipschitz modulus. Under these conditions, bias-corrected Adam (β₁=0.9, β₂=0.999, given δ) on the body, coupled with coordinatewise AdaGrad on the "head", outputs a uniformly random iterate x_J with 𝔼‖∇f(x_J)‖ ≤ ε.

**Proved budget.** Each iteration makes one single-sample gradient call. With d=b+h,

T = O( Q · log⁴(e(1+σ_b)Q) ),

Q = 1 + (1+d²(L+M)²Δ/L)(bδ+σ_b+√h σ_h)²/ε⁴ + [1+d²(L+M)²Δ/L + h(1+2LΔ+hσ_h²)·√(1+d²(L+M)²Δ/L)]/ε².

The parameters are:
- L: gradient Lipschitz constant;
- Δ ≥ f(x₀) − inf f: initial objective gap;
- σ_b: bound on the ℓ₁ sum of the body coordinates' mean absolute noise;
- σ_h²: head noise variance;
- M: bound on 𝔼K, the mean of the samplewise modulus;
- δ: Adam's stabilizer.

For fixed δ>0 an ε⁻⁴ term remains even without noise.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Standard reduction (full target setup): coordinatewise median of 3 samples on the body, then randomized SGD ([Ghadimi–Lan, SIOPT 2013, Cor. 2.2](https://arxiv.org/abs/1309.5549)) | 3·O(1 + LΔ/ε² + LΔ(σ_b²+σ_h²)/ε⁴) → T above | **Worse.** For all valid parameters, T ≥ the previous bound up to constants: the ratio is ≥ d²(1+M/L)²·log⁴ for the noise terms, with an added b²δ²-term. | None. The baseline does not need the samplewise modulus K. | None. Both outputs are uniformly random iterates under the same criterion 𝔼‖∇f‖ ≤ ε. Neither is adaptive: Adam's step uses L, Δ, d, T. | Requires K; adds a factor of d²; adds a δ-driven ε⁻⁴ term in the noiseless case; 10⁸⁴ and log⁴ overheads. |
| Repository [MedianFirstMomentNonconvex](../../LongTails/Theorems/MedianFirstMomentNonconvex.lean). Restricted to h=0 or a symmetric head; uses a paired-query oracle. | O(log²(LΔ/ε²)·(1 + (LΔ+σ²)/ε² + ΛσΔ/ε³)) paired queries, with σ ≥ the ℓ₂ first moment and Λ ≤ √b·M → T above | Worse by ε⁻¹ on the overlap (leading ε⁻³ vs ε⁻⁴); the stronger oracle makes this not a same-oracle comparison | None. The repository result only needs averaged (not samplewise) Lipschitz noise. | None | The selected result uses a single-point oracle and allows a non-symmetric head |
| [Dereich–Do–Jentzen–von Wurstemberger, arXiv 2511.06675 v2 (Jun 2026), Thm 1.2 and §4](https://arxiv.org/abs/2511.06675v2) (special-case baseline for the Adam method) | Lᵖ parameter error O(M⁻¹ + √γ) under strong convexity, bounded data, and bounded iterates → T above | Not comparable: different criterion and class | Adam-specific scope only: strongly convex, bounded data and iterates → L-smooth nonconvex, unbounded first-moment symmetric noise. The classes are incomparable, since here symmetry and K are required. | Expected stationarity of a random iterate replaces parameter error | Requires exact coordinate symmetry and the samplewise modulus K |

**Reduction check and proof ancestry.** A three-sample median of IID symmetric scalars is symmetric, so it is unbiased. It has second moment ≤ 6(𝔼|ζ_j|)², because P(|med|>t) ≤ 3P(|ζ|>t)² and P(|ζ|>t) ≤ 𝔼|ζ|/t. The body therefore gets an unbiased estimator with variance ≤ 6σ_b² + σ_h², and the problem class follows from Ghadimi–Lan in a few lines, without K. The genuinely new technical step concerns only the Adam history. It controls the adaptive history against a frozen symmetric reference, with first-moment factorization of K and no inverse powers of δ. Proof ancestry:
- Dereich et al. supply the symmetric-field idea.
- [Wang et al., COLT 2023](https://arxiv.org/abs/2305.18471) supply the AdaGrad potential.

Neither gives this bound.

**Search coverage.** Searched 2026-10-19 UTC: arXiv, plus the 2025–2026 ICML, ICLR, NeurIPS and UAI proceedings, on Adam/RMSprop under heavy-tailed or symmetric noise and on sign-based and nonlinear SGD. Related work found:
- [Pang, UAI 2026, arXiv 2607.27383](https://arxiv.org/abs/2607.27383) requires p>1 moments and couples β₁ to β₂.
- [Liu, arXiv 2606.22326](https://arxiv.org/abs/2606.22326) requires p>4/3 and β₁=β₂.
- [Yu et al., arXiv 2602.07425](https://arxiv.org/abs/2602.07425) covers sign methods with p>1.
- [Armacki et al., arXiv 2507.09093 v2](https://arxiv.org/abs/2507.09093) covers nonlinear SGD and needs a symmetric density, which excludes atoms.

None of these gives a fixed-β₂ Adam guarantee in this regime. I read only abstracts or partial HTML for Pang, Liu and §4 of Dereich et al., so the comparison relies on their stated hypotheses. The [companion note](../../LongTails/Theorems/HeterogeneousAdamFirstMoment.md) correctly disclaims a problem-class improvement. However, it describes only "two-sample normalized methods" and the stronger-oracle median result as competitors. It misses that the single-oracle median+SGD reduction already beats this bound uniformly. The result was introduced in commit 34b1a88 (2026-10-19 21:02 UTC).

## Conclusion

**No: it neither improves complexity nor covers new instances of the problem class. What it adds is another analysis, for a specific Adam/AdaGrad optimizer.** The strongest baseline is elementary. Take the coordinatewise median of three samples on the body, then run Ghadimi–Lan randomized SGD. This needs fewer assumptions (no samplewise modulus K) and uses the same single-point oracle and output criterion.

| Method | Gradient calls for 𝔼‖∇f(x_J)‖ ≤ ε |
|---|---|
| Median-of-3 + SGD | O(1 + LΔ/ε² + LΔ(σ_b²+σ_h²)/ε⁴) |
| This result | ≥ d²(1+M/L)²·LΔ(σ_b²+σ_h²+b²δ²)/ε⁴ · log⁴(…) + d²LΔ/ε² |

The selected bound is never better in any parameter regime. It loses at least a factor of d² and requires the extra modulus K. With fixed δ it also keeps an ε⁻⁴ term when there is no noise at all.

What may be new is method-specific: vanishing expected stationarity for bias-corrected Adam with fixed β₂=0.999 under nonconvex smoothness and symmetric first-moment noise, including atoms. The checked Adam literature only covers either strong convexity with bounded data or noise with p>1 moments and coupled or horizon-dependent β's. The search does not establish priority, and the result is not "almost as fast" as applicable methods. The claim that can actually be made is a first-moment, fixed-memory convergence proof for Adam (with an AdaGrad head), not an optimization advantage.

**Verdict: NO IMPROVEMENT**

**Confidence: medium**
