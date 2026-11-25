# HeavyTailedNcscLowerBound: randomized lower bound for heavy-tailed NC–SC minimax

[`result`](../../LongTails/Theorems/HeavyTailedNcscLowerBound.lean) proves `NonConvergence` on the [setup](../../LongTails/Setups/HighDimensionalHeavyTailedNcsc.lean), which restricts the [base setup](../../LongTails/Setups/HeavyTailedNcsc.lean) to ℝᵈ×ℝᵈ with x₀=y₀=0. For every valid parameter choice, every adaptive randomized algorithm, and every budget up to the one stated, some admissible instance gives P(‖∇Φ(X)‖>ε) > 1/4 ≥ δ. The instance may depend on the algorithm and the budget, but not on the seed. No algorithm is involved; the [hard instances](../../LongTails/Proofs/HeavyTailNcscLowerAssembly.lean) are in `Proofs/`.

**Proved necessary budget.** Here f is jointly L-smooth and μ-strongly concave in y, Φ(x₀)−inf Φ ≤ Δ, and ‖∇_y f(x₀,y₀)‖ ≤ G. The IID joint oracle is unbiased with central p-th moment ≤ σᵖ for p∈(1,2]. The target accuracy is ε, and the theorem shows that more than

N = c_p [ (LΔ/ε²)·(1 + (Lσ²/(με²))^{p/(2(p−1))}) + (Lσ/(με))^{p/(p−1)} ],  with c_p = 2^{−61−14p/(p−1)},

calls are needed. The parameter range requires δ≤1/4, L≥8μ, LΔ≥2³²ε², G√(L/μ)≥4176ε and d ≥ 2⁴⁰(1+(LΔ/ε²)(1+(√(L/μ)σ/ε)^{p/(p−1)}))⁴. Because the bound is at fixed confidence, it has no log(1/δ) term. It also has no √κ deterministic term and no G-dependence.

Write κ=L/μ, A=LΔ/ε², u=σ/ε and r=p/(p−1)≥2.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhu–Xu–Ji, [arXiv:2609.06064](https://arxiv.org/abs/2609.06064) v1 (5 Sep 2026), Thm 3.4. Prior. Zero-respecting algorithms; constrained hard domain; criterion is expected projected-gradient mapping. | Ω(κ^{1/3} A u^r) → Ω(A(√κu)^r + (κu)^r) | Larger by a factor of at least κ^{r/2−1/3} ≥ κ^{2/3} whenever √κu ≥ 1. Adds the (κu)^r term. | Zero-respecting algorithms → all randomized algorithms; unconstrained ℝᵈ. | Expected criterion → probability criterion. Markov gives E‖∇Φ‖>ε/4, but that conversion is not formalized. | Needs very large d and L≥8μ; constants are exponentially small in r. |
| Wu et al., [arXiv:2610.00229](https://arxiv.org/abs/2610.00229) v2 (19 Oct 2026), Thm 3.4. Prior. Randomized algorithms, variance-σ² instances. These also satisfy every p-th moment bound by Jensen's inequality, so the bound transfers to every p. | Ω(√κA + κAu² + κ²u² + √κ log₊(G/(ε√κ))) → Ω(A + A(√κu)^r + (κu)^r) | For p<2: larger by (√κu)^{r−2} on the chain term when √κu>1, and by (κu)^{r−2} on the dual term when κu>1. At p=2 the noise terms are the same order. | Bounded-variance hard instances → p-th-moment hard instances; the class is unchanged. | None | Loses √κA and the G-term. Worse when the √κA term dominates, for example at σ=0, where the bound is Ω(A) versus Ω(√κA). |
| Single-level heavy-tailed bound (Liu–Zhou, ICLR 2025, [arXiv:2412.19529](https://arxiv.org/abs/2412.19529) Thm 3.3; zero-respecting), embedded as F(x)−(μ/2)‖y‖² | Ω(A u^r) → Ω(A(√κu)^r + (κu)^r) | Larger by κ^{r/2} | Zero-respecting → randomized | None | Same as the first row |

**Gap to the upper bound.** The repository [upper bound](../../LongTails/Theorems/HighDimensionalHeavyTailedNcscUpperBound.lean) has the same specification and is O((2⁸⁰r)^{r+2}Λ^{2r+3}[√κ(1+A+Q)+(Aκ^{r/2}+κ^r)u^r]). It matches the lower bound up to r-dependent constants and polylogarithms when σ≥ε and the lower bound's range applies. This regime is nonempty. The constant ratio is about 2^{O(r log r)}, so the match is not uniform as p→1.

**Standard-reduction check.** The chain term is essentially a substitution. Lift a base chain H through [arXiv:2609.35206](https://arxiv.org/abs/2609.35206) Prop. 3.1 (28 Sep 2026); there the y-noise scales by q≍κ^{−1/2}, α≍ℓ/L and the gradient transfer factor is 1. Then the base bound ℓΔ_H ε⁻²(σ_H/ε)^r, with σ_H=σ/q and ℓΔ_H≍LΔ, becomes A(√κu)^r.

- **Zero-respecting algorithms.** Composing Prop. 3.1 with Liu–Zhou Thm 3.3 or Fradin et al. ([arXiv:2512.18713](https://arxiv.org/abs/2512.18713)) already gives this term.
- **Randomized algorithms.** The randomized extension uses the Arjevani et al. (Math. Program. 2023) hiding technique with a Bernoulli reveal probability of order (ε/(√κσ))^r. The repository's earlier lower bounds supply this step; I found no published heavy-tailed randomized single-level bound.
- **Dual term.** The (κu)^r term adapts Wu et al.'s two-point test (Thm D.1, Gaussian noise) by using Bernoulli spikes, the device of Fradin et al. Lemma C.1. It uses a Huber dual term, and its mechanism is not new.

**Search coverage (24 Nov 2026).** I read the cited theorem statements in 2609.06064, 2610.00229, 2609.35206, 2512.18713 and 2412.19529, and checked [arXiv:2609.30877](https://arxiv.org/abs/2609.30877) (p=2, zero-respecting). Further arXiv/web searches found no heavy-tailed NC–SC lower bound with exponent κ^{r/2}. I did not verify the proofs of the cited papers, and Arjevani et al. was checked from memory.

The commit is dated 24 Nov 2026, and all compared works predate it. The companion note is consistent with the Lean statement. It does omit the reduction from Wu et al. by moment monotonicity, which gives the p<2 baseline Ω(κAu²+κ²u²) instead of κ^{1/3}.

## Conclusion

**Yes, the lower bound is genuinely larger, but it comes from assembling known pieces.** For 1<p<2 and σ≥ε/√κ, the strongest prior bound comes from Wu et al.'s randomized bounded-variance construction, transferred to every p because a variance bound implies a p-th moment bound.

| | Necessary calls |
|---|---|
| Wu et al. (transferred) | √κA + κAu² + κ²u² |
| This result | A(√κu)^r + (κu)^r, with r=p/(p−1)>2 |

In that regime the bound grows by (√κu)^{r−2}. The result also improves Zhu–Xu–Ji's zero-respecting κ^{1/3} bound by at least κ^{2/3}, and it makes the repository's κ^{r/2} upper bound tight up to p-dependent constants and polylogarithms when σ≥ε. It loses the deterministic √κA term and the G-dependence, and it needs huge dimension and constants of order 2^{−14r}.

The gain is real, but a published lifting plus a published heavy-tailed chain gives it by direct substitution. The randomized hiding and Bernoulli-spike two-point test are standard adaptations. The literature search found no prior statement of this bound, though that does not prove priority.

What can be claimed: the first verified bound showing the optimal κ^{p/(2(p−1))} dependence for heavy-tailed NC–SC against randomized algorithms, obtained by routinely combining known constructions.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
