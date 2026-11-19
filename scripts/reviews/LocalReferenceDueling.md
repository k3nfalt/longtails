# LocalReferenceDueling: strongly convex optimization from flat comparison feedback

[`result`](../../LongTails/Theorems/LocalReferenceDueling.lean) proves the following. Consider a C¹ function on the fixed Euclidean unit ball that is μ-strongly convex, L-smooth and G-Lipschitz there, and whose minimizer `u` over the ball may lie on its boundary. Each query compares two points of the ball and returns one IID sign with mean ρ(f(x)−f(y)). The link ρ is unknown, odd, C¹, nondecreasing and bounded by 1, with c|t|ᵏ ≤ ρ′(t) ≤ M for |t| ≤ r. Under these assumptions, the weighted average returned by the [reference-opponent descent algorithm](../../LongTails/Algorithms/DuelingReferenceDescent.lean) has `∫ f(out) − f(u) ≤ ε` ([setup](../../LongTails/Setups/StronglyConvexDueling.lean)).

**Complexity.** Here d is the dimension, k the flatness order and ε the expected-gap accuracy. The comparison budget is

$$N=O\!\Big(\tfrac{d^2(4/\mu)^{2k}\max\{1,8G/r\}^{4k+2}}{c^2\mu\varepsilon}+\tfrac{d^2M^2L^2(4/\mu)^{4k}\max\{1,8G/r\}^{8k}}{c^4\mu^2\varepsilon^2}\Big).$$

The bound has no logarithms and no initialization term, because the domain is the unit ball and the algorithm starts at 0. All parameters must be positive. The algorithm knows (μ, L, G, r, c, M, k, ε).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Saha–Koren–Mansour, [ICML 2025](https://proceedings.mlr.press/v267/saha25a.html), Thm 4 (arXiv [2210.02562](https://arxiv.org/abs/2210.02562) v1, Thm 6). Prior; direct competitor on the overlap. Their p, c_ρp, α, β, D correspond to k+1, c, μ, L, 2. | Õ(c₀ᵏ L^{2k+2} d^{2k+3} / (c²μ^{2k+2}ε^{2k+2})) w.p. 1−δ, with log(1/δ) factors. Converting with δ = ε/(4G) adds log(G/ε). → N above. | ε^{−(2k+2)} → ε^{−2} and d^{2k+3} → d². The ratio (theirs / second term of N) ≍ (c/M)² d^{2k+1} (μL/(4C⁴ε))^{2k}, with C = max{1,8G/r}, up to logs and their hidden constants. For k ≥ 1 the gain needs ε ≲ μL/C⁴ (scaled by d and c/M). For k = 0 it needs d ≳ (M/c)². Example, k=1 with other parameters fixed: Õ(d⁵/ε⁴) → O(d²/ε²). | Their minimizer is the unconstrained global minimizer, which must lie in D, and they query outside D. Here the minimizer is the one over the ball (possibly on its boundary), and all queries stay in the ball. | High-probability last epoch point → expected gap of a weighted average. The expected bound follows from theirs with only a log loss; the converse does not hold. | Fixed unit ball versus a general bounded domain. Needs the upper slope M, an odd C¹ link, and the G/r window. Worse dependence on 1/μ (μ^{−(4k+2)} vs μ^{−(2k+2)}) and an extra max{1,8G/r}^{8k} factor. Constants grow exponentially in k. |
| Kumagai, [NeurIPS 2017](https://papers.nips.cc/paper/6747-regret-analysis-for-continuous-dueling-bandit), Thm 13. Prior. Covers only the k = 0 special case, with links whose derivative lies in [l₀, L₀] on the whole range [−2G, 2G]. | On the ball the barrier parameter is ν = 1. Then E f(ā_T) − f* ≤ (1/l₀)(2d√((log T + C)/T) + O(GL₀/T)) gives Õ(d²(1 + (B₂G + GML)/(cμ)) log(1/ε) / (c²ε²)) when r ≥ 2G. Here B₂ bounds ρ″. → N at k = 0. | Removes the log(1/ε) factor. N/Kumagai ≲ 1/(G log(1/ε)), so N is smaller when G log(1/ε) ≫ 1. When G ≪ 1, N can be larger by up to ML/(cμ). Saturating links give an exponential gain. For ρ = tanh, r = 1 and large G, Kumagai's l₀ ≈ 2e^{−4G}, while N is polynomial in G. | Link C³ with derivative bounded below on the whole range of f, nonincreasing on [0, 2G] → C¹ with a local window \|t\| ≤ r. Also f ∈ C² → C¹ on the ball. | None. Both give the expected gap of an averaged point. | Kumagai's method has an online-regret guarantee and works on any compact convex set with a barrier. |
| Jamieson–Nowak–Recht, [NeurIPS 2012](https://arxiv.org/abs/1209.2434), Thm 2. Prior. Applies only to unconstrained f on ℝⁿ, with a margin oracle, κ = k+2. | Õ(d^{2k+3} ε^{−2(k+1)}) with unstated poly-log constants. → N. | Not comparable as stated. The domains differ, and their constants are not explicit. In d and ε the rate equals Saha's. | Not comparable. Their oracle class is broader (a margin lower bound, no fixed link), but their domain is ℝⁿ. | None. | Their Thm 1 lower bound Ω(d ε^{−2(k+1)}) uses an ε-radius query cube (Lemma 1), so it does not bind on a fixed ball. |

**Reductions and mechanism.** At k = 0, the result is essentially one-point sphere smoothing plus weighted SGD. That is the ancestry of Flaxman–Kalai–McMahan, Hazan–Levy and Kumagai, and the d²/ε² order was already known up to a log. At k = 0 it is also tight: Kumagai's Thm 14, via Shamir's Thm 7, gives Ω(d²/ε²) on the unit ball. For k ≥ 1, no standard reduction reproduces the bound. Symmetric pairs w ± γu, as in Saha et al., give value gaps O(Gγ), so the slope is about (Gγ)ᵏ and the rate becomes ε^{−2p}. The new step compares the perturbed iterate with one of three opponents at fixed spacing s, frozen at x. Midpoint strong convexity then forces a value gap of at least μs²/4 for some opponent, which keeps ρ′ ≥ c(μs²/4)ᵏ independent of ε, and the mean of the estimator stays a positive multiple of ∇f(x) plus an O(MLh) bias. I found no prior use of this mechanism.

**Search coverage.** I searched on 2026-11-18 UTC. The result entered the repository in commit b1eee6b6 on 2026-11-18 21:21 UTC. I read Saha et al. (ICML camera-ready and arXiv v1), Kumagai, and Jamieson et al. I partly read the following later or concurrent work:
- [Lu et al. 2026](https://arxiv.org/abs/2608.15050) requires ρ′(0) = −γ ≠ 0, with γ known, and explicitly excludes flat links. Its d-dependence was not verified.
- [Kovalev et al. 2026](https://arxiv.org/abs/2611.19611) covers nonsmooth objectives with positive link slope.
- [Scheinberg–Xiong 2026](https://arxiv.org/abs/2604.26867) uses noiseless comparisons.

I did not check Xu et al. (UAI 2020, Borda) myself. Jamieson's Thm 2 constants were garbled in extraction. The companion note does not cite Kumagai. Its statement that the p = 1 case "improves the dimension dependence" is true only against Saha et al.: Kumagai already gives d² log(1/ε)/ε² for k = 0, under stronger link assumptions.

**Conclusion**

**Yes: for flat links (k ≥ 1), the proved comparison complexity is polynomially better than the best prior guarantee, which is Saha–Koren–Mansour (ICML 2025, Thm 4).**

On their common setup (unit ball, interior unconstrained minimizer), with other parameters fixed:

| | Saha et al. 2025 | This result |
|---|---|---|
| flat order k ≥ 1 | Õ(d^{2k+3} ε^{−2k−2}) | O(d² ε^{−2}) |
| k = 0 | Õ(d³ε^{−2}); Kumagai: Õ(d² log(1/ε)ε^{−2}) | O(d² ε^{−2}) |

The gain needs ε small relative to μL·r⁴/G⁴, scaled by d and c/M. The new bound has worse exponents in 1/μ and G/r, constants exponential in k, and only an expected-gap guarantee rather than a high-probability one. It also covers boundary minimizers with in-ball queries, which Saha et al. exclude, but it holds only on the fixed unit ball.

The gain comes from comparing against fixed-distance reference points, which prevents near-ties. Jamieson et al.'s ε^{−2p} lower bound, which Saha et al. cite as optimality, relies on a query domain that shrinks with ε, so it does not bind here. At k = 0 the result essentially matches Kumagai: it removes a log and weakens the link assumptions, but the rate is not new.

The comparison establishes the improvement. Priority rests on a search that found no earlier fixed-reference argument, and that search is not exhaustive. The claim that can be made: the first d²/ε² comparison bound for smooth strongly convex optimization on a ball under flat links (k ≥ 1), as far as this search found.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
