# Novelty assessment: StrongGrowthFiniteSumAcceleration

The [theorem](../../LongTails/Theorems/StrongGrowthFiniteSumAcceleration.lean) treats f = n⁻¹Σᵢfᵢ on a finite-dimensional space. Each fᵢ is convex and L-smooth, f is μ-strongly convex, global strong growth n⁻¹Σ‖∇fᵢ(x)‖² ≤ ρ‖∇f(x)‖² holds, and ‖x₀−x⋆‖ ≤ R ([setup](../../LongTails/Setups/FiniteSumStrongGrowthStronglyConvex.lean)). Under these assumptions, the last outer center of a minibatch proximal-point method ([algorithm](../../LongTails/Algorithms/StrongGrowthBatchProx.lean)) satisfies E[f(X)−f⋆] ≤ ε. The method draws r = min{n,⌈128ρ⌉} component indices per batch, uses prox weight μ, and solves each prox subproblem with Katyusha. The budget is deterministic and counts every exact component-gradient call.

**Complexity (component-gradient calls), with κ = L/μ:**

  O( (min{n,ρ} + √(min{n,ρ}·L/μ)) · log(2+L/μ) · log(2+LR²/ε) ),

valid for L, μ, ε > 0 and ρ ≥ 1. Here L is the component smoothness, μ the strong convexity of the mean, and ρ the strong-growth constant. Convexity and L-smoothness of the components, together with ∇fᵢ(x⋆) = 0, force the smallest valid ρ to be at most κ. So when ρ ≤ n the leading term is √(ρκ). Below, L_f ≤ L denotes the smoothness of the mean.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Restarted Katyusha, [Allen-Zhu, JMLR 2018, Thm 4.1](https://jmlr.org/papers/volume18/16-410/16-410.pdf), restarted using μ (prior) | O((n+√(nκ))·log(2+LR²/ε)) → O((min{n,ρ}+√(min{n,ρ}κ))·log(2+κ)·log(2+LR²/ε)) | Factor ≈ √(n/ρ)/log(2+κ) when ρ ≤ n ≤ κ, and n/(√(ρκ) log(2+κ)) when n ≥ κ. A gain needs ρ·log²(2+κ) ≪ n. For ρ ≳ n the bound is worse by log(2+κ). | None: the selected class is a subclass, since it adds global strong growth. | None: both need L and μ, and both bound the expected last-point gap. | Global strong growth forces a common minimizer of all fᵢ, which rules out generic inconsistent finite sums. Extra log(2+κ) factor. |
| SNAG under SGC, [Hermant et al., ICLR 2025, Thm 3](https://arxiv.org/abs/2410.07870v3); same order as AGNES, [Gupta–Siegel–Wojtowytsch, NeurIPS 2024](https://arxiv.org/abs/2302.05515) (prior) | O(ρ·√(L_f/μ)·log(2+LR²/ε)) → O(√(ρκ)·log(2+κ)·log(2+LR²/ε)), for ρ ≤ n | Factor √(ρL_f/L)/log(2+κ). A gain needs ρ·L_f/L ≫ log²(2+κ). With L_f ≈ L, the ρ factor becomes √ρ. | Incomparable classes. SNAG needs only an L_f-smooth mean with SGC, with no component convexity or smoothness and no finite sum. | None | Needs component convexity and component smoothness L. Worse whenever L_f ≲ L·log²(2+κ)/ρ. Per Hermant et al. Remark 8, batching does not improve SNAG's total cost for positively correlated gradients. |
| Repository: [ProximalStormStrongGrowth](../../LongTails/Theorems/ProximalStormStrongGrowth.lean) (2026-10-18, convex) with Γ² = ρ−1 and L̄ ≤ L, *restart not verified* | Heuristically O((ρ^{3/4}√κ + ρ)·log(eρ)·log(2+LR²/ε)) → O(√(ρκ)·log(2+κ)·log(2+LR²/ε)) | Factor ≈ ρ^{1/4}·log(eρ)/log(2+κ), if the restart is valid. | Incomparable classes. The repository result needs no finite sum or component convexity, only mean-squared smoothness. | That result needs no μ; it bounds an iterate selected by a seed. | The restart is unchecked: its budget needs a deterministic radius, but after a stage only the expected gap is controlled. |

**Mechanism and reduction check.** I found no substitution or batching argument that gives this bound from earlier results. Batching SNAG or AGNES still costs order ρ√κ_f. Running Katyusha on a random subsample fails because the subsample average is not strongly convex and its minimizer is not pinned down. The minibatch-prox analysis of [Chadha–Cheng–Duchi, ICML 2022, Thm 3, Lemma 4.1 and Cor. 4.1](https://arxiv.org/abs/2101.02696) either caps the step at about 1/L or gives an outer contraction of order (L/μ)²(1+ρ/m). It also assumes exact batch prox steps, whose cost it leaves unbounded.

The proof ancestry is minibatch proximal point ([Asi et al., NeurIPS 2020](https://papers.nips.cc/paper/2020/file/fa2246fa0fdf0d3e270c86767b77ba1b-Paper.pdf)) plus a Katyusha inner solver. The ingredient that appears new is the variance bound at the *fixed* population prox point: E‖w−y‖² ≤ (ρ/r)‖c−y‖². This allows a large prox step 1/μ with a batch of size about ρ, independent of κ.

**Other checks.** Plain SGD under interpolation needs order κ·log(2+LR²/ε) calls ([Ma–Bassily–Belkin, ICML 2018](https://arxiv.org/abs/1712.06559); I did not recheck the theorem number). Least-squares-only bounds such as √(κκ̃) ([Jain et al., COLT 2018](https://arxiv.org/abs/1704.08227)) use the statistical condition number κ̃, and its relation to ρ is unverified, so they are not comparable here. The √ρ claim in [Mishkin et al., arXiv 2404.02378](https://arxiv.org/abs/2404.02378v2) is invalid for stochastic AGD; v2 says so itself. [Chadha–Cheng–Duchi, Thm 5](https://arxiv.org/abs/2101.02696) gives an Ω(ρ log(1/ε))-sample lower bound for interpolating least squares. Combined with the deterministic Ω(√κ), this leaves a gap between max{ρ,√κ} and √(ρκ), so optimality is not established.

**Search coverage.** On 2026-11-03 UTC I searched arXiv, ICLR, NeurIPS, ICML and JMLR for strong growth, interpolation, accelerated SGD and minibatch prox. The result was committed on 2026-11-03.
- [Novoselov et al., arXiv 2610.38354v1](https://arxiv.org/abs/2610.38354) (28 Oct 2026) is a related preprint the companion note misses. It uses accelerated minibatch Moreau envelopes with SVRG under interpolation alone, without strong convexity, and its rates contain no ρ.
- I did not check the accepted NeurIPS 2026 paper flagged in the note.
- The note's main comparisons match what I checked.

**Conclusion**

**Yes: in a specific regime, the proved total complexity is better than the strongest checked baselines.**

The setting is finite sums with globally strong growth, convex L-smooth components and a strongly convex mean. The strongest checked baselines are restarted Katyusha and SNAG/AGNES:

| Method | Component-gradient calls (× log(2+LR²/ε)) |
|---|---|
| Restarted Katyusha | n + √(nκ) |
| SNAG / AGNES | ρ√(L_f/μ) |
| This result | (min{n,ρ} + √(min{n,ρ}κ)) · log(2+κ) |

When ρ·log²(2+κ) ≪ n and the mean's smoothness L_f is comparable to L, the leading cost becomes √(ρκ). Take n = κ = q³ and ρ = q, an instance I verified satisfies all assumptions: the cost is order q²·log q, against q^{5/2} for the best baseline. With L_f ≈ L, and counting plain SGD's order-κ bound as well, the best gain over all checked baselines is at most about κ^{1/4}/log κ, reached at ρ ≈ √κ and n ≳ κ.

The result loses an extra log κ factor, and it does worse when ρ ≳ n or when L_f ≪ L/ρ. It also needs component convexity, component smoothness and global strong growth.

The comparison establishes this gain. My search did not find an earlier √(ρκ) bound for nonquadratic finite sums, but that does not prove priority. The gain is polynomial and comes from a real new step, the fixed-point variance bound, rather than from retuning. It is still modest, regime-limited, and not shown to be optimal.

What can be claimed is a new accelerated bound of order √(ρκ), up to logarithms, for strong-growth finite sums. It improves on known methods by up to roughly κ^{1/4} when ρ is much smaller than n.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
