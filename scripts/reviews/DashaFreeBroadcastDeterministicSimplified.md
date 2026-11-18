# DashaFreeBroadcastDeterministicSimplified: novelty assessment

[`result`](../../LongTails/Theorems/DashaFreeBroadcastDeterministicSimplified.lean) is about the [setup](../../LongTails/Setups/DistributedFreeBroadcastSmoothNonconvex.lean) F = n⁻¹Σfᵢ on ℝᵈ. F is possibly nonconvex and L-smooth, the fᵢ are mean-square L̂-smooth, and workers have exact local-gradient oracles. Uploads go over a star network with dedicated links, and the server's broadcast is free. Finite-bit DASHA with cyclic-block masks and stochastic rounding ([algorithm](../../LongTails/Algorithms/DashaDistributed.lean), [deadline wrapper](../../LongTails/Algorithms/DashaDistributedDeadline.lean)) then returns a uniformly sampled iterate with 𝔼‖∇F(x_out)‖² ≤ ε² within a closed-form elapsed time. The same setup and algorithm already appear in [`DashaFreeBroadcastDeterministic`](../../LongTails/Theorems/DashaFreeBroadcastDeterministic.lean), whose budget is an exact finite minimum.

**Selected bound (elapsed time).** Parameters: λ = min(L,L̂); h_max = maxᵢhᵢ is the time for one gradient computation; ℓ and b are the upload latency and the time per bit; Δ bounds the initial gap; G bounds ‖∇fᵢ(x₀)‖; d is the dimension and n the number of workers. If min(2λΔ, G²) ≤ ε², the time is 0. Otherwise, for n ≥ 2, the Lean budget gives (constant 2²² suppressed):

T = O( (1+λΔ/ε²)(h_max+ℓ+b) + b·[2+log(1+Δ(λ+L̂/√n)/ε²)+log(1+log(nd))]·[1+Δ(λ + d·min(λ, L̂/√n))/ε²] + b·d·min{ (G/(ε√n))·√(log-terms), 1+log(1+log(d(1+λΔ/ε²))) + log(1+G²log(·)/(nε²)), 1+log(nd(1+λΔ/ε²)) } ).

The two "log-terms"/"log(·)" placeholders stand for the same bracket as the second term, times 1+log(1+log(d(1+λΔ/ε²))) in the first. For n = 1, the budget is T = O((1+λΔ/ε²)[h_max+ℓ+b + b·d(2+log(1+λΔ/ε²)+log(1+log d))]).

In plain terms: there are O(1+λΔ/ε²) rounds; each round uploads d·min(1, L̂/(λ√n)) coordinates (at least one); each coordinate costs O(log(ΔL̂/ε²) + log log(nd)) bits; and dense or sparse initialization costs d·Φ bits.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Prior: Tyurin–Richtárik, DASHA, [arXiv v2 (22 May 2022)](https://arxiv.org/abs/2202.01268v2), Thm 6.1, Cor. 6.2–6.3; [ICLR 2023](https://openreview.net/forum?id=VA1YpcNr7ul) | Rounds: O(1+Δ(L+ωL̂/√n)/ε²) with ω+1 = d/K. Coordinates: O(d + K·rounds), e.g. O(d + L̂Δd/(ε²√n)) for K ≤ d/√n. Exact reals, no time model. → O(1+λΔ/ε²) rounds with K ≍ d·min(1, L̂/(λ√n)); bits and time as above. | Rounds and coordinates: none, same order. Taking K = d·min(1, L̂/(λ√n)) in Cor. 6.2 gives the same counts, and L → λ is trivial because F is also L̂-smooth. Bits and time: not comparable, because DASHA transmits exact reals. | Real-valued messages → finite bit lists, with the quantization floor accounted for. Problem class: none, since Thm 6.1's proof needs only the mean-square condition. | None. Same uniformly sampled iterate, same squared-norm criterion; L, L̂, Δ, G, ε are all known. | Needs a G bound for packet ranges. Each coordinate costs an extra log(ΔL̂/ε²)+log log(nd) bits. Assumes free shared randomness, free broadcast, dedicated uplinks, and free arithmetic. Cyclic masks replace RandK. |
| Repository: [`DashaFreeBroadcastDeterministic`](../../LongTails/Theorems/DashaFreeBroadcastDeterministic.lean) (commit `5b8ca6be`) | Exact finite minimum over (k, r, init) of K·(h_max+ℓ+64b) + b[B_init+(K−1)B_round] → explicit closed formula that upper-bounds that minimum (`closedDeadline_suffices`) | None. The new budget is ≥ the old one. Within this repository it is only readability, not a sharper bound. | None (same setup) | None (same output) | Constant 2²². The budget is only proved to be an upper bound; I did not check whether it matches the finite minimum up to constants. |

**Reduction check.** The result is the original theorem composed with an algebraic upper bound on its finite minimum. That bound evaluates explicit block-size and precision recipes ([`DashaDistributedRecipes`](../../LongTails/Proofs/DashaDistributedRecipes.lean), [`ClosedBudget`](../../LongTails/Proofs/DashaDistributedClosedBudget.lean)). A deadline-slack argument then extends the run to the larger deadline. The convergence part is DASHA Thm 6.1 with a composed unbiased compressor (sparsification ∘ relative rounding) plus an additive lattice error. No new optimization mechanism is involved. Proof ancestry: DASHA's Lyapunov analysis supplies the round count. What this repository adds is the pathwise range bounds, modular initialization, and event-driven execution.

**Search coverage (2026-11-18).** I read DASHA v2's Assumption 5.3, Theorem 6.1, and Corollaries 6.2–6.3 in the PDF. I checked the Huang–Chen–Yin–Yuan lower bound ([NeurIPS 2022, Thm 1](https://arxiv.org/abs/2206.03665)). It requires σ > 0 and adversarially chosen compressors in U_ω, so it does not give a lower bound for this deterministic, independent-mask setting. I also checked bit-accounting MARINA work ([Panferov et al., UAI 2025](https://arxiv.org/abs/2401.05518)), which charges fixed 32-bit floats without a finite-precision error analysis. Further, I checked Shadowheart SGD ([NeurIPS 2024](https://arxiv.org/abs/2402.04785)), which is stochastic and was not re-derived for σ = 0, and Tyurin's [sparsification lower bound](https://arxiv.org/abs/2506.23836), which is stochastic and charges the downlink, unlike this setup. I did not re-read MARINA (ICML 2021) in detail. The companion note explicitly claims no novelty, and I found no discrepancy with the Lean budget.

## Conclusion

**No: this is a closed-form, looser restatement of an existing finite-bit DASHA timing theorem, whose round and communication counts are DASHA's own.**

The strongest baseline is DASHA's deterministic theorem (Tyurin–Richtárik, Thm 6.1/Cor. 6.2). On the same function class and accuracy criterion:

| | rounds per worker | per-round upload |
|---|---|---|
| DASHA, K = d·min(1, L̂/(λ√n)) | O(1 + Δ(L+λ)/ε²) | K exact reals |
| This result | O(1 + λΔ/ε²) | K·O(log(ΔL̂/ε²) + log log(nd)) bits |

The only rate change is L → λ = min(L, L̂), which holds trivially.

The repository's earlier theorem `DashaFreeBroadcastDeterministic` already proves the same guarantee with an exactly optimized, smaller budget. This file replaces that budget with a readable explicit formula that is proved to be an upper bound, with a constant of 2²². That is a presentation improvement within the repository, not new mathematics. The finite-bit timing itself has no bit-level competitor to beat, so it remains an accounting refinement of a known rate.

The claimable contribution is a readable, formally verified elapsed-time bound for finite-precision DASHA in an idealized free-broadcast star network.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
