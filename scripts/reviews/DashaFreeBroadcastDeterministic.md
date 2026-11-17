# DashaFreeBroadcastDeterministic: novelty assessment

[`result`](../../LongTails/Theorems/DashaFreeBroadcastDeterministic.lean) shows the following for the [setup](../../LongTails/Setups/DistributedFreeBroadcastSmoothNonconvex.lean). The objective is F = n⁻¹Σfᵢ on ℝᵈ, smooth (constant L), mean-square smooth (constant L̂), and possibly nonconvex. Workers have exact local-gradient oracles; uploads go over a star network and the server's broadcast is free. Under these assumptions, finite-bit DASHA ([algorithm](../../LongTails/Algorithms/DashaDistributed.lean), [selection](../../LongTails/Algorithms/DashaDistributedSelection.lean)) returns a point x_out, drawn uniformly from its iterates, with 𝔼‖∇F(x_out)‖² ≤ ε² within the elapsed time `budget p`.

**Selected bound.** Write λ = min(L,L̂) and h_max = maxᵢhᵢ (computation time); ℓ is the upload latency, b the time per bit, Δ the initial gap, and G a bound on ‖∇fᵢ(x₀)‖. If min(2λΔ, G²) ≤ ε², the time is 0. Otherwise, I bounded the finite minimum by its candidates with precision r = 2, signed dense initialization and k kept coordinates:

T = O( min_{1≤k≤d} K_k·[h_max + ℓ + b + b·k·(1 + log K_k + log log(2 + d + √n L̂/λ + Gd/(ε√n)))] + b·d·log(2 + Gd/(ε√n)) ), where K_k = 1 + Δ(λ + L̂d/(k√n))/ε².

Here K_k is the number of gradient calls per worker. The 64-bit padding per message is absorbed into the b term. Choosing k ≍ d/√n gives K = O(1 + Δ(λ+L̂)/ε²), with O(d/√n) coordinates per round.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Prior: Tyurin–Richtárik, DASHA, [arXiv v2 (22 May 2022)](https://arxiv.org/abs/2202.01268v2), Thm 6.1 (appendix form with arbitrary gᵢ⁰), Cor. 6.2–6.3; [ICLR 2023](https://openreview.net/forum?id=VA1YpcNr7ul) | Rounds: O(1 + Δ(L + ωL̂/√n)/ε²), in our ε² convention, with ω = d/k − 1. Real coordinates sent: O(d + k·rounds). With RandK at k ≤ d/√n: O(d + L̂Δd/(ε²√n)). DASHA gives no finite-bit or elapsed-time bound. → Same rounds, with L replaced by λ. Each coordinate costs O(1 + log K + log log(·)) bits, plus initialization bits b·d·log(2 + Gd/(ε√n)). | Rounds and gradient calls: none, same order. Replacing L by λ is trivial, because F is also L̂-smooth. Bits and time: not comparable, because DASHA sends exact reals. | Real-valued messages → finite bit lists, with additive quantization error controlled. Problem class: none. DASHA's proof averages Lemma H.8(3), so it only needs the same mean-square condition. | None. The output is the same uniformly sampled iterate, under the same squared-norm criterion, and all of L, L̂, Δ, G, ε are known. | Requires a G bound for packet ranges, which DASHA does not need. Shared randomness for the masks is assumed free. Cyclic-block masks replace uniform RandK. Free broadcast, dedicated uplinks, and no cost for arithmetic or coding. The extra log K bits per coordinate come from worst-case pathwise range growth. |

**Reduction check.** The convergence part is DASHA's Theorem 6.1 with its compressed-initialization terms, applied to a composed compressor. RandK-type masking (ω = q − 1) is composed with r-bit relative stochastic rounding using the standard rule (ω₁+1)(ω₂+1) − 1, which gives ω = (1+2/4ʳ)q − 1. A lattice-rounding error floor is then added, and the lattice spacing ρ ∝ ε√(n/(dq)) absorbs it. So the rate follows by a standard reduction. The new ingredients are engineering-level: deterministic exponent-width capacity bounds B₀Cᵗ, modular summation for dense initialization, and a proved event-driven execution.

**Search coverage (2026-11-17).** I read the actual theorem statements and proofs of DASHA v2. I also searched for distributed compression time-complexity work, including [Shadowheart SGD (NeurIPS 2024)](https://arxiv.org/abs/2402.04785), which is stochastic with a per-coordinate time model and is not re-derived here for σ = 0. I searched for finite-bit or quantized nonconvex communication bounds and found no finite-bit DASHA analysis. I did not re-read MARINA's theorems (Gorbunov et al., ICML 2021), whose round count is reportedly the same order, or the compressed-communication lower bounds. The result was introduced in commit `5b8ca6be`; DASHA predates it by years. The companion note itself states that no mathematical novelty is claimed. I agree with it, and I found no discrepancy with the Lean budget.

## Conclusion

**No: this is a finite-bit, timed re-analysis of DASHA, and its rate is the same as DASHA's.**

The strongest baseline is DASHA's own deterministic theorem (Tyurin–Richtárik, Thm 6.1 / Cor. 6.3). On the identical function class and accuracy criterion, the two rates are:

| | rounds = gradient calls per worker | per-round upload |
|---|---|---|
| DASHA | O(1 + Δ(L + L̂d/(k√n))/ε²) | k exact reals |
| This result | O(1 + Δ(λ + L̂d/(k√n))/ε²) | O(k·(1 + log K + log log(·))) bits |

The only rate change is L → λ = min(L,L̂), which holds trivially.

What is new is accounting: an explicit bit count, a quantization floor sized to ε, and a proved elapsed-time bound in an idealized star network with free broadcast. There is no bit-level baseline to compare against, so the time comparison is unresolved rather than a gain. The convergence proof follows from DASHA's theorem with a composed unbiased compressor plus an additive error term. The extra pieces — exponent-width range bounds and modular initialization — are reasonable implementation details, but they are not independent optimization results. I did not check MARINA or the lower-bound literature in detail; that would not change this verdict, since the result does not beat DASHA itself.

The claimable contribution is a rigorous finite-precision, elapsed-time formalization of known DASHA guarantees.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
