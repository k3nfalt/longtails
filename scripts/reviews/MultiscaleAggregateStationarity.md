# Novelty assessment: MultiscaleAggregateStationarity

The [theorem](../../LongTails/Theorems/MultiscaleAggregateStationarity.lean) proves an elapsed-time bound on a dedicated star network ([setup](../../LongTails/Setups/DistributedAggregateSmoothNonconvex.lean), [algorithm](../../LongTails/Algorithms/MultiscaleAggregateProtocol.lean)). Every message is a finite bit list. The root outputs a uniformly random pre-update iterate `X` with `E‖∇F(X)‖ ≤ ε`, where `F = (1/n)Σ fᵢ`. Only `F` needs to be `L`-smooth with gap `Δ`. Each worker gets unbiased samples of `∇fᵢ` with variance `σᵢ²`, the samples are independent, and there is no bound on worker disagreement, gradient magnitude, or component smoothness.

**Proved bound.** Here `hᵢ` is the time per sample at worker `i`, `ℓ` the per-message latency and `b` the time per bit. The Lean budget is `2(1+⌈2¹⁹LΔ/ε²⌉)·[maxᵢhᵢ + 2¹⁸Σᵢhᵢσᵢ²/(n²ε²) + 2(ℓ + b(64 + d(5+bits(n(d+1)))))]`, which gives

  T = O( (1 + LΔ/ε²) · [ maxᵢ hᵢ + Σᵢ hᵢσᵢ²/(n²ε²) + ℓ + b(1 + d·log(2+nd)) ] ).

This holds for all `d ≥ 0` and `σᵢ ≥ 0`. It pays for one round even when `2LΔ ≤ ε²`. The measured cost is elapsed time, not a count of oracle calls.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tyurin–Richtárik, Amelie SGD ([NeurIPS 2024, arXiv 2405.16218v2, Table 2](https://arxiv.org/html/2405.16218v2)). Same heterogeneous class with common `σ`, but messages are **real vectors** | `(LΔ/ε²)·max{τ, maxhᵢ, σ²Σhᵢ/(n²ε²)}`, with `τ` the time to send one real vector → `T` above | Not comparable in bit units: a real vector has no finite bit length. If each real coordinate costs 64 bits (`τ = ℓ+64bd`), the order is the same | Real-valued messages → finite bit packets of `O(d log(nd))` bits, with no bound on disagreement or gradient range | None (random-iterate output in both) | Their criterion `E‖∇F‖² ≤ ε²` is stronger. They allow random, time-varying speeds and general topologies; here service times are deterministic on a dedicated star |
| Tyurin, Leon SGD ([arXiv 2603.20735v1, Mar 2026, Thm 1.7](https://arxiv.org/html/2603.20735v1)). Heterogeneous, bandwidth-limited graphs | `(LΔ/ε²)·max{d/w̄₁, maxhᵢ, σ²Σhᵢ/(n²ε²)}`, where `w̄₁` is the min cut in coordinates per second → `T` | Not comparable: the unit is a real coordinate, not a bit | Coordinate units → bits | None | Leon covers general graphs, and its matching lower bound (Thm 5.2) is in coordinate units |
| Repository [DistributedBatchedSgd](../../LongTails/Theorems/DistributedBatchedSgd.lean). Special case: **homogeneous** (`fᵢ = f`, common `σ`), squared-norm criterion | With its tolerance set to `ε²`: `(1+LΔ/ε²)[minₘ(hₘ + σ²/(ε²Σⱼ≤ₘhⱼ⁻¹)) + ℓ + b(64 + d log(2+d+LΔ/ε²+σ²/ε²))]` → `T` | Bit term: `d log(d+LΔ/ε²+σ²/ε²)` → `d log(nd)`. This is a gain when `n ≪ (LΔ+σ²)/ε²`. **Worse** compute term: `maxhᵢ + σ²·avg(h)/(nε²)` against Rennala-style use of only the fastest workers (unbounded loss if one worker is very slow) | Homogeneous → heterogeneous, with only `F` smooth | None | The baseline also certifies the stronger squared-norm criterion |

**Reduction check.** Summing residues modulo a common period is standard ([Bonawitz et al.](https://eprint.iacr.org/2017/281.pdf); [arXiv 1912.00131](https://arxiv.org/pdf/1912.00131)). Combining it with a known range for the sum yields a direct baseline.
- Smoothness gives `‖∇F(x₀)‖ ≤ √(2LΔ)`, and normalized steps of length `α/L` keep `‖∇F(xₖ)‖ ≤ √(2LΔ)+Kα`.
- One modulus covering this whole range therefore costs `O(d log(ndLΔ/ε²))` bits per round.
- A wrong lift from heavy noise costs only `O(α²/R)` in expectation, by Chebyshev.

So heterogeneity and the finite-bit requirement do not need the new decoder. They follow from known tools. The new mechanism is decoding against a dyadic anchor `k−2^{v₂(k)}` with radius `2^{v₂(k)}α`, together with the error-charging argument. It removes the extra `log(LΔ/ε²)` factor without assuming bounded noise.

**Proof ancestry.**
- [Davies et al.](https://arxiv.org/abs/2002.09268) (ICLR 2021) prove `O(d log n)`-bit variance reduction with high probability (Theorem 3). It needs known `σ`, and decoding is relative to another machine's input. That only works when all inputs estimate a common mean, which is the homogeneous case.
- Wyner–Ziv SGD ([arXiv 2011.12160v2, Thms 5.4–5.5](https://arxiv.org/abs/2011.12160v2)) is convex and homogeneous, and needs gradients bounded almost surely.
- Moniqua (ICML 2020) assumes bounded disagreement and bounded gradients.

None of these is an end-to-end competitor on this class.

**Search coverage.** I searched on 2026-11-18: arXiv, PMLR/ICML, ICLR, NeurIPS and IACR sources on time complexity, lattice and modulo distributed mean estimation, Wyner–Ziv compression, and secure aggregation. The result was introduced in commit `681b3197` (2026-11-19 +03:00). I did not read the ISIT 2022 Wyner–Ziv paper or the theorems in Appendix C of 2405.16218 verbatim. The companion note matches the Lean statement. Its framing of Tyurin–Richtárik as a "benchmark" is fair, but the note presents single-modulus coding only as a comparison it does not prove. It does not say that this baseline already covers the full heterogeneous scope at an extra logarithmic cost.

## Conclusion

**The rate is not new; the gain is a logarithmic saving in packet size, on top of a scope extension that standard tools already reach.**

The strongest direct baselines are Amelie and Leon SGD. Both give the same computation and round structure, `(LΔ/ε²)·[maxhᵢ + Σhᵢσᵢ²/(n²ε²) + comm]`, which Tyurin's lower bound shows is optimal in coordinate units. But they send real vectors. Moving to finite bits under unbounded heterogeneity does not need the new method: modulo summation with the smoothness-derived range already gives

  comm per round: b·d·log(ndLΔ/ε²) (standard reduction) → b·d·log(nd) (this result).

The gain survives in the total bound only when the bit term dominates computation, i.e. roughly `b·d·log(nd) ≳ maxhᵢ + Σhᵢσᵢ²/(n²ε²)`, and `LΔ/ε² ≫ nd`. The saving is then a factor of order `log(LΔ/ε²)/log(nd)`. With positive noise and fixed hardware, computation dominates as `ε → 0`, and the gain disappears.

What is established is a correct finite-bit, deterministic-deadline guarantee, and a dyadic-anchor decoding technique that I did not find in prior work. What is not established is any polynomial improvement, or a bit lower bound showing that `d log(nd)` matters. The claimable contribution is a `log(LΔ/ε²)`-factor reduction in the communication term relative to straightforward modulo coding, in communication-dominated regimes.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
