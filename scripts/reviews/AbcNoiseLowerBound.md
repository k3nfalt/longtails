# AbcNoiseLowerBound: what is actually new?

[`result`](../../LongTails/Theorems/AbcNoiseLowerBound.lean) proves the following in the [high-dimensional setup](../../LongTails/Setups/HighDimensionalAbcNoiseNonconvex.lean), which restricts the [general ABC setup](../../LongTails/Setups/AbcNoiseNonconvex.lean). For every valid parameter tuple, every randomized adaptive algorithm (with no span or zero-respecting restriction) and every call count `N ≤ budget`, including `N = 0`, there is an instance and oracle on which `E‖∇f(x̂)‖ > ε`. The instance is an `L`-smooth `f` on `ℝ^d` with `f(x₀) − inf f ≤ Δ`. Its unbiased, jointly measurable IID oracle satisfies `E‖g − ∇f‖² ≤ 2A(f − inf f) + B‖∇f‖² + C`. The instance depends on the algorithm but not on its seed. The hard instance and oracle are built in `LongTails/Proofs/Abc*.lean`; no algorithm module is involved.

**Proved necessary budget.** Here `L` is the smoothness constant, `Δ` the initial gap to the infimum, `ε` the target expected gradient norm, and `A, B, C ≥ 0` the ABC constants. In the regime `2²⁶ε² ≤ LΔ` and `d ≥ 2⁴⁰(1 + LΔ(1+B+AΔ/ε²+C/ε²)/ε²)⁴`, every algorithm needs

  N > ⌊LΔ(1 + B + AΔ/ε² + C/ε²)/(2⁵³ε²)⌋ = Ω(LΔ/ε² + B·LΔ/ε² + LAΔ²/ε⁴ + LΔC/ε⁴)

calls. The bound is vacuous until the bracket exceeds `2⁵³`. The [matching SGD upper bound](../../LongTails/Theorems/AbcNoiseSgdUpperBound.lean) is `⌈144·LΔ(1+B+AΔ/ε²+C/ε²)/ε²⌉+1` (Khaled–Richtárik, Cor. 1). The two bounds differ only by the universal factor `144·2⁵³`, with no logarithmic factors.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Arjevani et al., Math. Program. 2023 ([arXiv 1912.02365](https://arxiv.org/abs/1912.02365), randomized-algorithm bound, Thm. 3 as cited by the note), combined with Carmon et al. (Math. Program. 2020, deterministic `Ω(LΔ/ε²)`); also Jin ([arXiv 2608.09004](https://arxiv.org/abs/2608.09004) v1, Aug 2026, Thm. 4.1, a.s.-bounded noise). *Applies only to the special case `A = B = 0`, `C = σ²`.* | `Ω(LΔ/ε² + LΔC/ε⁴)` is the best previous lower bound on the full ABC class, by inclusion → `Ω(LΔ/ε² + BLΔ/ε² + LAΔ²/ε⁴ + LΔC/ε⁴)` | Larger necessary budget whenever `AΔ ≥ max(C, ε²)` (gain factor `AΔ/max(C, ε²)`). Example: `B = C = 0`, `AΔ ≫ ε²` gives `LΔ/ε² → LAΔ²/ε⁴`. Also when `B ≥ 1`. None on the overlap `A = B = 0`: same order, much worse constants. | Bounded variance → noise proportional to the gap `f − inf f` (and to `‖∇f‖²`). This covers instances whose variance vanishes at minimizers. | None (same output criterion: expected gradient norm of the returned point) | Dimension must be quartic in the bound. Huge constants. Expectation criterion only, not high probability. |
| Huang–Chen–Yin–Yuan ([arXiv 2206.03665](https://arxiv.org/abs/2206.03665) v2, Oct 2022, Thm. 1, unbiased ω-compression). *Covers only zero-respecting algorithms, `n ≥ 2` workers and a compression oracle; relative noise only.* | `Ω((1+ω)LΔ/ε²)`, a relative-noise term (`B ≈ ω`) → `Ω(B·LΔ/ε²)` term for arbitrary randomized algorithms | Not comparable: different oracle model and algorithm class. The B-term itself is not claimed as new. | Zero-respecting, compression model → arbitrary randomized algorithms, single IID oracle | None | None beyond row 1 |
| Trivial reduction with an arbitrary lower bound `f_low < inf f` (the repository's [`ExpectedSmoothnessNonconvex`](../../LongTails/Setups/ExpectedSmoothnessNonconvex.lean) convention): take Arjevani's instance with gap `Δ/2`, `σ² = AΔ`, `f_low = inf f − Δ/2` | `Ω(LAΔ²/ε⁴)` in that weaker model → the same order with offset `inf f` | None in rate | Offset `f_low ≤ inf f` → exact infimum. The ABC budget must then vanish near minimizers, which is the class Khaled–Richtárik actually use. | None | The reduction does not apply to the exact-infimum class |

**Reduction check.** I tried to derive the A-term from known bounds and could not. Constant-variance hard oracles are inadmissible at near-minimizers. Adding a separate hidden or known 1-D component to keep the gap large also fails, because an adaptive algorithm can move to low-gap regions where the noise budget collapses. The proof instead uses a stage-dependent reveal probability `q_m ≍ ε²/(Aa(n−m) + Bε² + C)`, justified by a chain gap lemma. It also masks the whole next link of the chain so that the bound holds against randomized algorithms under coordinate hiding. The proof ancestry is Carmon et al.'s hidden chain and Arjevani et al.'s probabilistic zero-chain. Neither gives the A-term: the new step is coupling the reveal rate to the remaining suboptimality. That step is a natural adaptation, not a new framework.

**Search coverage (2026-11-17).** I searched arXiv and the web for ABC, expected smoothness, weak growth, affine and relative variance, and interpolation lower bounds for nonconvex stationarity. Besides the papers above, I found only bounds for other models (Fazla et al. [2604.16620](https://arxiv.org/abs/2604.16620) uses a distance-based Blum–Gladyshev model; heavy-tailed and (L₀,L₁) bounds). None of these bounds the A coefficient. I did not read Arjevani et al.'s theorem text verbatim. OpenReview-only submissions and Khaled–Richtárik's full text (for a possible remark on lower bounds) were not checked. The result was introduced in commit `4aa4d0f7` (2026-11-17). The companion note agrees with the Lean statement. It correctly disclaims novelty for the C, B and deterministic terms and for the SGD upper bound.

**Conclusion**

**Yes. For noise that scales with the suboptimality gap, this is a new and essentially tight lower bound for every algorithm.** The strongest previous lower bound on this class comes by inclusion from Arjevani et al.'s bounded-variance bound. That bound cannot see the `A` term.

| | necessary calls |
|---|---|
| previous (Arjevani / Carmon) | `Ω(LΔ/ε² + LΔC/ε⁴)` |
| this result | `Ω(LΔ/ε² + BLΔ/ε² + LAΔ²/ε⁴ + LΔC/ε⁴)` |

The gain is real whenever `AΔ` exceeds both `C` and `ε²`. For example, with `B = C = 0`, every algorithm needs order `ε⁻⁴` calls rather than `ε⁻²`. This shows that variance that vanishes at minimizers does not help in the worst case. Together with Khaled–Richtárik's SGD bound, it settles the class complexity `Θ((LΔ/ε²)(1+B+AΔ/ε²+C/ε²))` up to a universal constant. It holds only for `ε² ≤ LΔ/2²⁶`, in polynomially large dimension, and for an expected-gradient-norm criterion.

The comparison establishes a larger necessary budget. The search found no prior A-coefficient lower bound, but it cannot rule one out completely, and Khaled–Richtárik's full text and OpenReview-only material were not checked. The proof adapts Arjevani's technique with a gap-adaptive reveal rate. That rate is needed because the exact-infimum offset defeats the obvious reduction.

What can be claimed is the first lower bound in the `A` coefficient for nonconvex ABC noise. It makes Khaled–Richtárik's SGD rate minimax-optimal up to constants.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
