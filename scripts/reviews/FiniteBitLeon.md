# FiniteBitLeon: finite-bit Leon-type SGD for heterogeneous nonconvex sums

[`result`](../../LongTails/Theorems/FiniteBitLeon.lean) proves that, on a complete point-to-point network with a separate FIFO bit link for each ordered pair of workers, the event-driven protocol [`LeonProtocol.algorithm`](../../LongTails/Algorithms/LeonProtocol.lean) returns a measurable point `X` with `E‖∇F(X)‖² ≤ ε²` by the stated deadline. The setup is [BandwidthHeterogeneousSmoothNonconvex](../../LongTails/Setups/BandwidthHeterogeneousSmoothNonconvex.lean): `F = n⁻¹Σfᵢ`, and only `∇F` is assumed `L`-Lipschitz. The local oracles are unbiased with variance at most `σ²`, and sampling is IID within each worker and independent across workers. There is no bound on how far the local functions may differ.

**Elapsed time** (simplified from the Lean `budget`, universal constants such as `2¹⁹` dropped):

$$T=O\Big(\big(1+\tfrac{L\Delta}{\varepsilon^2}\big)\Big[\max_i h_i+\tfrac{\sigma^2\sum_i h_i}{n^2\varepsilon^2}+\ell+b\big(1+\lceil d/n\rceil\log(2+nd)\big)\Big]\Big).$$

The parameters are:
- `n` workers in dimension `d`;
- `hᵢ`, the time per sample on worker `i`;
- `ℓ`, the latency of one link message, and `b`, the time per bit;
- `Δ`, the initial objective gap;
- `ε`, the target, which bounds the gradient norm (so `ε²` bounds its square).

The ranges are `L, ε, hᵢ > 0` and `Δ, σ ≥ 0`. The formula counts both phases of each exchange (reduce-scatter, then allgather), every packet header, and every batch.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Leon SGD, [Tyurin, arXiv:2603.20735v1](https://arxiv.org/abs/2603.20735) (21 Mar 2026; prior), Thm 1.7 + App. F. Specialized here to a complete graph where each link carries `1/b` real coordinates per unit time, so the minimum cut is `n−1`; `ε` replaced by `ε²` | `(LΔ/ε²)(bd/(n−1) + max hᵢ + σ²Σhᵢ/(n²ε²))` in units of *real coordinates*, with no latency → `T` above in bits | **Not comparable.** Leon charges an exact real coordinate as one unit; here each coordinate costs `log(2+nd)` bits plus `ℓ` per round | Messages of exact real vectors → finite binary messages of explicit length (the same heterogeneous function class) | None. Both need `L, σ, ε, hᵢ`. This result outputs the better of two random leaf iterates; Leon’s output rule was not compared | Requires a complete multiport network, whereas Leon allows any graph via Steiner packing. Adds the `ℓ` term, retains the leaf history, and has large constants |
| Routine finite-bit Leon (not published; derived here and sketched in the companion note): sum lattice-rounded local means as integers modulo one full-range modulus. The modulus covers the bound `‖∇F(x_k)‖ ≤ √(2LΔ)+kδ` for normalized steps of length `δ/L`, and a radius test rejects decodes that wrapped because of noise | `(1+LΔ/ε²)[max hᵢ + σ²Σhᵢ/(n²ε²) + ℓ + b(1+⌈d/n⌉ log(2+nd+LΔ/ε²))]` → `T` | Removes the `log(LΔ/ε²)` term from the bit cost only. The total speedup reaches `Θ(log(2+nd+LΔ/ε²)/log(2+nd))` only when `b⌈d/n⌉log(2+nd+LΔ/ε²) ≳ max hᵢ + σ²Σhᵢ/(n²ε²) + ℓ` and `log(LΔ/ε²) ≫ log(nd)` | None (same class) | None | The four-ary tree schedule, multi-scale anchors, and stored history. Otherwise none |

**Reduction check.** The finite-bit extension itself follows from known ingredients. Integer sums modulo a modulus are homomorphic, so arbitrarily large local offsets cancel. Reduce-scatter/allgather is standard. Normalized steps keep `∇F` inside a known envelope. Together these give the second row, with only a `log(LΔ/ε²)` loss in the bit term. I checked that sketch only on paper; it is not formalized. The genuinely new mechanism is the multi-scale tree of anchors. Each tree level `j` gets `2ʲ` times the base batch and `2j` extra bits, and the reject radius `8·4ʲδ` bounds the damage from a bad decode. These make the amortized width independent of `ε`. Proof ancestry: modulo coding with side information ([Moniqua, ICML 2020, Lemma 2](https://proceedings.mlr.press/v119/lu20a/lu20a.pdf)) and lattice coding at the scale of the input distance ([Davies et al., ICLR 2021](https://arxiv.org/abs/2002.09268)). Both need bounded input distances or bounded gradients, which this setup does not provide. [Lin–Kostina–Hassibi, IEEE TIT 2022](https://arxiv.org/abs/2002.02508) uses differential quantization for deterministic, smooth, strongly convex GD, a class that does not overlap this one.

**Search coverage (2026-11-18 UTC).** I searched arXiv and proceedings for finite-bit, lattice, modulo, and quantized distributed SGD under heterogeneous data, and for Tyurin's time-complexity line of work. I read Leon's Thm 1.7, Thm 5.2 (the lower bound, restricted to coordinate sparsifiers) and App. F through the arXiv HTML; the OpenReview version could not be compared. I did not read the multi-worker or nonconvex sections of Lin–Kostina–Hassibi, or Malenia/Amelie SGD, line by line; Malenia and Amelie also communicate real vectors. The result was introduced in commit `6e7483f0` (2026-11-18), after Leon v1. The companion note matches the Lean statement. Its "full-range baseline" is the note's own sketch, not a published result. I did not run the build or the axiom audit.

## Conclusion

**It mainly removes one logarithmic factor from the bit-communication term; the rate itself is unchanged.**

The strongest prior guarantee is Tyurin's Leon SGD (Thm 1.7). It has the same heterogeneous class, computation term, and noise term, but it sends exact real coordinates and charges no latency, so its cost units cannot be compared with this bit-level model. Moving Leon to finite bits is fairly routine: a modular sum with a single full-range modulus, plus a rejection test, gives

$$\text{bit term } b\lceil d/n\rceil\log(2+nd+L\Delta/\varepsilon^2)\;\longrightarrow\; b\lceil d/n\rceil\log(2+nd)\ \text{(this result)},$$

and every other term is identical.

So the proved total-time gain is a factor of at most `log(LΔ/ε²)/log(nd)`. It appears only when bit transmission dominates sampling time and latency, and when `LΔ/ε²` is much larger than any power of `nd`. For example, with `σ = cε` and all other parameters fixed, the gain grows like `log(1/ε)`. The cost is a complete multiport network instead of Leon's arbitrary graphs, plus a stored history of iterates and large constants.

The comparison establishes this logarithmic gain only against a baseline I reasoned out myself. The literature search found no published finite-bit guarantee for this unbounded-heterogeneity class, but that does not establish priority. If the routine full-range construction failed, the finite-bit scope itself would become the main contribution. What can be claimed is a finite-bit, latency-aware implementation of Leon-type SGD whose bits per coordinate do not grow as `ε` shrinks, obtained through a new multi-scale anchoring argument.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
