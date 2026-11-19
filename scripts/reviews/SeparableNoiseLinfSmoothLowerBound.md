# Novelty assessment: SeparableNoiseLinfSmoothLowerBound

The [theorem](../../LongTails/Theorems/SeparableNoiseLinfSmoothLowerBound.lean) is a `NonConvergence` result. Fix any valid parameters and any randomized gradient-only algorithm, and run it with at most `⌊LΔ(1+S²/ε²)/(2⁶⁰ε²)⌋` calls to unbiased IID oracles. Then some ℓ∞-smooth instance with pointwise separable noise defeats it: its output does not satisfy `E‖∇f(x̂)‖₁ ≤ ε`. The setup is in [setup](../../LongTails/Setups/HighDimensionalSeparableNoiseLinfSmooth.lean) and [base setup](../../LongTails/Setups/SeparableNoiseLinfSmooth.lean), and the reduction is in [reduction](../../LongTails/Proofs/LinfLowerTransfer.lean). The setup has no `allowedAlgorithm` restriction.

**Necessary calls:**

$$\Omega\Big(\frac{L\Delta}{\varepsilon^2}+\frac{L\Delta S^2}{\varepsilon^4}\Big)\quad\text{whenever } L\Delta\ge 2^{30}\varepsilon^2,\ \ d\ge 2^{168}\Big(1+\tfrac{L\Delta}{\varepsilon^2}+\tfrac{L\Delta S^2}{\varepsilon^4}\Big)^{16}.$$

The parameters are:
- `L`: the ℓ∞→ℓ1 gradient-Lipschitz constant, `Σᵢ|∂ᵢf(x)−∂ᵢf(y)| ≤ L‖x−y‖∞`.
- `Δ`: the initial gap.
- `S`: a bound on `Σᵢ √Var(gᵢ(x))` at every `x`. The coordinate profile may vary with `x`.
- `ε`: the expected ℓ1-stationarity accuracy of the output.
- `d`: the dimension.

`S = 0` is allowed. The hard instance depends on the algorithm but not on its seed. The repository's companion [MinibatchSignSgdUpperBound](../../LongTails/Theorems/MinibatchSignSgdUpperBound.lean) uses `(⌈8LΔ/ε²⌉+1)(⌈16S²/ε²⌉+1)` calls on the same class. On the valid set that is the same order, with a constant gap of about 2⁶⁷.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tao–Yu–Zhang, [arXiv:2605.06615v1](https://arxiv.org/abs/2605.06615) (7 May 2026), Thm 2. *Applies to SignSGD only.* | Ω(LΔ/ε² + LΔ‖σ‖₁²/ε⁴) for SignSGD → Ω(LΔ/ε² + LΔS²/ε⁴) for every randomized algorithm | Same order. The new bound applies to every algorithm instead of one. | Lower bound for one method → lower bound for the whole problem class. | Thm 2 lower-bounds the best iterate of SignSGD; here any output fails | Proved only on the pointwise class (`Σσᵢ(x) ≤ S`), which is broader than their fixed-vector class `σᵢ(x) ≤ σᵢ`. Over all algorithms, the fixed-vector class is still open. Needs huge `d` and `LΔ ≥ 2³⁰ε²`. |
| Arjevani et al., [Math. Prog. 2023 / arXiv:1912.02365](https://arxiv.org/abs/1912.02365), Thm 1 (bounded variance). *Euclidean ℓ2 class only.* | Ω(LΔ/ε² + LΔσ²/ε⁴) in ℓ2 geometry → the same form in ℓ∞/ℓ1 geometry | Not comparable as stated. Moving their instance over by norm comparisons multiplies L by up to D and S by up to √D, where D is the instance dimension, so the transferred bound is weak. | ℓ2-smooth class with ℓ2 stationarity → ℓ∞→ℓ1-smooth class with ℓ1 stationarity | None | Needs polynomial dimension of degree 16 instead of the Euclidean degree 4. Gradient-only oracle (no function values). |
| Zhang–Lin, [arXiv:2605.18528v4](https://arxiv.org/abs/2605.18528) (v1 May, v4 11 Oct 2026), Thm 3.1. Hübler–Pethick–Sra, [arXiv:2606.14560v1](https://arxiv.org/abs/2606.14560) (Jun 2026), Thms 3.7 and E.9. *Matrix spectral→nuclear geometry, dual-norm noise.* | Ω(min{m,n}·LΔσ₀²/ε⁴) at p=2, all randomized algorithms (zero-respecting only in E.9) → Ω(LΔ/ε² + LΔS²/ε⁴) | Not comparable: the classes, norms and noise measures all differ. | Different class: a vector geometry with separable noise, not matrices with `E‖ξ‖_nuc^p ≤ σ₀^p` | None | The heavy-tailed `p<2` case is not covered. No reduction to or from these results was checked. |

**Reduction check.** The proof composes a Euclidean hard instance `h` with an explicit linear map: `f(x) = h(Aᵀ(x−x₀))`. The map `A`, built from 4-wise-independent signs, satisfies `‖w‖₂/3 ≤ ‖Aw‖₁ ≤ ‖w‖₂` and `‖Aᵀv‖₂ ≤ ‖v‖∞`. Pushing the noise through `A` keeps it separable, because the columns of `A` are orthogonal. This black-box argument is short, but no checked work does this transfer. The naive transfers lose factors of the dimension, as the table notes.

**Proof ancestry, not competitors.** The Euclidean randomized lower bound comes from Arjevani et al., used through the repository's [AbcNoiseLowerBound](../../LongTails/Theorems/AbcNoiseLowerBound.lean) with `A=B=0`, `C=S²`. The embedding is a Khintchine/Kashin-type ℓ2→ℓ1 near-isometry. The new work is the derandomized embedding and the proof that it preserves the noise and smoothness assumptions.

**Search coverage.** On 2026-11-19 I searched arXiv and the web for lower bounds under ℓ∞ smoothness and ℓ1 stationarity, for sign-method optimality, and for non-Euclidean or dual-norm stochastic lower bounds.
- Read: the lower-bound theorem statements of Tao–Yu–Zhang, Zhang–Lin v4 and Hübler–Pethick–Sra. Parts of each HTML page were seen only through summaries.
- Checked: Yu et al. [arXiv:2602.07425v2](https://arxiv.org/abs/2602.07425) contains no lower-bound theorem.
- Not verified: "Jin (2026)" and Jiang–Maladkar–Mokhtari's COLT 2025 deterministic bounds.
- Companion note: no material discrepancy with the Lean result. The note itself says, correctly, that the fixed-vector case is not covered.
- Chronology: everything cited here predates the commit that introduced the result, `04a401ca` (19 Nov 2026).

## Conclusion

**Yes. This is a new lower bound for the whole problem class of ℓ∞-smooth sign-descent geometry with separable noise, and it matches minibatch SignSGD.** The strongest prior lower bound in this geometry is Tao–Yu–Zhang's Theorem 2, which applies only to SignSGD.

$$\text{prior: } \Omega\Big(\tfrac{L\Delta}{\varepsilon^2}+\tfrac{L\Delta\|\sigma\|_1^2}{\varepsilon^4}\Big)\ \text{for SignSGD only}\ \longrightarrow\ \text{now: } \Omega\Big(\tfrac{L\Delta}{\varepsilon^2}+\tfrac{L\Delta S^2}{\varepsilon^4}\Big)\ \text{for every randomized gradient-only algorithm.}$$

On the pointwise class, minibatch SignSGD attains this rate up to a universal constant. The rate is therefore settled there, as long as `LΔ ≥ 2³⁰ε²` and the dimension is very large (polynomial in the call budget). The Euclidean bound of Arjevani et al. and the 2026 matrix Muon bounds do not imply it. The first fails to transfer without losing dimension factors, and the second concerns a different geometry and noise measure.

The limits are concrete. The bound is proved on the pointwise class `Σᵢσᵢ(x) ≤ S`, not on the standard fixed-vector model `σᵢ(x) ≤ σᵢ` of Bernstein et al. and Tao–Yu–Zhang, where minimax optimality is still open. The dimension requirement is enormous. The proof is a short black-box embedding of a Euclidean bound.

The comparison shows that this is a genuine new class-level bound. Priority rests on a search of a fast-moving 2026 literature, and some sources were read only in part. What can be claimed: the first verified algorithm-independent lower bound showing that minibatch SignSGD is minimax-optimal, up to a constant, for ℓ∞-smooth problems with pointwise separable noise in high dimension.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
