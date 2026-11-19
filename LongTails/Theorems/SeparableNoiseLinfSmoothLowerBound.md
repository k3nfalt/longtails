# Lower bound: ℓ∞-smooth nonconvex optimization with separable noise

Lean files: [theorem](SeparableNoiseLinfSmoothLowerBound.lean) · [setup (high-dimensional)](../Setups/HighDimensionalSeparableNoiseLinfSmooth.lean) · [setup (general)](../Setups/SeparableNoiseLinfSmooth.lean) · [embedding family](../Proofs/KhintchineSignFamily.lean) · [embedding maps](../Proofs/LinfEmbedding.lean) · [reduction](../Proofs/LinfLowerTransfer.lean). The companion upper bound is [MinibatchSignSgdUpperBound](MinibatchSignSgdUpperBound.md).

## Result

The setup is the sign-descent geometry used for SignSGD, Signum and Adam-type methods. The objective `f : ℝ^d → ℝ` is differentiable and ℓ∞-smooth:

\[
\sum_i |\partial_i f(x)-\partial_i f(y)| \le L\,\max_i|x_i-y_i| \qquad\text{for all }x,y.
\]

The initial gap satisfies `f(x0) − inf f ≤ Δ`. The oracle is gradient-only, with IID samples. Its replies `g(x,ω)` are unbiased, and the coordinate-wise standard deviations satisfy the separable bound

\[
\sum_i \sqrt{\mathbb E\,(g_i(x,\omega)-\partial_i f(x))^2}\ \le\ S \qquad\text{at every }x .
\]

The criterion is ℓ1-stationarity in expectation, `E‖∇f(x̂)‖₁ ≤ ε`.

`result : NonConvergence spec budget` holds with

\[
\texttt{budget} = \Big\lfloor \frac{L\Delta\,(1+S^2/\varepsilon^2)}{2^{60}\,\varepsilon^2}\Big\rfloor .
\]

It applies to every randomized algorithm, every valid parameter, and every call count `b ≤ budget` (including `b = 0`). The valid regime is

\[
2^{30}\varepsilon^2\le L\Delta,\qquad 2^{168}\Big(1+\tfrac{L\Delta(1+S^2/\varepsilon^2)}{\varepsilon^2}\Big)^{16}\le d .
\]

`S = 0` is allowed, so the deterministic term `LΔ/ε²` is covered for randomized algorithms. The regime is nonempty: take `L = Δ = 1`, `ε = 2^{-15}`, `S = 0`, and `d` large. The hard instance depends on the algorithm, not on its seed.

Together with the upper bound for minibatch SignSGD, `(⌈8LΔ/ε²⌉+1)(⌈16S²/ε²⌉+1)` calls on the same class, this gives

\[
\Theta\!\Big(\frac{L\Delta}{\varepsilon^2}\Big(1+\frac{S^2}{\varepsilon^2}\Big)\Big)
\]

up to universal constants, on the lower-bound valid set. On that set minibatch SignSGD is minimax-optimal on this pointwise separable class among all randomized gradient-only algorithms in high dimension.

## Construction and mechanism

The proof is a black-box reduction from the repository's Euclidean lower bound [AbcNoiseLowerBound](AbcNoiseLowerBound.lean). That bound is used with `A = B = 0` and `C = S²`; with these values it is Arjevani et al.'s bounded-variance construction against randomized algorithms. It is applied in dimension `D` at accuracy `3ε`.

**Embedding family.** Let `p` be a prime with `D + 4 ≤ p ≤ 2D + 6` (Bertrand), and index rows by cubic polynomials `c ∈ (ZMod p)⁴`. Set `s_c(i) = σ(c₀ + c₁i + c₂i² + c₃i³)`, where `σ` is the symmetric sign on `ZMod p`: `σ(0) = 0` and `σ(−t) = −σ(t)`. The Vandermonde determinant makes the values at any 4 distinct nodes uniform on `(ZMod p)⁴`, so the family is 4-wise independent with mean zero and `E s² = E s⁴ = (p−1)/p`.

With `n = p⁴` and `A = S/n`, the module proves, for every `w ∈ ℝ^D`:

\[
\tfrac13\|w\|_2\ \le\ \|Aw\|_1\ \le\ \|w\|_2,\qquad \|A^\top v\|_2\le\|v\|_\infty .
\]

The lower bound uses the pointwise inequality `|x| ≥ x²/t − x⁴/(4t³)` and the fourth-moment bound `E⟨s,w⟩⁴ ≤ 3a²‖w‖⁴`, where `a = (p−1)/p`. The family is padded into `ℝ^d` because `p⁴ ≤ d`.

**Lifted instance.** The lifted objective is `f(x) = h(Aᵀ(x − x0))`, and the lifted oracle replies `A·G(Aᵀ(x − x0), ω)` with the same IID seeds. The following properties hold:

- **ℓ∞-smoothness.** `‖A(∇h(u) − ∇h(v))‖₁ ≤ L‖u − v‖₂` and `‖Aᵀz‖₂ ≤ ‖z‖∞`.
- **Gap and infimum.** These are preserved because `Aᵀ` is onto: `AᵀA` is a positive multiple of the identity.
- **Unbiasedness.** This is preserved by linearity.
- **Separable noise.** For any Euclidean noise `ξ`, Jensen's inequality and the column orthogonality `Σ_c s_c(i)s_c(j) = (p−1)p³ δ_ij` give

  \[
  \sum_c \sqrt{\mathbb E\,((A\xi)_c)^2}\ \le\ \sqrt{\mathbb E\|\xi\|_2^2}\ \le S .
  \]

**Simulation.** Any algorithm for `f` becomes an algorithm for `h`: query `Aᵀ(x − x0)` and feed back `A·reply`. The two executions coincide call by call. If the ℓ∞ algorithm achieved `E‖∇f(x̂)‖₁ ≤ ε`, the simulated algorithm would achieve `E‖∇h‖₂ ≤ 3ε`, which the Euclidean bound forbids. The Euclidean budget at accuracy `3ε` dominates the stated budget because `81 ≤ 2⁷`.

## Why the obvious arguments fail

- **Axis-aligned Arjevani instance.** A Euclidean `ℓ`-smooth chain on `T` coordinates has a tridiagonal Hessian with ‖H‖_{∞→1} ≈ 3ℓT. Its ℓ∞-constant is therefore about `Tℓ`, and the bound degrades to about √(LΔ)/ε.
- **Block-diagonal averaging embeddings.** These also lose a factor `T`.
- **Separable 1-D lifting** (Tao–Yu–Zhang, Step 4). This needs a one-dimensional stochastic lower bound for randomized algorithms. Chewi–Bubeck–Salim show that randomization already helps in one dimension (Θ(√(LΔ)/ε) versus Θ(LΔ/ε²) deterministic), so this route cannot work. The high-dimensional regime of this theorem is therefore partly intrinsic.
- **What works.** A near-isometric ℓ2→ℓ1 embedding with polynomial `n` (Khintchine/Kashin type, derandomized by 4-wise independence) does preserve the class.

## Prior work and novelty

**Upper bounds (known).** Bernstein et al., [signSGD, ICML 2018](https://arxiv.org/abs/1802.04434), Thm. 1 (separable smoothness), and Tao–Yu–Zhang, [arXiv:2605.06615v1](https://arxiv.org/abs/2605.06615), Thm. 1 (ℓ∞-smoothness). Both prove `O(LΔ/ε² + LΔ‖σ⃗‖₁²/ε⁴)` for minibatch SignSGD.

**Previous lower bounds** are algorithm-specific or deterministic:

- Tao–Yu–Zhang, Thm. 2 (SignSGD itself), Thm. 3 (SGD itself), Thm. 5 (Muon itself).
- Jiang–Maladkar–Mokhtari, [COLT 2025, arXiv:2406.04592](https://arxiv.org/abs/2406.04592), Thms. 2.1 and 3.3: deterministic algorithms, noiseless, fixed dimension; Thms. 3.2 and 4.1: AdaGrad- and SGD-specific.
- Yu et al., [arXiv:2602.07425](https://arxiv.org/abs/2602.07425) (NeurIPS 2026 poster): compares only the ε-exponent with the Euclidean lower bound through ‖·‖₁ ≥ ‖·‖₂.
- Arjevani et al., [Math. Prog. 2023](https://arxiv.org/abs/1912.02365): Euclidean only.

**New contribution.** As far as our searches found, this is the first problem-class lower bound for all randomized gradient-only algorithms in this ℓ∞/separable-noise geometry that captures both terms jointly. The SGD-specific lower bounds of Tao–Yu–Zhang (Thm. 3) and Jiang et al. (Thm. 4.1) are proved on fixed-vector subclasses, so they also hold on the pointwise class. On that class they can now be compared with its exact minimax rate, which minibatch SignSGD attains. Whether any algorithm beats SignSGD on the smaller fixed-vector class remains open.

**Technique.** The technique is a short reduction and is not claimed as new. It is related to two lines of earlier work.
- **Spectral geometry.** Zhang–Lin, [arXiv:2605.18528v4](https://arxiv.org/abs/2605.18528), Thm. 3.1, and Hübler et al. (2026) prove class lower bounds in spectral geometry with dual-norm noise. The separable class here is smaller than the dual-norm class, so it needs its own lower bound.
- **Sign encoding.** Jin (2026), as described by Zhang–Lin, is a Euclidean, sign-encoded version of Arjevani et al.'s instance, and Zhang–Lin's construction builds on it.

The derandomized 4-wise independent embedding makes the reduction fully black-box. Kornilov et al., [arXiv:2502.07923](https://arxiv.org/abs/2502.07923), give high-probability upper bounds for sign methods under heavy-tailed noise.

## Limitations

- **Noise model.** The noise bound is pointwise: the coordinate profile `σ_i(x)` may change with `x`, with `Σ_i σ_i(x) ≤ S`. This class contains every fixed-vector class `{σ_i(x) ≤ σ_i}` with `‖σ⃗‖₁ ≤ S`, which is the model of Bernstein et al., Jiang et al. and Tao–Yu–Zhang.
  - The lower bound is **not** proved for the fixed-vector class, which remains open here.
  - **Obstruction.** The reused hard oracle's noise contains a term `(weight_trunc − weight_full)·(2/R)·w` proportional to the query point. It comes from the smoothMax wall that hides the chain. Every wall- or projection-based hiding device we examined has such a dense, query-proportional term, so per-coordinate variances cannot be bounded uniformly in `x`.
  - We therefore do **not** claim minimax optimality of SignSGD in the fixed-vector model.
- **Oracle.** The oracle is gradient-only. Oracles that also return function values are not covered.
- **Dimension and regime.** The lower bound needs very large dimension, a polynomial of degree 16 in `LΔ(1+S²/ε²)/ε²`, and the regime `LΔ ≥ 2³⁰ε²`. Low dimension is not covered. Some dimension requirement is unavoidable because of the one-dimensional randomized speedups.
- **Constants.** The constant gap between upper and lower bound is about 2⁶⁷.

## Scope compliance

- **Tight pair.** The requested tight upper/lower pair is delivered on one Template setup: this NonConvergence theorem and the Convergence theorem of the companion note, with matching parameter dependence in both terms on the lower-bound valid set.
- **Setup.** The setup uses the standard geometry for sign-based optimizers (ℓ∞-smoothness, ℓ1-stationarity). Its noise assumption is the pointwise generalization of the standard separable-noise assumption.
- **Reuse.** Previous techniques are reused through a black-box call to the repository's Euclidean ABC lower bound.
