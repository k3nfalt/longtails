# Upper bound: minibatch SignSGD under ℓ∞-smoothness and separable noise

Lean files: [theorem](MinibatchSignSgdUpperBound.lean) · [setup](../Setups/SeparableNoiseLinfSmooth.lean) · [algorithm](../Algorithms/MinibatchSignSgd.lean) · [one-step and telescoping bounds](../Proofs/SignSgdRate.lean) · [execution and tuning](../Proofs/SignSgdConvergence.lean). The companion lower bound is [SeparableNoiseLinfSmoothLowerBound](SeparableNoiseLinfSmoothLowerBound.md).

## Setting

The setup is exactly the class of the companion lower bound, in any dimension `d` and for any sample space `Ω`. The objective `f : ℝ^d → ℝ` is differentiable, ℓ∞-smooth with `Σ_i|∂_if(x) − ∂_if(y)| ≤ L max_i|x_i − y_i|`, and has gap `f(x0) − inf f ≤ Δ`.

The oracle is gradient-only, with fresh IID samples per call, and its replies are unbiased. The coordinate deviations are square-integrable and satisfy the pointwise separable bound `Σ_i (E(g_i(x,ω) − ∂_if(x))²)^{1/2} ≤ S`. Valid parameters are `L > 0`, `S ≥ 0`, `Δ ≥ 0`, `ε > 0`.

The smoothness form is the dual-norm Lipschitz-gradient condition used for arbitrary-norm steepest descent: Kovalev, [arXiv:2503.12645](https://arxiv.org/abs/2503.12645); Pethick et al., [ICML 2025, arXiv:2502.07529](https://arxiv.org/abs/2502.07529); Balles–Pedregosa–Le Roux, [arXiv:2002.08056](https://arxiv.org/abs/2002.08056). It implies Tao–Yu–Zhang's two-sided quadratic Assumption 3a with the same `L`. For twice-differentiable objectives, Bernstein et al.'s separable smoothness with vector `L⃗` (−diag L⃗ ≼ ∇²f ≼ diag L⃗) gives this form with the loose constant `(Σ_i√L_i)²`. Tao–Yu–Zhang's Lemma 1 converts separable smoothness into their two-sided form 3a with `‖L⃗‖₁`. We do not claim that the two smoothness forms are equivalent.

## Algorithm and output

`minibatchSignSgd` runs `T = ⌈8LΔ/ε²⌉ + 1` steps. Each step draws `B = ⌈16S²/ε²⌉ + 1` fresh oracle replies at the current point and averages them into `ḡ`. It then moves by `x ← x − η·sign(ḡ)` with `η = ε/(2L)`. The output is the iterate `x_τ` at an index `τ` drawn uniformly from `{0,…,T−1}` using the algorithm's own seed.

`result : Convergence spec budget` proves `E‖∇f(x_τ)‖₁ ≤ ε` with exactly

\[
\texttt{budget} = (\lceil 8L\Delta/\varepsilon^2\rceil+1)\,(\lceil 16S^2/\varepsilon^2\rceil+1)
= O\!\Big(\frac{L\Delta}{\varepsilon^2}\Big(1+\frac{S^2}{\varepsilon^2}\Big)\Big)
\]

oracle calls, all of them counted. The proof uses four steps:

1. **Descent.** The ℓ∞ descent lemma gives `f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)r²` whenever `max_i|y_i − x_i| ≤ r`.
2. **Sign comparison.** Pointwise, `a·sign(m) ≥ |a| − 2|m − a|`.
3. **Minibatch error.** The minibatch variance identity gives `E|ḡ_i − ∂_if| ≤ σ_i(x)/√B`.
4. **Telescoping.** Telescoping over the IID blocks gives `(1/T)Σ_t E‖∇f(x_t)‖₁ ≤ Δ/(ηT) + 2S/√B + Lη/2 ≤ ε`.

## Novelty and scope

This rate is known: Bernstein et al., [ICML 2018](https://arxiv.org/abs/1802.04434), Thm. 1, and Tao–Yu–Zhang, [arXiv:2605.06615](https://arxiv.org/abs/2605.06615), Thm. 1. They state it with a fixed noise vector and rates in `‖σ⃗‖₁`. The proof here is unchanged under the pointwise profile `Σ_iσ_i(x) ≤ S`, which contains every fixed-vector class with `‖σ⃗‖₁ ≤ S`.

The theorem is included to close the problem in Template terms. Together with the new lower bound it shows that the complexity of this class is Θ((LΔ/ε²)(1 + S²/ε²)) up to universal constants, on the lower bound's high-dimensional valid set `2³⁰ε² ≤ LΔ`, `d ≥ 2¹⁶⁸(1 + LΔ(1+S²/ε²)/ε²)¹⁶`. This upper bound itself holds in every dimension.
