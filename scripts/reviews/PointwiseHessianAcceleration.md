# Novelty assessment: PointwiseHessianAcceleration

[The theorem](../../LongTails/Theorems/PointwiseHessianAcceleration.lean) proves the following for every convex `C³` function `f` on a finite-dimensional Euclidean space with an attained minimizer `x⋆`, under the pointwise condition `‖D³f(x)‖ ≤ M₀ + M₁‖∇f(x)‖` ([setup](../../LongTails/Setups/PointwiseHessianConvex.lean)). With exact gradient and Hessian oracles, the damped Monteiro–Svaiter/Newton-homotopy method ([algorithm](../../LongTails/Algorithms/PointwiseHessianAccelerated.lean)) returns `x_out` with `f(x_out) − f(x⋆) ≤ ε` for every seed. The method must be given `x₀, M₀, M₁, R, Δ, ε`; it is not given `H₀`.

**Proved budget.** Here `R ≥ ‖x₀−x⋆‖`, `Δ ≥ f(x₀)−f⋆` and `H₀ ≥ ‖∇²f(x₀)‖`, with `R, Δ, ε > 0`. The budget is `K` gradient calls plus `K` Hessian calls:

```
N = O( (1 + (M₀R³/ε)^{2/7} + M₁^{3/2}R³) · [1 + log(2 + (Δ + H₀R² + M₀R³ + M₁²R⁴Δ)/ε + M₁R²)]⁴ )
```

The universal constant is `2·2⁴⁵`. The result was introduced in commit `7fb86449` on 2026-11-13, so every source below is prior work.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Agafonov et al., [arXiv:2609.32977v1](https://arxiv.org/abs/2609.32977) (26 Sep 2026, preprint), Thm. 4.1 with δ=0, plus Prop. 2.7. **Restricted to** TD ∩ {‖∇²f‖ ≤ L₀+L₁‖∇f‖}, or instances with direct pairwise (LH) constants. | Via Prop. 2.7, for any ρ: `Õ(1+((M₀+M₁L₀ρe^{L₁ρ})R³/ε)^{2/7}+(M₁e^{L₁ρ}R²)^{1/3}+(R/ρ)^{2/3})`. Minimizing over ρ gives `Õ(1+(M₀R³/ε)^{2/7}+(M₁R²)^{1/3}+(M₁L₀R⁴/ε)^{1/5}+(L₁R)^{2/3})`, which is never below `(M₁L₀R⁴/ε)^{1/5}` → `N` above | Better when `(1+(M₀R³/ε)^{2/7}+M₁^{3/2}R³)·log⁴(…) ≪ (M₁L₀R⁴/ε)^{1/5}`, e.g. `M₀=0` with ε→0: polylog(1/ε) versus ε^{-1/5}. **Worse** when `M₁R² ≫ 1`: `(M₁R²)^{3/2}` versus `(M₁R²)^{1/3}`. When `(M₀R³/ε)^{2/7}` dominates, the order is the same apart from a `log⁴` loss. | Pairwise (LH), or TD plus a first-order `(L₀,L₁)` Hessian bound → pointwise TD alone. `H₀, Δ` enter only through logarithms. Whether convex TD instances exist outside every (LH) class is unverified. | Worse: the baseline needs no parameters; this method needs `M₀,M₁,R,Δ,ε`. Both certify a deterministic objective gap. | Needs `C³` instead of `C²`. Only exact Hessians, while the baseline tolerates inexact Hessians up to δ. Four logarithms. |
| Doikov, [arXiv:2308.14742v1](https://arxiv.org/abs/2308.14742) (2023), Thm. 6.2 (accelerated scheme). **Restricted to** quasi-self-concordant (QSC) `f` with constant `M`. | Outer `O((MR)^{2/3} log(Δ/ε))`. The inner Dual-Newton total carries an extra log factor involving `max‖∇²f‖` on a ball of radius `(5+c)R` → `N` | On `f=Σcosh xᵢ+½xᵀQx`, which has `M=1` and `M₀=0, M₁=1+‖Q‖`: **Worse**, because the baseline has no `‖Q‖` power while `N` grows like `((1+‖Q‖)R²)^{3/2}` | Incomparable classes. Example: `½xᵀQx+β‖x‖⁴/4` with singular `Q` satisfies TD but is not QSC. | None. Both need known parameters (the baseline needs `M,R`). | The baseline uses the relative accuracy `ε/Δ`. |
| Carmon et al., [arXiv:2205.15371v2](https://arxiv.org/abs/2205.15371) (NeurIPS 2022), Cor. 3. **Special case** `M₁=0` (Hessian-Lipschitz with constant `M₀`). | `O(1+(M₀R³/ε)^{2/7})` Hessian calls, plus `O(log log)` extra linear solves → `N` with `M₁=0` | **Worse:** the extra factor `log⁴(2+(Δ+H₀R²+M₀R³)/ε)` | Global Hessian-Lipschitz → TD with `M₁>0` | Worse: the baseline is adaptive to `M₀` | None beyond the logarithms |

**Reduction and mechanism check.** Uniformizing on the ball `B(x₀,R)` does yield a valid reduction to Carmon et al. However, the Hessian-Lipschitz constant on that ball can grow like `e^{2√M₁R}`: for `cosh`, the Hessian equals `cosh R` at `|x|=R`. The selected bound avoids this exponential growth through its localization estimates and its accounting of center movement. I found no standard reduction that reproduces those estimates. The Agafonov reduction does fail to give the polylog rate on one checked instance, 1-D `cosh` with `x⋆=0`. Taking `x=0` and `y=ρ`, where `∇f(0)=0`, forces `M̄₀ ≥ (cosh ρ−1)/ρ ≥ ρ/2`, so the Thm. 4.1 bound is `Ω((R⁴/ε)^{1/5})` for every admissible ρ. That instance is QSC, however, and Doikov's accelerated scheme reaches `O(R^{2/3}·polylog)` on it. **Proof ancestry:** Monteiro–Svaiter and Carmon et al. supply the outer acceleration, and Newton continuation supplies the inner solver. They are not competitors under TD.

**Search coverage.** The search was run on 2026-11-13 and covered arXiv, ICLR/NeurIPS proceedings, generalized second-order smoothness, QSC, and tensor methods under local smoothness. I read the theorem statements of Agafonov et al. (Thm. 4.1, Prop. 2.7) and Doikov (Thm. 6.2), and Carmon et al. Cor. 3. Fang–Marumo–Takeda ([arXiv:2607.10741](https://arxiv.org/abs/2607.10741)) is nonconvex only and was checked at abstract level. Semenov–Jaggi–Doikov (ICLR 2026) and Jerad ([arXiv:2606.30225](https://arxiv.org/abs/2606.30225)) were not read directly. I could not verify the Mathematical Programming version of Doikov. The companion note is consistent with the Lean statement, but it omits Doikov's accelerated QSC baseline.

## Conclusion

**There is a real, but narrow, gain over the best pairwise generalized-smoothness method; on the instances checked, it is not a gain for the problem class.**

The strongest direct baseline is Agafonov et al. (Sept 2026), which needs pairwise local Hessian smoothness. Converted to the pointwise condition, its proved bound always contains an `ε^{-1/5}` stiffness term. The selected bound does not.

| regime | Agafonov et al. (via reduction) | this result |
|---|---|---|
| `M₀=0`, ε→0 | `Ω(ε^{-1/5})` | `O(log⁴(1/ε))` |
| `M₁R² ≫ 1` | `(M₁R²)^{1/3}` | `(M₁R²)^{3/2}` |

The verified instance showing this gap, cosine-hyperbolic coordinates plus a quadratic, is also quasi-self-concordant. On it, Doikov's older accelerated Newton scheme has better dependence on `R` and `‖Q‖` than the selected result. Elsewhere, the selected result needs known parameters, `C³` regularity, and exact Hessians, and it carries four logarithms. On the quartic example, a rough derivation (not fully checked) suggests Agafonov's direct constants give the same leading term with a better `M₁` exponent.

The open question is whether convex TD instances exist with small `M₀` that lie outside both the QSC class and every favorable (LH) class. A verified example of that kind would turn this into a clear regime-specific improvement. Literature-wise, I found no earlier accelerated convex guarantee stated under the pointwise condition alone, but that does not establish priority.

What can be claimed is an accelerated guarantee under pointwise third-derivative growth, with `H₀` and `Δ` entering only through logarithms. The only demonstrated advantage is against one reduction.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
