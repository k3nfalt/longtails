# Jacobian-only methods reach the optimal third-order rate for monotone equations

Lean: theorem [`result`](HomotopyNewtonMonotone.lean) (`Convergence LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone.spec budget`),
setup [`UnconstrainedLipschitzSecondDerivativeMonotone`](../Setups/UnconstrainedLipschitzSecondDerivativeMonotone.lean),
algorithm [`HomotopyNewtonAEP`](../Algorithms/HomotopyNewtonAEP.lean),
proofs in [`MonotoneTensorBounds`](../Proofs/MonotoneTensorBounds.lean),
[`StiffNewtonStage`](../Proofs/StiffNewtonStage.lean),
[`TikhonovHomotopy`](../Proofs/TikhonovHomotopy.lean),
[`HomotopyNewtonSchedule`](../Proofs/HomotopyNewtonSchedule.lean),
[`HomotopyNewtonInner`](../Proofs/HomotopyNewtonInner.lean),
[`HomotopyNewtonOuter`](../Proofs/HomotopyNewtonOuter.lean),
[`HomotopyNewtonExecution`](../Proofs/HomotopyNewtonExecution.lean),
[`HomotopyNewtonCost`](../Proofs/HomotopyNewtonCost.lean) and
[`HomotopyNewtonBudget`](../Proofs/HomotopyNewtonBudget.lean).

## Summary

For monotone equations whose operator has a Lipschitz **second** derivative, high-order methods that query that second derivative solve the problem with Θ̃((LD³/ε)^{1/4}) oracle calls. Up to logarithms this is optimal for every deterministic algorithm with access to `F`, `DF` and `D²F`: Jiang–Yoon, Thm 6.1 (p = 3), proves it for unconstrained monotone operators on ℝⁿ with the residual criterion. We prove that **the second derivative is not needed**: a method that only queries the operator and its Jacobian reaches the same rate, Õ((LD³/ε)^{1/4}) Jacobians and operator values, with no dependence on the dimension. This is the variational-inequality counterpart of Nesterov's "superfast" second-order methods for convex minimization. The convex argument does not transfer, because a monotone Jacobian need not be symmetric. Its derivative can have large rotational parts that monotonicity does not control pointwise in the step direction. Our mechanism has two parts, both new as far as we know. The first is a relative tensor bound for monotone operators. The second is a Tikhonov-homotopy Newton inner solver whose cost is governed by a Euclidean distance rather than the stiffness-weighted one.

## Problem, oracles, and accuracy

* `E` is a finite-dimensional real inner-product space of arbitrary dimension; no bound depends on `dim E`.
* `F : E → E` is `C²`, monotone (`⟪F x − F y, x − y⟫ ≥ 0`), and its second derivative is globally `L`-Lipschitz in operator norm: `‖D²F(x) − D²F(y)‖ ≤ L‖x − y‖`. This is the `p = 3` smoothness class of the high-order variational-inequality literature (`(p−1)`-th derivative Lipschitz). **No** bound on `F`, `DF`, or `D²F` themselves is assumed, and `DF` need not be symmetric.
* A zero `x⋆` with `‖x₀ − x⋆‖ ≤ D` exists. The problem is unconstrained.
* `H₀ ≥ ‖DF(x₀)‖` is an advertised upper bound that enters **only the logarithm** of the budget (and one logarithmic count in the algorithm). Every `C¹` instance has a finite `‖DF(x₀)‖`.
* Two exact oracle channels: channel `0` returns `F(x)`, channel `1` returns the Jacobian `DF(x)`. Linear algebra (one linear solve per Newton step) is not charged.
* Accuracy: the output `x̂` satisfies `‖F(x̂)‖ ≤ ε` deterministically. This is stated as an almost-sure statement over the trivial seeds.

Natural instances include convex–concave saddle functions `f(x,y)` with Lipschitz third derivative, via `F = (∇ₓf, −∇ᵧf)`. Examples are quartic games `Σᵢ(aᵢᵀx)⁴ + xᵀBy − Σⱼ(cⱼᵀy)⁴`, whose Jacobian is unbounded and whose coupling `B` may be arbitrarily large, and logistic-type games. The coordinates interact, the dimension is arbitrary, and the operator is non-symmetric. Scalar and quadratic diagnostics cannot exhibit the difficulty: affine monotone operators have `D²F = 0`, and scalar ones are gradient fields.

## Algorithm

[`HomotopyNewtonAEP`](../Algorithms/HomotopyNewtonAEP.lean), with `N = ⌈(LD³/ε)^{1/4}⌉ + 1`, `aₖ = c(k + 1)`, `Aₖ = c k(k + 1)/2`, `c = 4D/(εN(N + 1))`, `H̄ = 2H₀ + 250LD²`.

* **Outer loop.** This is the anchored extra-proximal (AEP) framework of Jiang–Yoon (an anchored inexact proximal-point step) with the fixed linear schedule `aₖ = c(k + 1)`. Each step has anchor `wₖ = (aₖx₀ + Aₖzₖ)/Aₖ₊₁` and extrapolation `cₖ = wₖ − (aₖAₖ/Aₖ₊₁)F(zₖ)`. It needs `zₖ₊₁` with the exact, checkable certificate `‖aₖF(zₖ₊₁) + zₖ₊₁ − wₖ‖ ≤ ‖zₖ₊₁ − cₖ‖/2`.
* **Inner solver (new).** Query `F(cₖ)` and set `g = ‖aF(c) + c − w‖`. If `g = 0`, take `zₖ₊₁ = c`. Otherwise run attempts `j = 0, 1, …` with radius guesses `ρⱼ = g·2ʲ/(1 + aH̄)`, step `η = min(1, 1/(50√(aL)ρⱼ))`, and homotopy parameters `bᵢ = min(a, b₀(1 + η)ⁱ)`, where `b₀ = min(a, aη2ʲ/(1 + aH̄))` and `i = 0, …, M = ⌈log(a/b₀)/log(1 + η)⌉`.
  * The parameter `bᵢ` defines the Tikhonov-type equation `bF(z) + z = c + (b/a)(w − c)`. Its solution moves from `c` (as `b → 0`) to the exact AEP resolvent point (at `b = a`).
  * Run three fresh-Jacobian Newton steps per stage, then `⌊log₂(⌈aH̄⌉ + 2)⌋ + 5` further Newton steps at `b = a`, and test the certificate.
  * Each Newton step costs one `F` and one `DF` query.
  * On failure the guess doubles. The first guess satisfies `ρ₀ ≤ R := ‖z⋆ − c‖ ≤ g`, because `g/(1 + aH̄) ≤ R ≤ g`.
* **Output:** `z_N`.

## Guarantee

`result` proves `‖F(z_N)‖ ≤ ε` with the same budget on both channels (the total number of queries is bounded):

```
budget p i = ⌈2^21 · (1 + (L D³ / ε)^{1/4}) · log(2 + H₀D/ε + LD³/ε)²⌉
```

Every query is charged, including failed attempts, the `F(c)` query, certificate queries, and padding after termination. The bound is therefore `Õ((LD³/ε)^{1/4})` Jacobians and operator values, with the logarithm squared and a large universal constant.

## Mechanism

1. **Relative tensor bound for monotone operators** ([`tensor_bound`](../Proofs/MonotoneTensorBounds.lean)).
   * Write `T(u; h, k) = ⟪u, D²F(x)[h, k]⟫` and `S = sym DF(x) ≽ 0`.
   * Monotonicity at `x ± τh` and Taylor's theorem bound only the symmetric part `⟪sym(D²F[h]) u, u⟫ ≤ ⟪Su, u⟫/τ + Lτ‖h‖²‖u‖²`.
   * The classical Koszul (Christoffel-symbol) identity `2T(u;h,k) = (T(k;h,u)+T(u;h,k)) + (T(h;k,u)+T(u;k,h)) − (T(k;u,h)+T(h;u,k))` uses only the symmetry `D²F[h,k] = D²F[k,h]`. Together with an optimised polarization, it gives
     `|⟪u, D²F(x)[h,k]⟫| ≤ 2√L (‖u‖_S‖h‖‖k‖ + ‖u‖‖h‖_S‖k‖ + ‖u‖‖h‖‖k‖_S)`.
     There is exactly one stiffness seminorm per term. For gradient fields (`F = ∇f`), full symmetry gives the stronger convex bound used by Nesterov, which has no stiffness seminorm on the step direction. The general monotone bound is weaker by exactly the rotational terms. The identity itself is folklore.
2. **Stiffness obstruction.** Unlike the convex case, the term `‖u‖‖h‖_S‖k‖` lets the rotational, skew part of `D²F[h]` in soft directions be as large as `√(sL)‖h‖` for a stiff direction `h` with eigenvalue `s` of `S`. Monotonicity allows exactly this: the `2 × 2` block `[[s, m],[m, Lτ]]` must be positive semidefinite.
   * Concretely, on a globally monotone quartic operator in `ℝ⁴` with one stiff coordinate, one intermediate coordinate, and a rotating soft pair coupled by `m x₀ (x₂, x₃)` with `m ≈ √(sL)`, at the third-order scale `aLR² = 0.1`:
     * a frozen-Jacobian Picard or Tseng-type inner solver started at the AEP extrapolation fails to converge once `as ≳ 10²`;
     * fresh-Jacobian Newton started at `c` overshoots to distance `≈ √(as)·R`.
   * The cause is that the AEP extrapolation and anchoring re-excite stiff components by about `D/k` in every step. A Newton step from `c` therefore sees the stiffness-weighted distance `‖z⋆ − c‖_{I+aS}`, which can be much larger than the controlled Euclidean distance.
   * These numerical diagnostics only motivated the design; the proof does not use them.
3. **Newton in the stiffness metric** ([`newton_error`, `newton_quarter`](../Proofs/StiffNewtonStage.lean)).
   * For `G(z) = bF(z) + z − v` and the metric `nq_b(x; u) = ‖u‖² + b⟪DF(x)u, u⟫`, a fresh-Jacobian Newton step satisfies `‖e⁺‖_{N_z} ≤ √(bL)‖e‖² + 2√(bL)‖e‖‖e‖_{N_z} + bL‖e‖³`.
   * With metric comparability (from the same monotonicity bound with `τ = 2`), each step divides the squared error by four once `169 b L ‖e‖²_{N⋆} ≤ 1`.
4. **Tikhonov homotopy controlled by the Euclidean distance** ([`TikhonovHomotopy`](../Proofs/TikhonovHomotopy.lean)).
   * The solutions `z(b)` of `bF(z) + z = c + (b/a)(w − c)` satisfy `‖z(b) − c‖ ≤ ‖z(a) − c‖ = R` for `b ≤ a`.
   * Consecutive solutions satisfy the identity `b₁(F(z₂) − F(z₁)) + (z₂ − z₁) = (1 − b₁/b₂)(z₂ − c)`. Hence `nq_{b₂}(z₂; z₂ − z₁) ≤ 5(1 − b₁/b₂)²R²`, which is stiffness-free on the right.
   * With stage ratio `η ≈ 1/(50√(aL)R)`, every stage starts inside the Newton region. One AEP step therefore costs `O((1 + √(aL)R)·log)` queries.
5. **Accounting.**
   * The guess bracket charges all attempts to the true radius `R`.
   * The AEP stability sum `Σ((k + 2)/2)²‖zₖ₊₁ − cₖ‖² ≤ (4/3)D²` and `R ≤ (3/2)‖zₖ₊₁ − cₖ‖` give, by Cauchy–Schwarz, `Σₖ√(aₖL)Rₖ = O(√(LD³/ε)·√log N / N) = O(N√log N)`. The total is `O(N log²)`.
   * A region invariant `‖zₖ − x⋆‖ ≤ D + ½Σ‖zₗ₊₁ − cₗ‖ ≤ 2.2D` places all relevant points in `B(x₀, 5D)`. There `‖DF‖ ≤ H̄` follows from `H₀` and the tensor bound (`‖D²F(x₀)‖ ≤ 6√(L‖DF(x₀)‖)`).
   * The AEP Lyapunov identities are reused from the repository's [`LazyAnchoredLyapunov`](../Proofs/LazyAnchoredLyapunov.lean).

## Comparison with prior work

| Result | Oracle | Assumption | Criterion | Cost |
|---|---|---|---|---|
| Jiang–Yoon, AEP, [arXiv 2609.30212v1](https://arxiv.org/abs/2609.30212) (Thms 4.4/4.6; Thm 6.1 lower bound; unreviewed) | `F, DF, …, D^{p−1}F` | `D^{p−1}F` Lipschitz | residual / tangent residual | `Θ̃((L_p D^p/ε)^{2/(3p−1)})`; at `p = 3`: `(LD³/ε)^{1/4}` **with a `D²F` oracle** |
| Zhang–Chen–Pan–Liu–Yang–Zhang, [arXiv 2609.23557v1](https://arxiv.org/abs/2609.23557) | `p`-th order | same, compact `X` | gap / residual | `O(T^{−(3p−1)/2})` |
| Li et al., [arXiv 2609.28246v2](https://arxiv.org/abs/2609.28246) | all derivatives, randomized | `p`-th order Lipschitz, convex–concave minimax on a compact domain | gap / tangent residual | matching lower bound `Ω(Q^{2/(3p−1)})` for adaptive and randomized algorithms (a different setting from our unconstrained residual one) |
| Lin–Jordan (Perseus, [arXiv 2205.03202](https://arxiv.org/abs/2205.03202)); Bullins–Lai ([arXiv 2007.04528](https://arxiv.org/abs/2007.04528)); Adil–Bullins–Jambulapati–Sachdeva ([arXiv 2205.06167](https://arxiv.org/abs/2205.06167)) | `p`-th order | `p`-th order Lipschitz | gap | `ε^{−2/(p+1)}` |
| AEP Newton (Jiang–Yoon, `p = 2`); repo [`LazyAnchoredExtraProximal`](LazyAnchoredExtraProximal.lean) at `m = 1` | `F, DF` | `DF` Lipschitz (`L₂`) | residual | `Θ̃((L₂D²/ε)^{2/5})` |
| Lower-order implementations via finite differences (Doikov–Grapiglia, [arXiv 2510.07992](https://arxiv.org/abs/2510.07992); **nonconvex minimization**, not variational inequalities) | `(p−1)`-th order | `p`-th derivative Lipschitz | `‖∇f‖ ≤ ε` | `O(n^{1/p} ε^{−(p+1)/p})`, dimension-dependent; the same finite-difference idea for variational inequalities would need `d` Jacobians per tensor. See also [arXiv 2611.01819](https://arxiv.org/abs/2611.01819), another lower-order method for minimization only. |
| Convex analogue: Nesterov's superfast methods ([JOTA 2021](https://doi.org/10.1007/s10957-021-01930-y), rate `O(k^{−4})` with a second-order oracle), inexact high-order proximal point ([SIOPT 2021](https://doi.org/10.1137/20M134705X)), AINE ([arXiv 2607.24520v3](https://arxiv.org/abs/2607.24520), `(L₃/ε)^{1/5}`), survey [arXiv 2208.13190](https://arxiv.org/abs/2208.13190) | `∇f, ∇²f` | `D³f` Lipschitz, convex | gap | up to the third-order rate; symmetric (convex) case only |
| **This theorem** | `F, DF` | monotone, `D²F` Lipschitz, unconstrained | residual | `Õ((LD³/ε)^{1/4})`, dimension-free |

* **What is new.** As far as our search found, no prior result attains the third-order variational-inequality rate with only Jacobian access, dimension-free. Every high-order variational-inequality method at this smoothness level queries `D²F`.
* **Overlap with the second-order class.** On instances where `DF` is also Lipschitz, the best Jacobian-only guarantee was `(L₂D²/ε)^{2/5}`. Ours, `(L₃D³/ε)^{1/4}`, is better whenever `(L₃D³/ε)^{1/4} ≪ (L₂D²/ε)^{2/5}`, in particular for all small enough `ε` with the other parameters fixed. An example is a logistic-coupled game with bounded derivatives of all orders. The two classes are not nested: neither assumption implies the other.
* **Lower-bound consistency.** The `p = 2` hard instance (Jiang–Yoon, Lemma 6.2 and the remark on p. 22, after Jang–Ryu) uses a `C^{1,1}` profile rescaled by `σ = D/D₀` with `D₀ ≍ N^{3/2}`, so `σ → 0` as `N` grows. A smoother profile would be needed for `D²F` to exist at all. Any `D²F`-Lipschitz constant of the rescaled instance therefore grows like `L₂/σ`, so there is no contradiction with the `Ω(ε^{−2/5})` second-order lower bound. This is the analogue of Nesterov's remark for minimization.
* **Prior use of homotopy.** Alves–Svaiter ([arXiv 2308.05887](https://arxiv.org/abs/2308.05887)) use a homotopy in a proximal-Newton method for variational inequalities with a Lipschitz Jacobian, to remove a step-size search. They do not obtain a third-order rate or control stiffness.
* **Not claimed as new:** the Koszul identity, the AEP outer loop, and the use of fresh-Jacobian Newton steps.

## Scope requirement

The task asked for work in second- and third-order optimization. The algorithm is a second-order method for variational problems: it queries the Jacobian of the operator, which is the Hessian for saddle problems. The guarantee is driven by third-order smoothness (Lipschitz `D²F`) and attains the optimal third-order rate.

## Limitations

* Unconstrained problems only. Constrained variational inequalities and the tangent residual are not covered.
* `H₀` and stiffness enter logarithmically. The constant `2^21` and the squared logarithm are not optimised. Linear-algebra cost is not counted.
* The lower bound is the `p`-th-order oracle bound of Jiang–Yoon (Thm 6.1, at `p = 3`: deterministic algorithms querying `F`, `DF` and `D²F`). It applies a fortiori to Jacobian-only methods. No Jacobian-oracle-specific lower bound is claimed, and the optimal logarithmic factor is open.
* The algorithm needs `L`, `D` and `ε` (fixed schedule) and `H₀`, which it uses only inside logarithmic counts. Adaptivity is not addressed.
* The dimension enters only through uncounted linear algebra (one linear solve per Newton step).
* The comparisons with the unreviewed 2026 preprints are against their stated theorems.

## Literature coverage

The search was carried out on 4 November 2026 (UTC). It covered:

* ICML 2025/2026, ICLR 2025/2026 and NeurIPS 2025/2026 title listings;
* arXiv from November 2024 to November 2026 (math.OC, cs.LG), searching for superfast/hyperfast, implementable tensor, lower-order implementations, Jacobian/second-order with third-order smoothness, and homotopy plus Newton for variational inequalities;
* full text of the closest papers listed above.

We could not systematically check COLT 2026 or recent journal online-first lists.
