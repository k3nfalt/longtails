# Lazy anchored extra-proximal method: a Jacobian–operator trade-off for monotone equations

Lean: theorem [`result`](LazyAnchoredExtraProximal.lean) (`Convergence LongTails.Setups.UnconstrainedLipschitzJacobianMonotone.spec budget`),
setup [`UnconstrainedLipschitzJacobianMonotone`](../Setups/UnconstrainedLipschitzJacobianMonotone.lean),
algorithm [`LazyAnchoredExtraProximal`](../Algorithms/LazyAnchoredExtraProximal.lean),
proofs in [`LazyAnchoredLyapunov`](../Proofs/LazyAnchoredLyapunov.lean),
[`FrozenJacobianSplitting`](../Proofs/FrozenJacobianSplitting.lean),
[`LazyAnchoredInner`](../Proofs/LazyAnchoredInner.lean),
[`LazyAnchoredOuter`](../Proofs/LazyAnchoredOuter.lean),
[`LazyAnchoredExecution`](../Proofs/LazyAnchoredExecution.lean) and
[`LazyAnchoredBudget`](../Proofs/LazyAnchoredBudget.lean).

## Problem, oracles, and accuracy

* `E` is a finite-dimensional real inner-product space and `F : E → E` is a monotone operator,
  `⟪F x − F y, x − y⟫ ≥ 0`, which is differentiable with an `L`-Lipschitz Jacobian,
  `‖DF(x) − DF(y)‖ ≤ L‖x − y‖`. A zero `x⋆` with `F x⋆ = 0` and `‖x0 − x⋆‖ ≤ D` exists.
  No Lipschitz bound on `F` itself is assumed, there is no compact domain, and `DF` need not be
  symmetric. This is the standard class of the second-order literature on monotone equations,
  variational inequalities, and convex–concave minimax problems (Monteiro–Svaiter's NPE, LEN, AEP Newton);
  a convex–concave `f(x, y)` with `L`-Lipschitz Hessian gives `F = (∇ₓf, −∇ᵧf)`.
* Two oracle channels: channel `0` returns `F(x)` (cost 1) and channel `1` returns `DF(x)`
  (cost `m ≥ 1`, e.g. `m ≈ d` when the Jacobian is formed from `d` Jacobian–vector products).
  This is the cost model of lazy second-order methods (Doikov–Chayti–Jaggi, ICML 2023; Chen–Liu–Zhang,
  ICLR 2025; Chen–Liu–Luo–Zhang, COLT 2026; Zhang–Chen–Liu–Zhang, arXiv 2610.03222).
  Linear algebra is not charged: each inner step solves one linear system with the matrix
  `(1 + τ/a)I + τJ`.
* Accuracy: the returned point `y` satisfies `‖F(y)‖ ≤ ε`, deterministically. A residual bound implies
  the restricted gap bound `sup_{‖u − x⋆‖ ≤ r} ⟪F u, y − u⟫ ≤ ε(r + ‖y − x⋆‖)`, and for minimax problems
  the corresponding duality-gap bound on bounded sets. The converse implication does not hold, so the
  comparisons below with gap-criterion results are one-way.

## Algorithm

Let `N = ⌈(L D²/(m ε))^{2/5}⌉ + 1`, `c = 4D/(ε N (N + 1))`, `a_k = c(k + 1)`, `A_k = c k(k + 1)/2`.
The outer loop is the anchored extra-proximal (AEP) framework of Jiang–Yoon
([arXiv 2609.30212v1](https://arxiv.org/abs/2609.30212), Alg. 1 with `H = 0`) with this **fixed**
step schedule:

* `w_k = (a_k x0 + A_k z_k)/A_{k+1}`, `c_k = w_k − (a_k A_k/A_{k+1}) F(z_k)`;
* find `z_{k+1}` with `r_{k+1} = a_k F(z_{k+1}) + z_{k+1} − w_k` and `‖r_{k+1}‖ ≤ ‖z_{k+1} − c_k‖/2`.

The new part is the inner solver. One Jacobian `J = DF(c_k)` and one value `F(c_k)` are queried. The
equation `F(y) + (y − w_k)/a_k = 0` is split into the affine, strongly monotone part
`B(y) = F(c_k) + J(y − c_k) + (y − w_k)/a_k` (its resolvent is one linear solve) and the Taylor remainder
`A(y) = F(y) − F(c_k) − J(y − c_k)`, and Tseng's forward–backward–forward iteration is run from `c_k`
with step `τ = a_k/K`, `K = 5 L a_k ρ̂ + 1`. The forward–backward–forward residual
`(a_k/τ)(z_i − z_{i+1})` equals `a_k F(y_i) + y_i − w_k` exactly, so it is a certificate of the AEP
relative-error condition; the first certified `y_i` becomes `z_{k+1}`. The radius guess `ρ̂` starts at
`R̄_k 2^{−J_k}` with `R̄_k = D a_k/A_{k+1}` and doubles after `⌈(8/3) K log(36K²)⌉ + 1` uncertified steps
(all attempts reuse the same Jacobian). The output is `z_N`.

## Guarantee

`result` proves `‖F(z_N)‖ ≤ ε` within the per-channel budget

* Jacobians: `N = ⌈(L D²/(m ε))^{2/5}⌉ + 1`;
* operator values: `2^15 (m + 1) N (log₂(m N) + 1)²`,

counting every query (including failed doubling attempts and the `F(c_k)` queries; padding after the last
outer step is harmless). With `T = L D²/ε`, the weighted cost `m·N + #F` is
`O((m + 1) N log²(m N)) = Õ(m + m^{3/5} T^{2/5})`. The same argument with any number `N` of outer steps
gives `N` Jacobians and `Õ(N + T/N^{3/2})` operator values; only the balanced choice of `N` above is
formalized.

## Mechanism (what is new)

1. *Frozen-Jacobian splitting with an exact certificate.* With the Jacobian frozen at the extrapolated
   point, the remainder `A` is `L·r`-Lipschitz on a ball of radius `r`, so forward–backward–forward
   contracts at rate `1 − 3/(8K)` once `ρ̂` exceeds the distance `R_k` from `c_k` to the exact resolvent
   point. The number of operator values per outer step is `O((1 + J_k + L a_k R_k) log)`, i.e. it adapts to
   the actual step length rather than to a worst-case bound.
2. *A-priori radius.* Applying the AEP potential step to the exact resolvent point gives
   `R_k ≤ D a_k/A_{k+1}`, which bounds the number of doublings.
3. *Cauchy–Schwarz accounting with a fixed schedule.* Exactness gives `R_k ≤ (3/2)‖z_{k+1} − c_k‖`, and the
   AEP stability sum `Σ (A_{k+1}/a_k)²‖z_{k+1} − c_k‖² ≤ (4/3)D²` then yields
   `Σ_k L a_k R_k = O(L D²/(ε N^{3/2}))`. No outer bisection is needed: AEP Newton needs a line search
   because its Newton step is only valid for small steps, whereas here the inner cost absorbs large steps.

The AEP potential identity, its descent with relative error, the stability sum and the residual bound
`‖F(z_N)‖ ≤ 2D/A_N` are re-derived in Lean (`LazyAnchoredLyapunov`), so the proof does not rely on the
unreviewed preprint.

## Comparison (cost `m·#DF + #F`, `T = L D²/ε`)

| Method | Criterion, domain | Cost |
|---|---|---|
| AEP Newton, Jiang–Yoon, arXiv 2609.30212v1 (Thms 4.4, 4.6; unreviewed) | tangent residual, composite | `Õ(m T^{2/5})` |
| Zhang et al., arXiv 2609.23557v1 (unreviewed) | tangent residual, compact `X` | `O(m T^{2/5})` |
| Halpern-NPE, Chen et al., arXiv 2608.08463v1 (Assumption 2.1, Thm 4.1; checked in the PDF) | proximal residual, compact `X` | `Õ(m T^{1/2})` |
| LEN, Chen–Liu–Zhang, ICLR 2025 ([arXiv 2410.09568v2](https://arxiv.org/abs/2410.09568)) | minimax gap | `Õ(m + m^{2/3} T^{2/3})` |
| Lazy Minimax-AIPE, Chen–Liu–Luo–Zhang, COLT 2025 ([arXiv 2506.08362](https://arxiv.org/abs/2506.08362), Thm 5.7) | minimax gap, bounded domains | `Õ(m + m^{5/7} T^{4/7})` |
| VIJI, Agafonov et al., NeurIPS 2024 ([arXiv 2405.15990](https://arxiv.org/abs/2405.15990)): `O(ε^{-2/3} + δ ε^{-1})` calls with `δ`-inexact Jacobians | gap | no lazy result stated; our estimate for stale Jacobians (`δ ≈ L·distance`) is no better than `m^{1/3} T^{2/3}` |
| First-order (extra assumption `F` is `L₁`-Lipschitz), EAG/FEG | residual | `O(L₁ D/ε)` |
| Haihan Zhang et al., [arXiv 2609.13462v2](https://arxiv.org/abs/2609.13462) (Thm 3.3 as cited in [`CachedJacobian.md`](CachedJacobian.md); unreviewed) | tangent residual | `Õ(m T^{2/5})` |
| [`CachedJacobian`](CachedJacobian.lean) (this repository, PR #67) | tangent residual, compact `X` | `Õ(m + √(m T))` |
| Lazy composition of the optimal residual framework with lazy strongly monotone solves (reconstructed in [`CachedJacobian.md`](CachedJacobian.md); not stated in a paper) | tangent residual, compact `X` | `Õ(m + m^{4/5} T^{2/5})` |
| Cutting-plane VI methods plus residual recovery (dimension `d`; see the discussion in [`CachedJacobian.md`](CachedJacobian.md)) | residual, bounded domain | `Õ(m + d)` |
| **This theorem** | residual, unconstrained | `Õ(m + m^{3/5} T^{2/5})` |

Up to logarithms this improves AEP Newton and the optimal non-lazy methods by `m^{2/5}` uniformly, Halpern-NPE
by `m^{2/5} T^{1/10}`, the reconstructed lazy composition by `m^{1/5}`, and (through the one-way
residual-to-gap conversion) LEN and lazy Minimax-AIPE for all `m, T ≥ 1`. At `m = 1` it recovers the optimal
second-order rate `Õ(T^{2/5})` (lower bound: Jiang–Yoon Thm 6.1) without an outer line search, with worse
logarithmic factors than AEP Newton.

*Relation to `CachedJacobian`.* That theorem treats a known compact convex `X` (assumptions only on `X`,
tangent-residual criterion) and proves `Õ(m + √(m T))`. It also applies to the present class: take
`X = B(x0, 2D)`; if `u ∈ X` and `n ∈ N_X(u)` satisfy `‖F(u) + n‖ ≤ ε/4`, then either `n = 0`, or
`n = λ(u − x0)/(2D)` with `λ ≥ 0`, and monotonicity with `F(x⋆) = 0` gives
`λD ≤ ⟨n, u − x⋆⟩ ≤ ⟨F(u) + n, u − x⋆⟩ ≤ (ε/4)·3D`, so `‖F(u)‖ ≤ ε`. On the present class the new bound is
therefore smaller by the factor `(T/m)^{1/10}` when `T > m`, and both are `Õ(m)` when `T ≤ m`. The classes are
not nested: `CachedJacobian` also covers constrained problems and needs its assumptions only on `X`, while
this theorem is unconstrained and assumes them globally.

*Dimension-dependent methods.* Cutting-plane methods on a ball containing `x⋆`, followed by a residual-recovery
step, use `Õ(d)` operator values (with logarithms of instance-dependent magnitudes) plus `O(1)` Jacobians.
The bound here is dimension-free, so it is an improvement only when `m^{3/5} T^{2/5} ≪ d`, which requires
the Jacobian price to be much smaller than the dimension (`m ≪ d`), e.g. sparse or structured Jacobians
obtained with few compressed derivative passes, or separately priced derivative services. If `m` is
proportional to `d` (a dense Jacobian formed from `d` products), there is no gain over cutting planes beyond
logarithmic factors.

## Limitations and open questions

* Unconstrained problems only (AEP Newton, Halpern-NPE and `CachedJacobian` also handle constraints).
* The gain over dimension-dependent cutting-plane methods requires `m^{3/5} T^{2/5} ≪ d`, hence `m ≪ d`;
  when `m` is proportional to `d` there is no improvement beyond logarithms.
* The step schedule and budget need `D`, `L`, `ε`, `m`; there is no adaptivity to unknown parameters.
* Linear algebra is not charged (one linear solve with `(1 + τ/a)I + τJ` per inner step; with one
  factorization per Jacobian this costs `O(d²)` per step after an `O(d^ω)` factorization).
* No lower bound is known in the lazy model; the exponent `3/5` may be improvable. By analogy, in convex
  minimization our own estimate for the naive combination (an accelerated inner solver with condition
  number `m²`) gives `m^{3/7}`, while arXiv 2610.03222 establishes the optimal exponent `m^{1/7}`; the
  `m^{3/7}` figure is our estimate, not a statement of that paper. A first-order inner solver for
  strongly monotone problems cannot beat linear dependence on
  its condition number in general, so an improvement would have to exploit that the remainder vanishes to
  first order at `c_k`.
* The bound carries a `log²(mN)` factor and the explicit constant `2^15`.
* The strongest compared baselines (arXiv 2609.30212, 2609.23557, 2609.13462, 2608.08463, 2610.03222) are
  recent, unreviewed preprints.

## Example

`F = (∇ₓf, −∇ᵧf)` for `f(x, y) = Σᵢ softplus(aᵢᵀx) − Σⱼ softplus(cⱼᵀy) + xᵀBy + (r/2)(‖x‖² − ‖y‖²)` is
monotone with Jacobian Lipschitz constant at most `(6√3)^{-1} max(Σᵢ‖aᵢ‖³, Σⱼ‖cⱼ‖³)`, while
`‖DF‖ ≥ ‖B‖` can be arbitrarily large, so first-order guarantees degrade with `‖B‖` and the coordinates
interact through `aᵢ`, `cⱼ` and `B`.

## Credits

The outer loop is the AEP framework of Jiang–Yoon (anchored extrapolation, relative-error proximal step,
potential and stability lemma); anchoring follows Halpern (1967), Lieder (2021), Yoon–Ryu (2021) and
Lee–Kim (2021); the inner solver is Tseng's forward–backward–forward splitting (2000); the
large-step/Cauchy–Schwarz accounting follows Monteiro–Svaiter (2012, 2013); lowering the effective
regularization and solving subproblems with a stale Hessian follows the lazy/Catalyst line
(Doikov–Chayti–Jaggi 2023; Chen–Liu–Luo–Zhang 2025, 2026; Zhang–Chen–Liu–Zhang 2026). The contribution is
the lazy rate and the frozen-Jacobian inner solver that makes the fixed-schedule accounting work.
