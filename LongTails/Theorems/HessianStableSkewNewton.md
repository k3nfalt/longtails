# Ball-anchored Newton: polylog-in-ε second-order complexity for skew-coupled monotone equations with Hessian-stable curvature

Lean: theorem [`result`](HessianStableSkewNewton.lean) (`Convergence LongTails.Setups.HessianStableSkewMonotone.spec budget`).
- Setup: [`HessianStableSkewMonotone`](../Setups/HessianStableSkewMonotone.lean).
- Algorithm: [`BallAnchoredNewton`](../Algorithms/BallAnchoredNewton.lean).
- Proofs:
  - [`HessianStableNewton`](../Proofs/HessianStableNewton.lean): polarization and the quadratic-form Newton inequality.
  - [`BallAnchoredInner`](../Proofs/BallAnchoredInner.lean): the ball-constrained Newton contraction.
  - [`BallAnchoredSearch`](../Proofs/BallAnchoredSearch.lean) and [`BallAnchoredTrial`](../Proofs/BallAnchoredTrial.lean): ball variational inequalities, the displacement function and its modulus.
  - [`BallAnchoredOuter`](../Proofs/BallAnchoredOuter.lean): the anchored potential, region invariant and growth lemma.
  - [`BallAnchoredRun`](../Proofs/BallAnchoredRun.lean) and [`BallAnchoredSearchRun`](../Proofs/BallAnchoredSearchRun.lean): the state machine and the step search.
  - [`BallAnchoredExecution`](../Proofs/BallAnchoredExecution.lean) and [`BallAnchoredBudget`](../Proofs/BallAnchoredBudget.lean).

## Summary

We consider monotone equations `F(z) = 0` whose Jacobian splits as a constant skew part `S` plus a symmetric PSD part `H(z)`, with `H` **Hessian-stable**:

`⟪H(y)v, v⟫ ≤ exp(M‖y − x‖)⟪H(x)v, v⟫` for all `x, y, v`.

The canonical members are bilinearly coupled convex–concave saddle problems `φ(x, y) = f(x) + xᵀBy − g(y)` with logistic, softplus, log-sum-exp, pseudo-Huber or exponential losses `f, g`. We give a deterministic method using exact `F` and `DF` queries that finds `‖F(ẑ)‖ ≤ ε` with

`O( (1 + (MD)^{2/3}) · log³(3 + MD + MΛ(D + 1/M)²/ε) )` operator and Jacobian calls,

where `D ≥ ‖x₀ − x⋆‖`. Here `Λ` bounds `‖DF‖` on the explicit region `B(x⋆, 3D + 1/(4M))`. It enters **only the logarithm and the budget**; the algorithm never uses it.

The dependence on the accuracy is polylogarithmic. On this class, second-order methods analysed under a Lipschitz Jacobian pay a polynomial `(L D²/ε)^{2/5}`, with `L ≈ M·Λ`, and first-order methods pay `ΛD/ε`.

The main exponent `2/3` in `MD` matches the ball-oracle lower bound for minimization of Carmon et al. (2020). We know of no lower bound for the `(F, DF)` oracle on this class.

## Scope: second-order optimization

This is a second-order method. Every inner step queries the Jacobian `DF(x)`, which for saddle problems `F = (∇ₓφ, −∇ᵧφ)` is the (signed) Hessian of `φ`. It then takes a Newton-type step. The guarantee counts operator and Jacobian queries separately, with the same budget on each channel. The assumption that drives the rate is second-order regularity: Hessian stability of the symmetric Jacobian part.

## Problem, oracle, accuracy

- **Space and data.** `E` is a finite-dimensional real inner-product space, of any dimension; no bound depends on `dim E`. The public data are `x₀, M > 0, D > 0, ε > 0`.
- **Instance.** `F : E → E` is differentiable, and there is one linear `S` with `⟪Sv, v⟫ = 0` such that for every `x`:
  - `H(x) := DF(x) − S` is self-adjoint;
  - `H(x)` is PSD;
  - `H` is Hessian-stable with constant `M`.

  Equivalently, `F = ∇h + S·(·) + b` with `h` convex, `C²` and `M`-Hessian-stable.
- **Root.** There is `x⋆` with `F(x⋆) = 0` and `‖x₀ − x⋆‖ ≤ D`.
- **Budget-only parameter.** `Λ ≥ 0` with `‖DF(x)‖ ≤ Λ` whenever `‖x − x⋆‖ ≤ 3D + 1/(4M)`. It lives in `Params`, not in the public data. The algorithm needs neither `Λ` nor `x⋆`.
- **Oracle.** Two exact channels: channel 0 returns `F(x)` and channel 1 returns `DF(x)`. The budget charges both channels, and every query counts, including failed step-search trials and padding after termination. Linear algebra is free arithmetic, as elsewhere in this repository: one strongly monotone affine variational inequality over a Euclidean ball per Newton step.
- **Accuracy.** The output `ẑ` satisfies `‖F(ẑ)‖ ≤ ε` deterministically. This is stated almost surely over the trivial seeds.

### Provenance and necessity of the assumptions

- **Hessian stability** (equivalently, quasi-self-concordance up to constants) is a standard assumption in second-order and ball-oracle minimization:
  - Karimireddy–Stich–Jaggi, *Global linear convergence of Newton's method without strong-convexity or Lipschitz gradients*, arXiv:1806.00413, Def. 2 ("c-stable Hessian");
  - Carmon, Jambulapati, Jiang, Jin, Lee, Sidford, Tian, *Acceleration with a Ball Optimization Oracle*, NeurIPS 2020, arXiv:2003.08078, Def. 1 and §5 (Hessian stability);
  - Doikov, *Minimizing quasi-self-concordant functions by gradient regularization of Newton method*, arXiv:2308.14742.

  We use the same two-sided form and the Euclidean norm. Every loss `Σᵢ ℓ(aᵢᵀz)` with `ℓ` logistic, softplus, log-sum-exp or exp satisfies it with `M = c·maxᵢ‖aᵢ‖`.
- **Monotonicity with a symmetric/skew split** is the standard structure of convex–concave saddle problems, `F = (∇ₓφ, −∇ᵧφ)`. For bilinear coupling, `S = [[0, B], [−Bᵀ, 0]]`.
- **The constant skew part is a genuine restriction.** It excludes nonlinear couplings in which `∇²ₓᵧφ` varies. It is used in exactly one place, the Newton contraction. There `DF(y) − DF(x) = H(y) − H(x)` must be self-adjoint for the polarization lemma ([`polarization`](../Proofs/HessianStableNewton.lean)). With a varying skew part, `Δ = DF(y) − DF(x)` has an uncontrolled antisymmetric part, and the contraction argument fails.
- **The localized derivative bound `Λ`** is a budget-only regularity constant on a bounded region; it is not used by the method. It is finite for every `C¹` instance.
- **`M > 0`** is required. Affine instances are covered by any positive `M`.

**Nontrivial nonlinear family.** `F(x, y) = (Σᵢ σ(aᵢᵀx) aᵢ + By + b₁, Σⱼ σ(cⱼᵀy) cⱼ − Bᵀx + b₂)`, with `σ` the logistic sigmoid.
- This is the operator of the logistic–bilinear–logistic saddle function.
- The coordinates interact through both the data vectors and the arbitrary coupling `B`, and the dimension is arbitrary.
- `M = maxᵢ‖aᵢ‖ ∨ maxⱼ‖cⱼ‖`, while `‖B‖` and the curvature scale enter only `Λ`.
- Scalar or quadratic instances cannot show the difficulty. Quadratics have `M = 0`, and scalar monotone maps are gradients, so `S = 0`.

## Algorithm ([`BallAnchoredNewton`](../Algorithms/BallAnchoredNewton.lean))

**Constants.** Radius `r = 1/(8M)` and step cap `a_max = (2D + r)/ε`.

**Outer loop: anchored extra-proximal, as in Jiang–Yoon.** The state is `(k, A_k, z_k, g_k)`, with `g_k = F(z_k)` (and `g_0 = 0`).
- Stop and output `z_k` once `A_k ≥ a_max`.
- For a trial step `a`, form the anchor `w = (a x₀ + A z)/(A + a)` and the centre `c = w − (aA/(A + a)) g`.

**Trial(a).**
1. Query `F(c)` and `DF(c)`, and set `Γ = ‖DF(c)‖`.
2. Run `T = 2⌊log₂(k + 1)⌋ + 2⌊log₂⌈1 + 4aΓ⌉⌋ + 9` ball-constrained Josephy–Newton steps from `u₀ = c`. Step `t` queries `F(u_t)` and `DF(u_t)`, and sets `u_{t+1}` to the solution in the closed ball `B(c, r)` of the affine VI

   `⟪aF(u_t) − w + (I + aDF(u_t))(u − u_t), v − u⟫ ≥ 0` for all `v ∈ B(c, r)`.
3. Query `F(u_T)` and compute `d̂ = ‖u_T − c‖`.

**Step search.**
- *Halving:* trials at `a = a_max, a_max/2, …`.
- `d̂ ≥ 2r/3` (HIGH): halve.
- `d̂ < r/3` (LOW):
  - at `a = a_max`, this is a terminal accept;
  - otherwise bisect, arithmetically, between the LOW point and the previous HIGH point.
- Otherwise ACCEPT.
- *Accept:* `A ← A + a`, `z ← u_T`, `g ← F(u_T)`; the value `F(u_T)` is already queried.

The method uses only `x₀, M, D, ε` and the oracle replies. `Λ`, `x⋆` and the exact ball solutions appear only in the analysis.

## Guarantee

`result` proves `‖F(output)‖ ≤ ε` with the same budget on each channel. Both channel counts are bounded by the total number of queries:

```
budget p _ = ⌈2^17 · (1 + (M D)^{2/3}) · log(3 + M D + M Λ (D + 1/M)² / ε)³⌉
```

This is `Õ((MD)^{2/3})` operator values and Jacobians, with a polylogarithmic factor in `MD`, `Λ(D + 1/M)`, `M` and `1/ε`, and a large universal constant. [`total_le`](../Proofs/BallAnchoredBudget.lean) proves that the actual execution fits this budget, counting every query:
- at most `outerBound + 1` outer steps;
- at most `haltBound + bisBound + 3` trials per outer step;
- `2T + 1` queries per trial.

## Mechanism and new technical content

1. **Skew-robust ball-constrained Newton contraction** ([`newton_contract`](../Proofs/BallAnchoredInner.lean)).
   - *Setup.* Let `u⋆⋆` solve the nonlinear VI of `G(u) = aF(u) + u − w` over `B(c, r)`. Write `e = u_t − u⋆⋆` and `e' = u_{t+1} − u⋆⋆`.
   - *Comparison.* Testing both VIs and applying the scalar mean value theorem gives
     `⟪e + aDF(ξ)e, e'⟫ + ⟪(e' − e) + aDF(u_t)(e' − e), e'⟫ ≤ 0`.
   - *Polarization.* Combined with polarization for the self-adjoint difference `H(u_t) − H(ξ)`, this yields `Q(e') ≤ (e^{2Mr} − 1)²Q(e)` in the quadratic form `Q(v) = ‖v‖² + a⟪H(u_t)v, v⟫` ([`newton_core`](../Proofs/HessianStableNewton.lean)).
   - *Fixed norm.* Hessian stability changes the norm by at most `e^{1/8}` across the ball, so the error contracts by `1/4` per step in the fixed form `Q_c`.
   - *Uniformity.* The contraction is uniform in `a`, `‖S‖` and the curvature magnitude.
   - *The ball constraint is essential.* Without it, an unconstrained Newton step can overshoot along the stiff and rotational directions and leave the stability region. Example: `H = diag(λ, 0)`, `S = sJ`.
   - *Minimization analogue.* The minimization counterpart uses symmetric Newton under Hessian stability, where no skew term appears.
2. **Anchored ball-step acceleration** ([`growth_step`](../Proofs/BallAnchoredOuter.lean), [`growth_bound`](../Proofs/BallAnchoredOuter.lean), [`progress_bound`](../Proofs/BallAnchoredExecution.lean)).
   - *Per-step decrease.* Every non-terminal accepted step has displacement `‖z_{k+1} − c_k‖ ≥ r/3` and certificate residual at most `r/12`. Jiang–Yoon's anchored potential therefore drops by `(A_{k+1}/a_k)²·15r²/288` ([`accept_potential`](../Proofs/BallAnchoredOuter.lean)).
   - *Sum bound.* The potential is bounded below by `−D²/2`, so `Σ q_k² ≤ 614.4 (MD)²` with `q_k = A_{k+1}/a_k`.
   - *Growth.* `log(A_{k+1}/A_k) ≥ 1/q_k`, and two Cauchy–Schwarz steps give `n³ ≤ log²(a_max/A₁)·Σq²`. So after `O((MD)^{2/3} log^{2/3}(…))` steps `A_k` exceeds `a_max`.
   - *Prior art.* This is the anchored, monotone-operator analogue of the ball-oracle acceleration of Carmon et al. (2020, §3–4). As far as we found, it has not been published for variational inequalities.
3. **Region invariant with tightened certificates** ([`dist_step`](../Proofs/BallAnchoredOuter.lean), [`final_dist`](../Proofs/BallAnchoredOuter.lean)).
   - Accepted points are within `τ_k = r/(12(k + 1)²)` of exact anchored resolvents, which are nonexpansive toward `x⋆`.
   - Hence `‖z_k − x⋆‖ ≤ D + r/6`, every query lies in `B(x⋆, 3D + 2r)`, and the localized `Λ` suffices.
4. **Search without a priori lower step bounds** ([`halving_core`](../Proofs/BallAnchoredSearchRun.lean), [`bis_search`](../Proofs/BallAnchoredSearchRun.lean)).
   - *Modulus.* The exact displacement `φ(a) = ‖u⋆⋆(a) − c(a)‖` is Lipschitz on `[lo, a_max]`. This follows from a moving-ball VI stability lemma, [`vi_stability`](../Proofs/BallAnchoredSearch.lean) and [`phi_lip`](../Proofs/BallAnchoredTrial.lean). The modulus is polynomial in `Λ, D, 1/ε, M`.
   - *Bisection count.* The bisection keeps a LOW/HIGH bracket with `φ(hi) − φ(lo) > r/6`, so it ends after `O(log(Λ(D + 1/M)²M/ε))` trials.
   - *Halving count.* Halving ends after `O(log(ΛD amax M))` trials because `φ(a) ≤ 2aΛρ`.

## What is known, and comparison

All rates below count operator and Jacobian calls to reach `‖F‖ ≤ ε` on unconstrained monotone problems, unless noted otherwise.

| Method / paper | Assumption on the instance | Rate on this class |
|---|---|---|
| First-order: EAG/Halpern (Yoon–Ryu, ICML 2021, arXiv:2102.07922, Thm 1; Diakonikolas, COLT 2020) | `F` `L`-Lipschitz (`L = Λ` on the region) | `O(ΛD/ε)` |
| Second-order AEP (Jiang–Yoon, arXiv:2609.30212v1, Thm 3.x; p = 2) and log-free version (Zhang et al., arXiv:2609.23557v1, Thm 3.1/5.1) | `DF` `L₂`-Lipschitz; on this class `L₂ ≲ M·Λ` on the region | `O((M Λ D²/ε)^{2/5})` (polynomial in `1/ε`) |
| Higher-order convex–concave methods (arXiv:2506.08362, `Õ(ε^{-4/7})` second-order; arXiv:2604.19462, `p`-th order) | Lipschitz high-order derivatives, gap criterion | polynomial in `1/ε` |
| Ball-oracle acceleration for **minimization** (Carmon et al., arXiv:2003.08078, Thm 1/Thm 3, and §5 for Hessian-stable `f`); Doikov arXiv:2308.14742 | `S = 0` (gradient fields), `f` Hessian-stable | `Õ((MD)^{2/3})` and an `Ω((MD)^{2/3})` lower bound for ball oracles |
| Ball methods for matrix games / max-loss (Carmon–Jambulapati–Jin–Sidford, arXiv:2105.01778, 2311.10886) | primal reformulation over a finite set or simplex | not applicable to a general skew `S` with Hessian-stable `h` |
| Unaccelerated ball proximal point (reconstructed baseline, not published for VIs) | this class | `Õ(MD)` |
| **This work** | this class | `Õ((MD)^{2/3})`, polylog in `1/ε` and `Λ` |

### Regimes and honest limitations

- **When it improves.** The guarantee improves on the second-order Lipschitz-Jacobian bound whenever `(MΛD²/ε)^{2/5} ≫ (MD)^{2/3}·log³(…)`. This holds in particular for every fixed instance as `ε → 0`. It improves on first-order methods whenever `ΛD/ε ≫ (MD)^{2/3}·log³`.
- **Large-curvature regime.** When `Λ` is exponentially large, as for exp-type losses where `Λ ≤ e^{O(MD)}‖H(x⋆)‖ + ‖S‖`, the logarithm contributes a factor `MD`. The bound then becomes `Õ((MD)^{5/3}·polylog(1/ε))`. For logistic, softplus and pseudo-Huber losses with bilinear coupling, `Λ ≲ ‖B‖ + maxᵢ‖aᵢ‖²`, so the logarithm is benign.
- **Lower bounds.** The `(MD)^{2/3}` dependence matches the ball-oracle lower bound of Carmon et al. (proved for minimization, hence also for this class). For the actual `(F, DF)` oracle no lower bound is known; we claim no optimality.
- **Constants.** The constant `2^17` and the `log³` factor are not optimized.
- **Not new coverage: KKT systems.** KKT systems of linearly constrained QSC minimization lie in the class, but minimization ball acceleration on the affine subspace already covers them. We do not count them as new coverage.
- **Composition of known techniques.** The method composes known techniques:
  - Jiang–Yoon's anchored potential (reused unchanged from [`LazyAnchoredLyapunov`](../Proofs/LazyAnchoredLyapunov.lean));
  - Carmon et al.'s ball-step growth argument;
  - a Newton inner solver.

  What is not a composition of published theorems:
  - the ball-constrained Newton contraction under a skew part;
  - the anchored growth lemma with inexact, tightened certificates and its region invariant;
  - the moving-ball displacement modulus.

  As far as we found, no published monotone-operator or VI method attains a polylogarithmic dependence on `1/ε` under Hessian stability with general skew coupling.
- **Literature search coverage.** ICML 2025, ICLR 2025–2026, NeurIPS 2024–2025, and arXiv through November 2026: ball oracle × monotone / variational / saddle / minimax; Hessian stable / quasi-self-concordant × saddle / VI. We found no ball-acceleration or quasi-self-concordant result for monotone operators. Conference status of the arXiv-only items above (2609.30212, 2609.23557) is unreviewed.
- **Deterministic exact oracles only.** There are no inexact, stochastic or constrained extensions.
