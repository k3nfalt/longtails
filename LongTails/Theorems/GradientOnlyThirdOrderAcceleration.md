# Gradient-only ε^{-5/3} stationarity under Lipschitz third derivatives

Lean: [`GradientOnlyThirdOrderAcceleration.lean`](GradientOnlyThirdOrderAcceleration.lean) (theorem `result`),
setup [`GradientOnlyThirdOrderNonconvex.lean`](../Setups/GradientOnlyThirdOrderNonconvex.lean),
algorithm [`GradientOnlyGuarded.lean`](../Algorithms/GradientOnlyGuarded.lean).

## Setup

- **Space.** `E` is a finite-dimensional real inner-product space of arbitrary dimension. No bound depends on `dim E`.
- **Objective.** `f : E → ℝ` with the following assumptions:
  - `f` is `C³`.
  - `∇f` is `L₁`-Lipschitz.
  - The third derivative (the derivative of the Hessian map `x ↦ D(∇f)(x)`) is `L₃`-Lipschitz in operator norm.
  - `f(x₀) − f(x) ≤ Δ` for all `x`.

  These are the assumptions of the third-order case of Carmon–Duchi–Hinder–Sidford (CDHS17).
- **Oracle.** The algorithm may only query `∇f(x)`. It never sees function values, Hessians, or anything else.
- **Accuracy criterion.** Return `x̂` with `‖∇f(x̂)‖ ≤ ε`. The algorithm is deterministic, so this holds for every run. In Lean it is
  stated almost surely with respect to the (trivial) seed law.
- **Parameters.** The only requirement is that `L₁, L₃, Δ, ε` are positive. There is no regime restriction.

## Result

**Budget.** The algorithm makes at most

`(⌊2048 Δ L₃^{1/3} / ε^{4/3}⌋ + 1) · (97 ⌈√(L₁/(L₃^{1/3} ε^{2/3}) + 4) · log(1 + 200 (L₁ + 4 L₃^{1/3} ε^{2/3}) Δ / ε²)⌉ + 290)`

gradient calls, and its output satisfies `‖∇f(x̂)‖ ≤ ε`. The budget is
`Õ(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3} + √(L₁/(L₃^{1/3}ε^{2/3})))`. The second term is one epoch, and it is dominated by
the first as soon as `ε^{2/3} ≤ Δ L₃^{1/3}`.

**Exact accounting.** The Lean budget equals (epochs) × (calls per epoch). It counts every gradient call
the algorithm makes, including all quadrature nodes. Each epoch makes:

- `N` AGD calls;
- 1 call for `∇f(x_N)`;
- `64N` Step-A quadrature calls;
- `32N` Step-B quadrature calls;
- `192` candidate-evaluation calls.

## Prior work and what is new

| Work | Oracle | Rate to `‖∇f‖ ≤ ε` (`C^{1,1} ∩ C^{3,1}`) |
|---|---|---|
| Gradient descent | gradient | `O(L₁Δ ε^{-2})` |
| Carmon–Duchi–Hinder–Sidford, ICML 2017 ([arXiv:1705.02766](https://arxiv.org/abs/1705.02766)), third-order guarantee | value + gradient | `Õ(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3})` |
| Xiong–Jerad–Cartis ([arXiv:2605.02127](https://arxiv.org/abs/2605.02127)), parameter-free | value + gradient | `Õ(ε^{-5/3})` |
| Li–Lin, JMLR 2023 (restarted AGD) | gradient only | `O(ε^{-7/4})` (Lipschitz Hessian) |
| Jiang–Mokhtari–Patitucci, STOC 2025 | gradient only | `O(d^{1/4} ε^{-13/8})`, dimension-dependent |
| Zhou–Sugiyama–Suzuki ([arXiv:2610.02791v1](https://arxiv.org/abs/2610.02791)), trapping-or-descent framework | gradient only | `O(d^{4/3} ε^{-4/3} + d²)`, dimension-dependent |
| **This result** | **gradient only, deterministic** | **`Õ(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3})`, dimension-free** |

**Lower bounds.**
- Zhou ([arXiv:2606.05438](https://arxiv.org/abs/2606.05438)) gives `Ω(ε^{-5/3})` for deterministic value-and-gradient
  methods in high dimension under Lipschitz third derivatives.
- Zhou–Sugiyama–Suzuki (2610.02791, Cor. 6.3 with `p = 3`) give a randomized value-and-gradient lower bound
  `Ω(Δ L₁^{1/2} L₃^{1/6} ε^{-5/3})`. It matches the bound here in `Δ`, `L₁`, `L₃` and `ε` up to the logarithmic factor.

**What is new.** Zhou–Sugiyama–Suzuki state the gap explicitly in 2610.02791v1 (§1, discussion after Theorem 1.4):
"the strict gradient-only complexity therefore remains open between the exponents 5/3 and 7/4."
This result closes it:
- The dimension-free strict gradient-only complexity under Lipschitz gradients and Lipschitz third derivatives is
  `ε^{-5/3}`, tight up to the logarithmic factor.
- It matches the value-and-gradient rate of CDHS17 without function values.

**Why the obvious gradient-only routes fail.**
- **Li–Lin's analysis.** Under these assumptions, the Landau–Kolmogorov inequality only gives a Hessian-Lipschitz
  constant `ρ ≲ √(L₁L₃)`. Plugging that into Li–Lin's analysis yields `ε^{-7/4}`, not `ε^{-5/3}`.
- **Naive substitution into CDHS17.** CDHS17 uses function values in three places:
  - its convexity certificates (`f(u) ≥ f(v) + ⟨∇f(v), u−v⟩ + (σ/2)‖u−v‖²` along AGD iterates);
  - its negative-curvature exploitation;
  - its "best iterate" selection.

  Replacing each value by a line integral of gradients introduces quadrature errors. These errors are not relative to
  the certificate margins `α‖u−v‖²`: pairs can be far apart, and errors accumulate along AGD paths.

## Technical mechanism

The algorithm keeps the CDHS17 "guarded AGD on `f + α‖·−c‖²`" structure with `α = 2L₃^{1/3}ε^{2/3}`, but changes four things.

1. **Localized quadrature value surrogate.**
   - **Surrogate.** `V(a,b)` is a composite 2-point Gauss–Legendre rule for `∫_a^b ⟨∇f, db⟩` on the straight segment,
     using `m = 16` pieces.
   - **Error bound.** It satisfies `|V(a,b) − (f(b) − f(a))| ≤ L₃‖b−a‖⁴/m³` (`GradientQuadrature.surrogate_error`).
     The cubic Taylor terms cancel exactly because the nodes are at `±1/√3`.
   - **Why it is relative.** Every compared pair lies in a ball of radius `O(√(α/L₃))` around the epoch center, and
     segments always start at a single tested point, never along an AGD path. So the error is at most `(α/32)‖u−v‖²`,
     a fixed fraction of the certificate margin.
2. **Robust tests.** A pair test that passes implies the exact strong-convexity inequality with `μ = α/2`
   (`pass_supports`). A test that fails implies exact negative curvature `D_f(u,v) ≤ −(α/2)‖u−v‖²` (`fail_deficit`).
   So CDHS17's Proposition 1 can be re-proved verbatim from the tested inequalities alone (`GradientOnlyAgd.prop_one`).
   It uses no global convexity and no function values.
3. **Exit and stall handled with exact gradients.**
   - An AGD iterate leaving the ball of radius `R = √(α/L₃)/21` certifies a decrease of `αR²` in `f`.
   - Termination is detected from `∇f(x_N)` exactly.
   - When the regularized gradient is not small, Prop 1 applied to the comparator `w = x_N − ∇F(x_N)/L`, together with
     the AGD horizon, forces a failed test. That is, a negative-curvature witness exists.
4. **Witness exploitation by surrogate argmin.**
   - For a witness, six candidates are compared by `V(c, ·)`:
     - two points on the line through the last two iterates (a quartic interpolation lemma);
     - four `±η` steps along the negative-curvature direction, with `η = √(α/L₃)/4`.
   - At least one candidate decreases `f` by `α²/(4096L₃)`.
   - The surrogate argmin loses at most twice the quadrature error, so each epoch decreases `f` by at least
     `α²/(8192L₃) = ε^{4/3}/(2048 L₃^{1/3})`.

**Epoch count.** Each epoch either returns a point with `‖∇f‖ ≤ ε` or moves the center with that guaranteed decrease
(`GradientOnlyEpochResult.epoch_result`). After `⌊2048ΔL₃^{1/3}ε^{-4/3}⌋ + 1` epochs the second case is impossible.

## Limitations

- **Constants.** The constants (2048, 97, 290, `m = 16`) are not optimized.
- **Log factor.** The bound carries one `log(1 + LΔ/ε²)` factor from the AGD horizon. The lower bounds leave this
  factor open.
- **Problem class.** The result concerns first-order stationarity under global Lipschitz third derivatives. It does
  not cover Hölder variants, stochastic gradients, or second-order stationarity.
- **Novelty basis.** The novelty claim rests on the gap stated in 2610.02791v1, which is three weeks old at the time of writing. We
  found no later work closing it, but the literature after that preprint was checked only through arXiv listings up
  to 2026-10-24.
