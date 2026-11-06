# BFGS with weak Wolfe steps on standard self-concordant functions

Lean result: [`result`](SelfConcordantBFGS.lean). Setup: [`SelfConcordantBFGS`](../Setups/SelfConcordantBFGS.lean). Algorithm: [`method`](../Algorithms/SelfConcordantBFGS.lean), defined as `bfgs x0 B0`. Main proofs: [`SelfConcordantBFGSAccuracy`](../Proofs/SelfConcordantBFGSAccuracy.lean).

## Setting

The objective `f` is a standard self-concordant function on an open convex domain `D ⊆ ℝ^d`, in the sense of Nesterov–Nemirovski:

- `f` is C³ on `D`, with explicit derivatives `Df`, `D2f`, `D3f`.
- The Hessian is nondegenerate: `D2f x v v > 0` for `v ≠ 0`.
- `|D3f x h v v| ≤ 2 ‖h‖_x ‖v‖_x²`, where `‖v‖_x² = D2f x v v`.
- `f` is closed: every sublevel set `{x ∈ D : f x ≤ c}` is closed.
- A minimizer `x⋆ ∈ D` exists.

This is standard self-concordance (constant `M_f = 1`, Nesterov, *Lectures on Convex Optimization*, 2018, §5.1) plus two standard additions: a nondegenerate Hessian and an existing minimizer.

- The formal bound is the `(h, v, v)` form of the trilinear inequality. For C³ functions it is implied by Nesterov's `|D³f(x)[u,u,u]| ≤ 2‖u‖_x³`, because the third derivative is symmetric (Nesterov 2018, Lemma 5.1.2 and Thm 5.1.1).
- Closedness of `f` is encoded as closed sublevel sets.

The class includes:

- logarithmic barriers of polytopes and of second-order and semidefinite cones, plus linear terms (the central-path objectives `t·cᵀx − Σ log(b_i − a_iᵀx)`);
- `−log det` and the barrier `x log x − log x`;
- strongly convex functions with Lipschitz Hessian, after the usual rescaling.

Barrier-type instances are **not** strongly self-concordant: their Hessians blow up at the boundary. Gradients are not Lipschitz and there is no global condition number.

### Public parameters

- Initial point `x0 ∈ D` and initial SPD matrix `B0`.
- Weak Wolfe parameters `0 < c1 < c2 < 1`. Any values are allowed, including the defaults `c1 = 1e-4`, `c2 = 0.9`.
- `Δ ≥ f(x0) − f⋆`.
- `Φ0 ≥ Φ(B0; ∇²f(x0))`, where `Φ(B;H) = 2 log det(B+H) − log det B − log det H − 2d log 2` (`mismatch` in the setup).
  - `Φ(B;H) = Σ_i log((1+λ_i)²/(4λ_i))` with `λ_i = eig(H^{-1}B)`; it vanishes iff `B = H`.
  - It grows only logarithmically in the eigenvalue mismatch.
- Accuracy `ε > 0`.

### Oracle

Each call takes a query `(x, v)` with `x ∈ D` and `Df x v ≤ 0`. It returns a step `η` and the exact gradient at `x + ηv`. The point `x + ηv` must stay in `D`. When `v` is a descent direction, the step satisfies the weak Wolfe conditions `f(x+ηv) ≤ f(x) + c1 η Df x v` and `Df(x+ηv) v ≥ c2 Df x v`.

The oracle is adversarial: the theorem holds for every admissible answer. Each iteration costs one call. As in Jin–Mokhtari and in the repository's `LinearPredictorBFGS` setup, the internal cost of the line search is not counted.

Such steps exist, but this is not formalized. Along a descent ray, `φ(η) = f(x+ηv)` is convex on the open interval `{η ≥ 0 : x+ηv ∈ D}`.

- If the interval is bounded, closedness forces `φ → ∞` at its end.
- If it is unbounded, then `φ` is either eventually increasing or bounded below. In the latter case `φ′ → 0 ≥ c2 φ′(0)`, so Armijo holds on an initial segment and the curvature condition holds eventually.
- In both cases, continuity gives a point satisfying both conditions, by the classical bisection argument.

### Algorithm

The algorithm is unmodified BFGS:

- `s_t = −η_t B_t^{-1} g_t`, `y_t = g_{t+1} − g_t`;
- `B_{t+1} = B_t − B_t s_t s_tᵀ B_t/(s_tᵀB_ts_t) + y_t y_tᵀ/(y_tᵀ s_t)`;
- the output is the last iterate `x_T`.

`allowedAlgorithm` forces exactly this method, `bfgs x0 B0`.

## Result

Write `δ = min(c1, 1 − c2)`. The last iterate satisfies `f(x_T) − f⋆ ≤ ε` after `T = ⌈N⌉ + 1` iterations (`⌈N⌉ + 2` oracle calls), where

```
N = 2^21 (d+1)(Δ+1) [ (Δ+1)/(c1³ δ²) + (d+1)/(c1 δ⁴) ] + 10 Φ0/δ² + 4 log(64 + 2/ε)/δ .
```

For fixed line-search parameters this is

```
O( Φ(B0; ∇²f(x0)) + log(1/ε) + d(1+Δ)² + d²(1+Δ) ).
```

Every quantity in this bound is affine invariant.

- There is no condition number, Lipschitz constant or diameter.
- The dependence on the initial Hessian mismatch is logarithmic.
- The dependence on the accuracy is `O(log(1/ε)/δ)`.

The proof counts potential decrements; it does not prove a per-step contraction.

The dependence on the line-search parameters, `c1^{-3}δ^{-2}` and `c1^{-1}δ^{-4}`, is explicit and crude. At the default `c1 = 10^{-4}` the leading constant exceeds `10^{20}·2^{21}`. This is an artefact of the proof (short steps are those of local length `≤ c1/32`) and is not claimed to be necessary.

## What is new, and the technical mechanism

1. **A global non-asymptotic bound for standard Wolfe-BFGS on standard self-concordant functions.**
   - Jin & Mokhtari, *Affine-invariant global non-asymptotic convergence analysis of BFGS under self-concordance* ([arXiv 2507.00361v2](https://arxiv.org/abs/2507.00361), NeurIPS 2025), prove linear and superlinear rates under **strong** self-concordance. Their §7 says: "A limitation is the reliance on strong self-concordance; extending results to standard self-concordance is a potential future direction."
   - Strong self-concordance, `∇²f(y) − ∇²f(x) ⪯ M‖y−x‖_z ∇²f(w)`, excludes barrier functions.
   - Gao & Goldfarb ([arXiv 1612.06965](https://arxiv.org/abs/1612.06965), Optim. Methods Softw. 2019) prove superlinear convergence of BFGS with a closed-form adaptive step size (not a Wolfe line search) for *strongly convex* self-concordant functions.
   - Our dedicated search found no other non-asymptotic global bound for this class.

2. **The symmetric log-determinant potential.** The proof uses `U_k(B, g; Q) = k Φ(B; Q) + log gᵀ(B+Q)^{-1}g`.
   - **Static lemma.** Take any SPD `B, Q` and an exact secant pair `y = Qs`, with `θ = yᵀs / (−gᵀs)`. Then BFGS changes `U_k` by exactly `log F_k(t, p, ν)`, with
     - scalars `t = b′/β₁` and `p = b′/β₂`,
     - `b′ = (Bs)ᵀ(B+Q)^{-1}(Qs)`, `β₁ = sᵀBs`, `β₂ = sᵀQs`,
     - `ν = (θ−1)²`.
   - The proof uses two rank-one determinant identities and an explicit solve of `(B₊+Q)x = g₊` on `B+Q`: [`BFGSLogPotential`](../Proofs/BFGSLogPotential.lean) and [`BFGSLogStep`](../Proofs/BFGSLogStep.lean).
   - **Scalar inequality.** An analytic bound gives `F_k ≤ ν̄(1 + 1/(2k−1)) < 1` whenever `ν ≤ ν̄ < 1` and `k ≥ ⌈1/(1−ν̄)⌉ + 2` ([`BFGSLogScalar`](../Proofs/BFGSLogScalar.lean)).
   - So every Wolfe step with short local length decreases the potential by at least `δ/2`, whatever the spectrum of `B`.
   - This is a quantitative form of the "self-correcting" behaviour of BFGS, valid in any dimension. Its per-step decrease does not depend on `d`.
     - Powell (1986, *How bad are the BFGS and DFP methods when the objective function is quadratic?*, Math. Programming 34) analysed two-variable quadratics with exact line searches.
     - Byrd–Liu–Nocedal (1992) gave a qualitative version.
   - Unformalized remark: on quadratics the static lemma alone gives an `O(Φ(B0; A) + log 1/ε)` iteration bound. There `Q = A` is fixed, so there are no switch costs, and Armijo gives `θ ≤ 2(1−c1)`.
   - Earlier potentials have different properties:
     - Byrd–Nocedal's `tr − log det`, as used by Rodomanov–Nesterov and Jin–Mokhtari, is linear in large eigenvalue mismatch.
     - The Rodomanov–Nesterov (JOTA 2021, [arXiv 2004.14866](https://arxiv.org/abs/2004.14866)) potential `log det + trace` gives local superlinear rates only.

3. **Self-concordance calculus for Wolfe segments with no global constants.**
   - **Oscillation lemma.** On any segment where `f` oscillates by at most `Δ`, all Hessians agree up to the factor `e^{±(6Δ+6)}`. The proof is integral-free: monotone comparison functions plus AM-GM ([`SelfConcordantCalculus`](../Proofs/SelfConcordantCalculus.lean)).
   - **Short steps** (local length `r ≤ c1/32`): Dikin-type comparisons with factor `e^{±8r}`.
   - **Metric switches.** These control the change of `U_k` when the reference metric moves between consecutive secant averages `Q_t = ∫₀¹ ∇²f(x_t + τ s_t) dτ`. The cost is `(3kd+1)·log`-ratio ([`SelfConcordantSegment`](../Proofs/SelfConcordantSegment.lean)).
   - **Counting.** Long steps decrease `f` by `≥ c1³/4096`, so there are at most `4096Δ/c1³` of them. Short steps give `Σ r_t² ≤ 4Δ/c1`. A Cauchy–Schwarz argument then bounds the number of short steps ([`SelfConcordantBFGSRate`](../Proofs/SelfConcordantBFGSRate.lean)).
   - **Termination.** The potential is bounded below by `log ‖g‖²_{Q^{-1}}` (determinant inequalities only). The initial Newton decrement is at most `2Δ + 1` (Dikin ellipsoid via closedness). A Newton decrement `≤ 1/8` implies `f − f⋆ ≤ 2λ²`.

## Comparison with the closest results

The comparison below uses self-concordant units: `Δ` and `Φ0` are affine invariant.

| Work | Class | Line search | Guarantee |
|---|---|---|---|
| Jin–Mokhtari 2024 ([arXiv 2404.16731](https://arxiv.org/abs/2404.16731), [NeurIPS 2024](https://proceedings.neurips.cc/paper_files/paper/2024/file/1e269abc604816c35f600ae14b354efd-Paper-Conference.pdf)) | μ-strongly convex, L-smooth (+ Lipschitz Hessian) | Armijo–Wolfe | `(1−1/κ)` linear rate; κ-free linear phase after a κ-dependent transient |
| Jin–Mokhtari 2025 (arXiv 2507.00361, NeurIPS 2025) | strongly self-concordant (constant `M`) | weak Wolfe | Thm 3.3 / eq. (93): `O(Ψ(B̃0) + (Ψ(B̄0) + (1+D0)²)D0 + log 1/ε)` with `Ψ(A) = tr A − d − log det A`, `D0 = 2ω^{-1}(M²(f(x0)−f⋆)/4)`; then superlinear |
| Rodomanov 2024 ([arXiv 2404.15051](https://arxiv.org/abs/2404.15051)) | strongly convex, L-smooth, Lipschitz Hessian | Armijo, Armijo–Goldstein, Wolfe–Powell | multi-stage bounds before superlinear convergence; for a reasonable `B0` the total is of order `κ² log(·) + d log κ + log 1/ε` (v1) |
| Gao–Goldfarb 2019 | strongly convex + self-concordant | closed-form adaptive step | superlinear |
| **This result** | **standard self-concordant (includes barriers)** | **weak Wolfe, any c1<c2** | **`O(Φ0 + log 1/ε + d(1+Δ)² + d²(1+Δ))` iterations** |

- **Overlap class.** Strongly convex functions with Lipschitz Hessian are self-concordant after scaling by `M²/4`. On this class:
  - our bound has no `κ`;
  - its transient depends on the initial mismatch only through `Φ0 ≤ d·log((1+κ_B)²/(4κ_B))`, where `κ_B` is the eigenvalue range of `∇²f(x0)^{-1}B0`;
  - the Jin–Mokhtari transient contains `Ψ(B̃0) + Ψ(B̄0)D0`, which is linear in that range.
- **Where we lose.**
  - In the gap variable (`D0 ≈ Δ` in self-concordant units), their transient is `O(D0³)` and dimension-free. Ours, `d(1+Δ)² + d²(1+Δ)`, carries polynomial factors of `d`, so it is worse when `d` is large compared with `Δ`.
  - They also prove a superlinear phase, which we do not.
  - We claim no uniform superiority on the overlap class.
- **The clean gains** are:
  - coverage of the standard self-concordant class, including barriers;
  - logarithmic rather than linear dependence on the initial mismatch.

## Limitations

- **No superlinear phase.** Composing with existing local superlinear analyses is not immediate, because the trace-type potentials can be exponentially larger than `Φ`.
- **Not a problem-class improvement.** Damped Newton uses `O(Δ + log log 1/ε)` Hessian evaluations. Cutting-plane methods need `Õ(d log)` gradient calls on bounded domains. The contribution is about the BFGS method itself.
- **Line-search work is not counted.** A bracketing search on barrier domains may need `O(Δ)` inner evaluations per iteration; we do not claim a bound for that.
- **Not tight.** The polynomial dependence on `d`, `Δ`, `1/c1` and `1/δ` is an upper bound, with no matching lower bound. The constants are loose.

## Scope

The task asked for second-order optimization. BFGS is a quasi-Newton method: it builds and uses a second-order model `B_t` of the Hessian. Quasi-Newton methods are the canonical second-order methods of Nocedal–Wright, Ch. 6. The theorem is about this exact method, and the setup enforces its update and output.
