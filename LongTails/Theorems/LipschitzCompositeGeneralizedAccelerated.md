# Radius-only acceleration for convex (L0,L1)-smooth plus Lipschitz composite objectives: Everest's transient without smoothing

This note explains the contribution formalized in
[`LipschitzCompositeGeneralizedAccelerated.lean`](LipschitzCompositeGeneralizedAccelerated.lean)
(`OracleTemplate.CompositeSherpa.result : Convergence spec budget`).

## Setup

The [setup](../Setups/LipschitzCompositeGeneralizedSmooth.lean) is the composite problem

    minimize  F(x) = f(x) + ψ(x)  over a real Hilbert space E,

with the following standard assumptions.

- `f : E → ℝ` is convex and differentiable with continuous gradient, and symmetric `(L0, L1)`-smooth in the segment form used
  throughout the repository: whenever `‖∇f‖ ≤ S` on the segment `[x, y]`, `‖∇f(x) − ∇f(y)‖ ≤ (L0 + L1 S)‖x − y‖`
  (`L0, L1 > 0`). For twice differentiable `f` this is the condition `‖∇²f(x)‖ ≤ L0 + L1‖∇f(x)‖` of Zhang, He, Sra and Jadbabaie
  ([ICLR 2020](https://openreview.net/forum?id=BJgnXpVYwS)), in the symmetric form of Everest Definition 2.1
  ([Rudomanov, Fomin, Gasnikov, Stonyakin, arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461)).
- `ψ : E → ℝ` is convex and `M`-Lipschitz (`M ≥ 0`): `|ψ(x) − ψ(y)| ≤ M‖x − y‖`. Typical instances: `λ‖·‖₁`, `λ‖·‖₂`, group
  norms, `λ‖·‖_*` on matrices, Huber-type penalties, maxima of finitely many affine functions.
- Some minimizer `x*` of `F` satisfies `‖x0 − x*‖ ≤ R`. **No bound on the initial gap `F(x0) − F*` is assumed**: on this class the
  gap can be as large as `(L0/L1²)(e^{L1R} − 1 − L1R)` (Everest Lemma A.2 applied to `f`).
- Oracle: `∇f(x)`; the exact proximal map `prox(a, z, g) = argmin_u ‖u − z‖²/(2a) + ⟨g, u − z⟩ + ψ(u)` (the repository's
  composite prox query, i.e. `prox_{aψ}(z − a g)`); and the value `ψ(x)`. Every call costs one unit; success is
  `F(x̂) − F* ≤ ε` for the returned point.
- **Information.** `Public = (E, x0, L0, L1, M)`. The radius `R` and the accuracy `ε` are fields of `Params` only, so the Lean types
  guarantee that the method never uses them; they appear only in the call budget. The method is anytime (its output is the current
  primal point). There is no constraint set, no `allowedAlgorithm`, and no function-value oracle for `f`.

Write `L0' = L0 + L1M`, `q = L1R` and `A = L0'R²/ε`.

## Algorithm

[`CompositeSherpa.algorithm`](../Algorithms/CompositeSherpa.lean) runs two phases.

**Phase 1 (composite SHERPA).** State `(A, x, v)`, initially `(0, x0, x0)`; at every iteration it queries `ψ(x)`, `∇f(v)` and
`ψ(v)`, and then searches the segment `z(t) = v + t(x − v)`, `t ∈ [0, 1]`, with `d = x − v`:

- *Exit rule.* At every gradient query at a point `z` (the point `v` or a midpoint), if `‖∇f(z)‖ ≤ G_thr := 5M + L0/L1`,
  Phase 1 ends with `z`.
- *Acceptance tests* (gradient of `f` and values of `ψ` only). A probe `t` with gradient `g_t = ∇f(z(t))`, `G_t = ‖g_t‖`, current left
  bracket end `t₋` and tolerance `τ(G) = G²/(200 L̂(G))`, `L̂(G) = L0 + 2L1M + L1G`, is accepted when
  (i) `(1 − t)⟨g_t, d⟩ + ψ(x) − ψ(z(t)) ≥ −τ(G_t)` and
  (ii) `t·[⟨g_t, d⟩ + (ψ(z(t)) − ψ(z(t₋)))/(t − t₋)] ≤ τ(G_t)`.
  Test (i) is a convexity surrogate for `F(z(t)) ≤ F(x) + τ`; test (ii) bounds the error of the dual step through the left
  ψ-secant. At `t = 0` only (i) is needed. If (i) fails the bracket moves right (`t₋ := t`), else if (ii) fails it moves left
  (`t₊ := t`); the midpoint is probed next. No depth is fixed in advance.
- *Update* at the accepted `y = z(t)`, `g = ∇f(y)`, `G = ‖g‖`: the prox-gradient step `x⁺ = prox(1/(4L̂(G)), y, g)`, the composite
  dual step `v⁺ = prox(a, v, g)`, `A⁺ = A + a`, where `a` is the positive root of

      a² = (A + a)/(12 L̂(G)) + a Φ'(G)/(2G²),     Φ'(G) = Φ_{L0', L1}(G − M),
      Φ_{L,L1}(s) = (L/L1²)[(1 + L1 s/L)log(1 + L1 s/L) − L1 s/L].

  This is Everest's weight rule (3.6) with the curvature `L̂` and the enlargement evaluated at the *shifted* gradient norm `G − M`.

**Phase 2.** The repository's composite backtracking accelerated method
([`BacktrackingComposite`](../Algorithms/BacktrackingComposite.lean), Nesterov's similar-triangles scheme with prox steps and the
gradient-only acceptance test; its analysis is the merged theorem
[`BacktrackingCompositeGeneralized`](BacktrackingCompositeGeneralized.lean)) started at the exit point with initial trial step
`1/L0'`. It is parameter-free; its current point is the output.

## Guarantee

For every valid instance, after

    budget = ⌈ 184 √((L0 + L1M) R²/ε) + 130000 (1 + L1R) log(2 + L1R) ⌉

oracle calls (gradients, proxes and ψ-values together) the returned point satisfies `F(x̂) − F* ≤ ε` (`theorem result`). In order
notation,

    O( √((L0 + L1M) R²/ε) + (1 + L1R) · log(2 + L1R) ),

with every call counted: the three calls opening a Phase-1 iteration, two calls per bisection probe including the probe that exits,
the two proxes of every accepted iteration, and the three calls of every Phase-2 trial, accepted or rejected. The constants are not
optimized.

## Contribution

**What is proved.** The first radius-only (gap-free) accelerated guarantee for convex `(L0,L1)`-smooth `f` plus Lipschitz convex `ψ`
with Everest's near-optimal transient `(1 + L1R) log(2 + L1R)` and **no smoothing term**: the complexity has exactly the structure
of Everest's smooth bound (their Theorem 3.7, `5√(L0R²/ε) + 240(1 + L1R)log2(64(1 + L1R)) + 2`), with `L0` replaced by
`L0 + L1M` in the leading term, and it is attained by a method that receives only `L0, L1, M, x0`.

Unlike Everest's SHERPA, Phase 1 uses neither `R` (no fixed bisection depth, no iteration cap, no `R`-based exit test) nor `ε`;
both are analysis-only, as in the repository's smooth R-free theorem.

**Comparison with the closest results** (same oracle model unless stated; all for the class above, `ψ ≠ 0`).

| method | needs | calls |
|---|---|---|
| Moreau smoothing of ψ with parameter `μ = ε/M²` + Everest SHERPA/CRUISE (Thm 3.7) on `f + ψ_μ + (ε/(4R²))‖· − x0‖²` (the quadratic term keeps a minimizer of the surrogate within `R` of `x0`, as Everest's radius hypothesis requires, and costs `ε/4`; the surrogate is `(L0 + L1M + M²/ε + ε/(2R²), L1)`-smooth and its gradient is one prox + one gradient) | `L0, L1, M, R, ε` | `√(L0'R²/ε) + MR/ε + (1 + q)log(2 + q)` |
| merged [`CompositeGeneralizedAccelerated`](CompositeGeneralizedAccelerated.md) (Nesterov–Nemirovski-type weight from the gradient at `x_k`, displacement cap) | `L0, L1, R, Δ ≥ F(x0) − F*`, analysis-only `G ≥ ‖∇f(x*)‖` | `3⌈10√((L0 + L1G)R²/ε) + (6 + 128q)log(2 + (3 + 96q)√(Δ/(L0R²)))⌉`; on the radius-only class `Δ` is up to `(L0/L1²)e^{q} + MR`, i.e. a `q²` transient |
| sister session's open [PR #155](https://github.com/k3nfalt/longtails/pull/155) `RadiusCompositeAccelerated` (unmerged, opened 12 Nov 2026; allows a constraint set through a joint prox, analysis-only `G`) | `L0, L1, R, ε` | `⌈32768((1 + q)^{4/3} + √τ)log²(128(1 + q + τ))⌉`, `τ = (L0 + L1G)R²/ε` |
| Tyurin, Thm 4.3 ([arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884), ICML 2026) | unconstrained, smooth `ψ = 0` only; `Γ0 ≥ 2Δ/R²` | `√(L0R²/ε) + L1R log(min{L1²R²Γ0/L0, Γ0R²/ε})`, `q²` on the radius-only class |
| Deng–Gao, Alg. 3, Thm 6.1 ([arXiv:2512.09720v3](https://arxiv.org/abs/2512.09720)) | composite, local smoothness, function values of `F` | curvature constant is the maximal local Lipschitz constant on an invariant ball, exponential in `q` under `(L0,L1)`-smoothness |
| **this theorem** | `L0, L1, M` | `184√(L0'R²/ε) + 130000(1 + q)log(2 + q)` |

- Against smoothing the gain is the removal of `MR/ε`: the new bound is better exactly when `MR/ε ≳ √(L0'R²/ε)`, i.e.
  `ε ≲ M²/(L0 + L1M)`, and the two are of the same order otherwise. This is the standard proximal-versus-smoothing gain (as for FISTA
  versus smoothing in the `L`-smooth case), now obtained on the `(L0,L1)` class without losing the single-log transient.
- Against the merged theorem the gain is the removal of `Δ` (polynomial: `q log q` instead of `q²` on the radius-only class) at the
  price of `M` in place of `G = ‖∇f(x*)‖ ≤ M` in the leading term.
- Against PR #155 (which is not merged and whose note states that "a near-linear composite transient remains unresolved by this
  proof") the transient improves from `(1 + q)^{4/3}log²` to `(1 + q)log` and the `log²` factor on `√τ` disappears, on the
  subclass of Lipschitz `ψ` without constraints, with `M` public and ψ-values available. This is a tradeoff, not a dominance.
- Everest's lower bound (their Thm 4.10) applies to the subclass `ψ ≡ 0`: every deterministic first-order method needs
  `Ω(√(L0R²/ε) + L1R/√log(2 + L1R))` calls, so the transient is optimal up to logarithms. The leading term `√(L0'R²/ε)` matches that
  bound only up to the factor `√(1 + L1M/L0)`; whether `√((L0 + L1‖∇f(x*)‖)R²/ε)` is attainable on this class is open (Phase 2 is
  adaptive and its analysis holds with `G = ‖∇f(x*)‖` in place of `M`, but then the logarithm contains `(L0 + L1M)/(L0 + L1G)`; the
  theorem is stated with `M` to keep a single clean logarithm).

**Technical mechanism** (the proofs are in `LongTails/Proofs/CompositeSherpa*.lean`).

1. *Shifted smooth function (analysis only).* `ξ* = −∇f(x*)` is a subgradient of `ψ` at `x*` with `‖ξ*‖ ≤ M`, and
   `h = f − ⟨∇f(x*), ·⟩` is convex, `(L0 + L1M, L1)`-smooth in the segment form, with `∇h(x*) = 0` and `G − M ≤ ‖∇h(y)‖ ≤ G + M`.
   Everest's Lemma 3.2 for `h` gives `f(x*) ≥ f(y) + ⟨∇f(y), x* − y⟩ + Φ_{L0',L1}(‖∇f(y)‖ − M)` — the shift cancels, so the
   enlargement is observable (`Hyp.phi_inequality`). This is not a reduction of the problem: `ξ*` is unknown and the method takes prox
   steps.
2. *Prox-gradient step with the local step `1/(4L̂)`.* Movement `λ(G − M) ≤ ‖x⁺ − y‖ ≤ λ(G + M) < 1/(4L1)`, descent
   `F(x⁺) ≤ F(y) − 3L̂‖x⁺ − y‖²`, and `‖x⁺ − x*‖ ≤ ‖y − x*‖` through firm nonexpansiveness of the prox and the cocoercivity of `h`
   (`Hyp.step_descent`, `Hyp.step_dist`). All iterates and probes stay in `B(x*, R)` (a fact of the analysis, not of the algorithm).
3. *Composite potential.* `A(F(x) − F*) + ½Σ a_i²‖∇f(y_i)‖² + ½‖v − x*‖² ≤ R²/2` is nonincreasing (`accepted_potential`). The
   composite dual step pays the Young term `½a²(G + M)² ≤ 0.72a²G²` (every accepted `G > 5M`), and the error of the dual step is
   bounded through the left ψ-secant: convexity gives `ψ(v⁺) − ψ(y) ≥ [ψ(z(t₋)) − ψ(y)]·t/(t − t₋) − M‖v⁺ − v‖`, which is exactly
   what test (ii) controls. The tolerances `τ` and the Young term are absorbed by the descent term and the weight rule.
4. *Line search without function values of `f`.* The bracket invariants are: (i) fails at `t₋` and (ii) fails at `t₊` with the current
   `t₋` (preserved when `t₋` moves because ψ-secants with a fixed right endpoint are nondecreasing in the left endpoint). Comparing
   `U(t₋, t₊) = ⟨g_{t₊}, d⟩ + sec_ψ(t₋, t₊)` with `Λ(t₋) = ⟨g_{t₋}, d⟩ + sec_ψ(t₋, 1)` through the gradient closeness bound forces the
   bracket width above `1/(2304(1 + L1‖x − v‖)²)` (`probe_width`), hence at most `⌈log2(2304(1 + 2q)²)⌉` probes per iteration,
   with no dependence on `M`, `1 − t₊`, `R` or `ε` inside the depth.
5. *Count of Phase-1 iterations.* Everest's Lemma 3.5 for the shifted function: `J/I` split on `L1 a_i‖∇f(y_i)‖` with the
   curvature `L̂ = L0' + L1(G + M)` and the enlargement `Φ'`; the weight before every iteration satisfies `L0'A ≤ 12q²` because the
   prox-gradient descent certifies `F(x) − F* ≥ L0'/(24L1²)` while the gradient exceeds `G_thr` (`gap_lower_x`,
   `iteration_increment`, `omega_bound`): at most `1300(1 + q)` iterations.
6. *Exit certificate and Phase 2.* At the exit point `z ∈ [v, x] ⊂ B(x*, R)` with `‖∇f(z)‖ ≤ 5M + L0/L1`,
   `F(z) − F* ≤ (‖∇f(z)‖ + M)R ≤ 6L0'R/L1`. The merged composite backtracking analysis started from `(z, Δ = 6L0'R/L1, h0 = 1/L0')`
   with `G = M` has every logarithm equal to `log(poly(1 + q))`, so Phase 2 costs `183√A + O((1 + q)log(2 + q))` calls
   (`phase2_bound_le`). No second-stage constant-step method and no sublevel-set argument are needed.

## What is already known, and limitations

- Everest's smooth result (both stages) and the repository's R-free smooth variant
  ([`RadiusFreeGeneralizedAccelerated`](RadiusFreeGeneralizedAccelerated.md)) are the `ψ ≡ 0`, `M = 0` case of the present
  theorem up to constants (then `G_thr = L0/L1`, `L̂ = L0 + L1G`, `Φ' = Φ`, the prox is the identity).
- The result is a composite extension of a known near-optimal guarantee, not a new rate for an established class; its value is the
  removal of the smoothing term `MR/ε` and of the gap `Δ` on the Lipschitz-composite `(L0,L1)` class with the single-log transient.
- The leading constant uses the public Lipschitz bound `M`, not the intrinsic `‖∇f(x*)‖ ≤ M`. For `ψ = λ‖·‖₁` on `ℝ^d` one has
  `M = λ√d`, so the leading term carries `√(L1λ√d)`-type dimension dependence that an `‖∇f(x*)‖`-based bound (`λ√(support size)`)
  would not; the Phase-1 steps use `M` and we did not remove it.
- The oracle includes values of `ψ` (cheap for the usual regularizers; not needed by the smooth method). No constraint set is covered
  (the prox is over `E`); the constrained case with `∇f(x*) ≠ 0` needs a different enlargement and is left open.
- Constants are large (as in the repository's smooth theorem) and not optimized.
