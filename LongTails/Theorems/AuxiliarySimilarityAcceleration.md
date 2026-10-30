# Accelerated nonconvex optimization with a Hessian-similar auxiliary function

Lean theorem: [`AuxiliarySimilarityAcceleration.lean`](AuxiliarySimilarityAcceleration.lean) (`result`).
Setup: [`Setups/AuxiliarySimilarityNonconvex.lean`](../Setups/AuxiliarySimilarityNonconvex.lean).
Algorithm: [`Algorithms/AuxiliarySimilarity.lean`](../Algorithms/AuxiliarySimilarity.lean) (`method`, `tuning`), run through
the two-oracle plan in [`Algorithms/AuxiliaryPlan.lean`](../Algorithms/AuxiliaryPlan.lean).

## Problem and oracle model

The setup works on a finite-dimensional Euclidean space `E` and uses two functions, `f, h : E → ℝ`.

- **Target `f`.** It is `C²` and its Hessian is `ρ`-Lipschitz: `‖∇²f(x) − ∇²f(y)‖ ≤ ρ‖x − y‖`.
- **Auxiliary `h`.** It is differentiable and `∇h` is `L`-Lipschitz. It may be arbitrarily nonconvex.
- **Hessian similarity.** `∇(f − h)` is `δ`-Lipschitz. For `C²` functions this is `‖∇²f − ∇²h‖ ≤ δ`.
- **Initial gap.** `f(x₀) − f(x) ≤ Δ` for every `x`.

There are two oracles, and the theorem bounds the number of calls to each one separately.

- **Expensive oracle `O_f`** (oracle index 0) returns `(f(x), ∇f(x))`.
- **Cheap oracle `O_h`** (oracle index 1) returns `(h(x), ∇h(x))`.

The algorithm may use the public parameters `x₀, L, δ, ρ, Δ, ε`. The accuracy criterion is deterministic: the output
`x̂` satisfies `‖∇f(x̂)‖ ≤ ε` (stated as an almost-sure statement under the trivial seed law).

The assumptions are standard ones.

- **Similarity (S).** This is the condition used for DANE (Shamir–Srebro–Zhang, ICML 2014) and for optimal gradient
  sliding (Kovalev et al., NeurIPS 2022). It is also the "auxiliary information" or helper assumption of Chayti–Karimireddy
  (TMLR 2024, arXiv:2206.00395) and Chayti–Doikov–Jaggi (TMLR 2024, arXiv:2302.11962, Assumption 3.1).
- **Hessian-Lipschitz `f`.** This is the standard assumption behind the `ε^{-7/4}` first-order rate (Carmon–Duchi–Hinder–
  Sidford, ICML 2017; Li–Lin, ICML 2022).
- **Smooth `h`.** Only that `∇h` is Lipschitz.

The intended use is any setting where `∇f` is costly but a structurally similar surrogate `h` is cheap. Examples are the
server-side subsample loss in federated or distributed learning (an `O_f` call is a communication round) and a smaller
proxy or auxiliary task. A typical instance: `f` is the empirical risk of a smooth nonconvex model (all coordinates
interacting), `h` is the same risk on a subsample, and `δ` is their statistical Hessian discrepancy. In this instance `L`
can be much larger than `δ`.

## Result

Write `s = √(ρε)` and `Q = 1 + (L + δ)/s`. The algorithm returns `x̂` with `‖∇f(x̂)‖ ≤ ε` using at most

- **Expensive calls (`O_f`):** `K·((T + 1)(J + 2) + 6)`.
- **Cheap calls (`O_h`):** `K·(T + 1)·((J + 1)(N + 3) + 1)`.

The counts are defined as follows:

- `K = ⌈2¹⁹ Δ s / ε²⌉ + 1` (epochs);
- `T = ⌈6 √(1 + δ/s) · log(8 + 8δ/s)⌉` (accelerated proximal steps per epoch);
- `J = ⌈15 log(400 Q)⌉` (DANE steps per proximal step);
- `N = ⌈(L/δ + 6) · log(2¹¹⁰ Q¹⁰ (1 + Δ s/ε²))⌉`. The algorithm's tuning uses `N + 2` gradient steps per DANE
  step, and with its initial cheap call each DANE step makes `N + 3` cheap calls.

The `budget` in the Lean file is exactly these two lines, written out in the setup parameters. In order notation:

`#O_f = O( (√ρ Δ ε^{-3/2} + √δ ρ^{1/4} Δ ε^{-7/4}) · log(2 + δ/√(ρε)) · log(2 + (L + δ)/√(ρε)) )`,

`#O_h = #O_f · O((L/δ + 1) · log(Q (1 + Δ√ρ ε^{-3/2})))`.

The expensive count does not depend on `L` except through one logarithm.

## Comparison with the closest known results (expensive-oracle calls)

- **Chayti–Doikov–Jaggi, arXiv:2302.11962v7, Theorem 3.3.**
  - Rate: `O(Δ(√ρ ε^{-3/2} + δ ε^{-2}))`.
  - This is a helper cubic Newton method that uses Hessian-vector products of `h`. Here these can only be emulated by
    finite differences of cheap gradients, so we do not claim that their method has an oracle advantage or disadvantage.
  - Their guarantee is stated for a randomly chosen output iterate. It is deterministic when the helpers are exact.
  - Our `√δ ρ^{1/4} Δ ε^{-7/4}` is the geometric mean of their two terms, so it is never larger than their bound up to
    constants and the two logarithms.
  - When `δ ≫ √(ρε)` it is smaller by the factor `√(δ/√(ρε))`. The theorem improves on this baseline once that factor
    exceeds our explicit `log·log` factor and constants.
- **Chayti–Karimireddy, arXiv:2206.00395 (first-order auxiliary information).** Rate `O(δ Δ ε^{-2})`. It is improved in the
  same regime.
- **Methods that ignore `h`** (Carmon–Duchi–Hinder–Sidford 2017; Li–Lin, restarted AGD).
  - Rate: `O(√(L + δ) ρ^{1/4} Δ ε^{-7/4})` (up to their logs), since the smoothness of `f` is up to `L + δ`.
  - We replace `√(L + δ)` by `√δ` in the expensive count.
- **Gradient sliding and similarity-accelerated methods** (Kovalev et al. 2022 and related work). These need convexity
  (of the sum, or of the parts used in the prox steps) and give no `ε^{-7/4}` nonconvex stationarity guarantee. They do not
  apply when `h` is nonconvex.
- **Lower bound.**
  - Taking `h ≡ 0` (so `L = 0`) gives a first-order nonconvex problem with `δ`-Lipschitz gradient and `ρ`-Lipschitz
    Hessian.
  - Every first-order method needs `Ω(√δ ρ^{1/4} Δ ε^{-7/4})` gradient calls on this class.
    - The deterministic statement is arXiv:2606.05438v2. The randomized statement is arXiv:2610.00245v2.
    - Both hold in high dimension when `ε ≲ δ²/ρ` and `Δ√ρ ε^{-3/2} ≳ 1`.
  - In the regime `δ ≳ √(ρε)` our expensive count is therefore optimal up to the two logarithmic factors and absolute
    constants.

We do not know of a published guarantee with expensive count `o(min{δ ε^{-2}, √L ε^{-7/4}})·Δ` under (S) with nonconvex
`h`. This statement is based on a search (as of 2026-10-29) of ICML, ICLR and NeurIPS 2024–2025 and of arXiv from
2024–2026. It covered similarity, gradient sliding, auxiliary-information and helper methods, and nonconvex
`ε^{-7/4}` methods, and followed the citations of the papers above.

## Algorithm and proof mechanism

The method has three nested levels, each protected by after-the-fact guards in the style of "convex until proven
guilty" (CDHS 2017).

1. **Epochs.** Fix an anchor `y` and minimize `g(x) = f(x) + α‖x − y‖²` with `α = √(ρε)/8`. Use an accelerated inexact
   proximal-point method with prox parameter `2δ̄`, where `δ̄ = max(δ, α)`. It has momentum `a = √(α/(4δ̄))` and runs
   `T ≈ √(δ̄/α)` steps.
2. **Prox subproblems.** Each prox subproblem `T_v(x) = g(x) + δ̄‖x − v‖²` is solved by DANE. Here DANE is a
   relative-smoothness gradient method (Lu–Freund–Nesterov 2018) with reference `ψ = h + α‖·−y‖² + δ̄‖·−v‖² + δ̄‖·‖²`.
   It uses one `O_f` call per step. `D_{T_v} ≤ D_ψ` always holds, by (S) alone.
3. **DANE subproblems.** Each DANE subproblem is minimized by plain gradient descent using only `O_h`.

Every guard compares a Bregman difference with a quadratic, and every failure yields a negative-curvature certificate of
`f`: `D_f(u, w) < −(α/2)‖u − w‖²`. This transfer uses only (S); `h` is never assumed convex. There are three transfers:

- **Prox step.** A failed strong-convexity guard of `g` gives the certificate directly.
- **DANE step.** A failed relative-strong-convexity guard `D_T ≥ (2/5) D_ψ` gives it.
- **Gradient-descent step.** A failed guard `D_ψ ≥ (3δ̄/2)‖·‖²` gives it.

The epoch keeps the first certificate in execution order. Each epoch either finds a point with `‖∇f‖ ≤ ε` or decreases
`f` by `ατ² = ε^{3/2}/(2¹⁹√ρ)`, where `τ = α/(32ρ)`. The proof of this dichotomy goes as follows.

- **Clean prefix.** If the first certificate arises at step `t`, all guards before step `t` held. The accelerated
  potential (with additive inexactness errors) then bounds the iterates at step `t`.
- **Localization.** Monotonicity of DANE and gradient descent, together with the lower bound on `f` at the evaluated
  endpoints, places the certificate in the ball `B(y, 3τ)`.
- **Exploit step.** The Hessian-Lipschitz property moves the curvature to the anchor, and two expensive calls at
  `y ± (α/(8ρ)) d` decrease `f` by `α³/(512ρ²)`.
- **No certificate.** If no certificate arises, the final prox point `x'` has `‖∇g(x')‖ ≤ ε/2`. Hence either
  `‖∇f(x')‖ ≤ ε` (which the method checks with one call) or `f(x') ≤ f(y) − ατ²`.

The new ingredient compared with CDHS-style methods is the two inner guarded levels. They let the expensive oracle pay
only for the similarity constant `δ` while `h` stays nonconvex; the black-box similarity solvers that would otherwise
do this require convexity.

## Formalization notes

- **Execution.**
  - The method is a two-oracle query plan (`TwoPlan`).
  - `execute_eq_eval` shows that the template's `execute` returns the plan's value whenever the per-oracle budgets
    dominate the calls along the evaluation path.
  - `calls_bound` bounds the calls of the whole method by the two budget lines. Every guard check, exploit call, restart
    and stationarity check is counted.
- **Analysis.** The modules `AuxiliaryInner`, `AuxiliaryDaneRun`, `AuxiliaryAppa` and `AuxiliaryEpoch` contain the
  gradient-descent rate, the DANE rate, the inexact accelerated potential, the certificate transfers, the localization
  invariant and the epoch dichotomy.
- **Tuning.** `AuxiliaryTuning` derives every analysis requirement from the explicit formulas for `K, T, J, N`.

## Limitations

- **Logarithmic factors.** The expensive bound carries two of them, `log(2 + δ/√(ρε))` and `log(2 + (L+δ)/√(ρε))`, and
  large absolute constants (for example `2¹⁹` in `K`). The improvement over Chayti–Doikov–Jaggi is therefore a
  `√(δ/√(ρε))` factor beyond these logs and constants. The method is not log-free; Li–Lin's method is log-free but pays
  `√(L+δ)`.
- **Asymptotic improvement only.** The absolute constants are large (`2¹⁹` epochs per unit of `Δ√ρ ε^{-3/2}`, and
  logarithms with large constants). The gain over Chayti–Doikov–Jaggi therefore appears only asymptotically, when
  `√(δ/√(ρε))` is large.
- **Cheap count.** It scales like `L/δ` because the innermost solver is plain gradient descent. An accelerated inner
  solver would give `√(L/δ)`, but this is not formalized. Cheap calls are only claimed to be polynomial.
- **Deterministic oracles only.** There is no stochastic or high-probability version.
- **Worst-case design.** On benign random instances, plain DANE needed far fewer expensive calls than the guarded method in
  the Researcher's prototype experiments. The theorem is a worst-case guarantee.
- **Lower-bound comparison.** It uses the special case `h ≡ 0` and inherits the dimension and accuracy regimes of
  arXiv:2606.05438v2 and arXiv:2610.00245v2.
- **Unchecked sources.** Some recent related work could be checked only from its abstract (for example TIGER,
  arXiv:2610.25504v1).
