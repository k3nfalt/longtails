# BFGS with arbitrary Armijo–Wolfe steps on linear-predictor objectives: a rate in the initial distance

Lean: theorem [`result`](LinearPredictorBFGS.lean), setup
[`LinearPredictorBFGS`](../Setups/LinearPredictorBFGS.lean) (problem class, line-search oracle, BFGS
update `bfgsUpdate`, direction `direction`, algorithm `bfgs`), algorithm instance
[`method`](../Algorithms/LinearPredictorBFGS.lean) (`bfgs L x0`), proofs
[`BFGSMatrix`](../Proofs/BFGSMatrix.lean), [`BFGSInequalities`](../Proofs/BFGSInequalities.lean),
[`BFGSRate`](../Proofs/BFGSRate.lean), [`BFGSComposite`](../Proofs/BFGSComposite.lean),
[`BFGSExecution`](../Proofs/BFGSExecution.lean), and the nonvacuity result
[`BFGSWolfe`](../Proofs/BFGSWolfe.lean). There, `wolfe_exists` proves that Armijo–weak-Wolfe steps
exist, and `admissible_exists` constructs an oracle meeting the setup's gradient and line-search
obligations.

## Setting

- **Objective.** f(x) = h(Ax) on ℝ^d. A : ℝ^d → ℝ^m is an arbitrary linear map: it may be
  rank-deficient or arbitrarily ill-conditioned, and d > m is allowed. h is convex with an
  L_h-Lipschitz gradient. A minimizer x⋆ with ‖x0 − x⋆‖ ≤ R exists.
- **Quadratic growth.** h has quadratic growth with constant μ on the image of the initial sublevel
  set: (μ/2)‖Ax − Ax⋆‖² ≤ f(x) − f(x⋆) whenever f(x) ≤ f(x0).
- **Smoothness bound.** L ≥ L_h‖A‖², so f is L-smooth. Write κ = L_h/μ ≥ 1 and γ = c1(1 − c2).
- **Examples.** The class contains least squares (κ = 1, rank-deficient designs allowed) and any
  smooth strongly convex loss composed with any design. It also contains logistic and other GLM
  losses on non-separable data, where h is strongly convex on the compact image sublevel set
  ([Karimi–Nutini–Schmidt, arXiv 1608.04636](https://arxiv.org/abs/1608.04636)). Overparameterized problems are included, where X⋆ is an affine set
  of dimension ≥ d − m. This is the prototype class f = h(Ax) of Necoara–Nesterov–Glineur
  ([arXiv 1504.06298](https://arxiv.org/abs/1504.06298), Math. Program. 2019).
- **Oracle.** A query (x, v) returns a pair (α, ∇f(x + αv)).
  - If ⟨∇f(x), v⟩ < 0, the step α > 0 may be *any* step satisfying the Armijo condition
    f(x + αv) ≤ f(x) + c1 α⟨∇f(x), v⟩ and the weak Wolfe condition ⟨∇f(x + αv), v⟩ ≥ c2⟨∇f(x), v⟩,
    with 0 < c1 < c2 < 1. The oracle is adversarial and may depend on the history.
  - Gradients are always exact.
  - Weak-Wolfe steps exist for every descent direction of a bounded-below C¹ function
    (Nocedal–Wright, Lemma 3.1). This is formalized in `BFGSWolfe.wolfe_exists`, and
    `BFGSWolfe.admissible_exists` builds an oracle satisfying the setup's obligations, so the class
    is nonvacuous.
- **Algorithm (`bfgs`).** Standard BFGS with B0 = L·I:
  - p_k = −B_k⁻¹ ∇f(x_k), and x_{k+1} = x_k + α_k p_k;
  - B_{k+1} = B_k − B_k s_k s_kᵀ B_k/⟨s_k, B_k s_k⟩ + y_k y_kᵀ/⟨y_k, s_k⟩, with s_k = x_{k+1} − x_k and
    y_k = ∇f(x_{k+1}) − ∇f(x_k).

  The setup's `allowedAlgorithm` restricts admissible methods to this BFGS recursion with B0 = cI for
  some c > 0. The output is the last iterate x_K. The method is a single, instance-independent
  algorithm that uses only x0 and L. It never uses c1, c2, μ, L_h, R or ε; these enter only the
  iteration budget.
- **Cost.** One initial query gives ∇f(x0), then one line-search-oracle call per iteration. The count
  is in BFGS iterations (line-search-oracle calls), not gradient evaluations inside the line search.

## Guarantee

The main proof (`main_bound`) shows, for every k ≥ 1:

  f(x_k) − f⋆ ≤ e·(L‖x0 − x⋆‖² + 2κ Σ_{i=1}^{k} (f(x_i) − f⋆)) / (γ k²).

Using f(x_i) − f⋆ ≤ LR²/2, this gives f(x_k) − f⋆ ≤ e(1 + κk)LR²/(γk²) ≤ e(κ + 1)LR²/(γk).

A three-stage bootstrap (`bootstrap`) turns it into

  f(x_k) − f⋆ ≤ 1200 κ³ L R² / (γ³ k²).

The budget `⌈35 · (κ/γ) · √(κ L R²/(γ ε))⌉₊ + 1` oracle calls therefore suffices for
f(x_K) − f⋆ ≤ ε. Written in setup parameters, it is
`⌈35 * (Lh / (μ * c1 * (1 - c2))) * √(Lh * L * R^2 / (μ * c1 * (1 - c2) * ε))⌉₊ + 1`.

## Mechanism

1. **Ding–Yang–Zhou chain.** Armijo + weak Wolfe gives 1/Δ_{i+1} − 1/Δ_i ≥ γ/(L T_i), with
   T_i = Δ_i² ⟨y_i, s_i⟩/(L⟨g_i, s_i⟩²). Since s_i ∥ B_i⁻¹g_i, we have T_i = Q_i ζ_i/L, where
   Q_i = Δ_i²/⟨g_i, B_i⁻¹g_i⟩ and ζ_i = ⟨y_i, s_i⟩/⟨s_i, B_i s_i⟩ = det B_{i+1}/det B_i.
2. **Determinant budget.** The trace grows by at most ‖y‖²/⟨y, s⟩ ≤ L per step, by cocoercivity.
   With log det ≤ trace − d this gives Π_{i<k} ζ_i ≤ e^k. Cauchy–Schwarz and AM-GM then give
   Δ_k ≤ e Σ_{i<k} Q_i/(γk²).
3. **The new step: a variable-metric distance identity.** For V_i = ⟨x_i − x⋆, B_i(x_i − x⋆)⟩, the
   BFGS update satisfies exactly

     V_{i+1} = V_i − ⟨g_i, x_i − x⋆⟩²/⟨g_i, B_i⁻¹g_i⟩ + ⟨y_i, x_{i+1} − x⋆⟩²/⟨y_i, s_i⟩.

   By convexity the subtracted term is at least Q_i. So Σ Q_i ≤ V_0 + Σ G_i, where V_0 = L‖x0 − x⋆‖²
   and G_i is the last term. The metric absorbs arbitrarily long flat steps: no bound on the iterates
   or on the sublevel set is needed.
4. **Composite structure (the only place the class is used).** Here y_i = Aᵀ(∇h(Ax_{i+1}) − ∇h(Ax_i)).
   Cocoercivity of ∇h and quadratic growth then give G_i ≤ L_h‖A(x_{i+1} − x⋆)‖² ≤ 2κΔ_{i+1}.

## Relation to prior work

- **Ding–Yang–Zhou, [arXiv 2608.16009v1](https://arxiv.org/abs/2608.16009)** (Thm 3.1; open
  questions in §4; unrefereed note, Aug 2026).
  - *What they prove.* For the same method (BFGS with any Armijo–Wolfe step, B0 = LI), on convex
    L-smooth f: Δ_k ≤ LW0²/(γk), where W0 = sup over the sublevel set of (f − f⋆)/‖∇f‖ ≤ R0 and R0
    is the sup over the sublevel set of dist(·, X⋆).
  - *Their open question.* Their §4, Question 2, asks for a rate depending only on dist(x0, X⋆).
    Question 1 asks whether f(x_k) → f⋆ at all without bounded level sets.
  - *In this class.* Here R0² can be as large as 2Δ0/(μ σ_min⁺(A)²) ≤ κ·cond(A)²·R², so their bound
    reads κ·cond(A)²·LR²/(γk). It is vacuous as σ_min⁺(A) → 0.
  - *This result.* It removes cond(A) entirely and answers both questions for linear-predictor
    objectives. Both questions remain **open for general convex L-smooth f**.
- **Global BFGS rates in the strongly convex / self-concordant setting.** Examples are:
  - Jin–Jiang–Mokhtari, [arXiv 2404.16731](https://arxiv.org/abs/2404.16731) (Armijo–Wolfe; NeurIPS
    2024);
  - Jin–Jiang–Mokhtari, [arXiv 2404.01267](https://arxiv.org/abs/2404.01267) (exact line search;
    Math. Program. 2025, as cited by Ding–Yang–Zhou);
  - Rodomanov–Nesterov, [arXiv 2003.09174](https://arxiv.org/abs/2003.09174) (Math. Program. 194,
    2022).
  - On this class their linear and superlinear rates depend on the restricted strong convexity
    μ σ_min⁺(A)², or on the trace–log-det potential of the transformed initial matrix.
  - They give nothing when A is singular. The present bound is a complementary sublinear guarantee
    that is uniform in the spectrum of A.
- **Optimal order.** BFGS iterates lie in x0 + span{∇f(x0), …, ∇f(x_{k−1})}, so Nesterov's lower
  bound Ω(LR²/k²) applies (Nesterov, *Lectures on Convex Optimization*, 2nd ed., Thm 2.1.7; convex
  quadratics, k ≲ d/2).
  - The O(1/k²) rate is therefore of optimal order in k. It is attained with any Armijo–Wolfe line
    search, no momentum, and no parameter knowledge beyond B0 = LI.
  - For comparison, gradient descent with Armijo steps is Θ(1/k) on this class (quadratics are
    included). For gradient descent with exact line search on general convex L-smooth functions,
    unpublished numerical performance-estimation computations (not a published theorem) suggest
    there is no rate in ‖x0 − x⋆‖ at all.
  - With *exact* line search, BFGS on quadratics coincides with conjugate gradients, so O(LR²/k²) is
    classical there. The new parts are arbitrary inexact Wolfe steps and non-quadratic h.

## Limitations and unresolved comparisons

- **Class restriction.** The class requires the composite structure f = h(Ax), with quadratic growth
  of h on the image sublevel set. General convex Q2 of Ding–Yang–Zhou remains open.
- **Constants.** They are poor:
  - 1/γ already appears in Ding–Yang–Zhou;
  - the accelerated O(1/k²) regime carries κ³/γ³, which is astronomically large for c1 = 10⁻⁴.
- **What is counted.** The guarantee counts BFGS iterations. The cost of finding a Wolfe step is
  delegated to the line-search oracle.
- **B0.** The analysis uses B0 = L·I with L ≥ L_h‖A‖². A general B0 = cI only changes constants
  (e^{L/c}), but this is not formalized.
- **Residual literature check.** The full texts of classical analyses of BFGS on convex quadratics
  could not be checked.
  - Powell, "How bad are the BFGS and DFP methods when the objective function is quadratic?"
    (Math. Program. 34, 1986, [doi:10.1007/BF01582161](https://doi.org/10.1007/BF01582161)). By its
    abstract, it studies unit steps on two-variable quadratics. It
    shows that BFGS may need more than ten iterations for one decimal place, which is consistent with
    the large constants above. It concerns unit steps, not arbitrary Wolfe steps.
  - Work by Dai and Yuan could not be checked either.

  No non-asymptotic O(1/k²) or initial-distance bound for arbitrary inexact Wolfe steps was found in
  the sources we could access. This comparison remains unresolved.
