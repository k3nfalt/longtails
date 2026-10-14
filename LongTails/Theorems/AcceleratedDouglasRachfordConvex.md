# Fast Douglas–Rachford splitting at rate O(1/N²) without the quadratic assumption

This note explains the contribution formalized in
[AcceleratedDouglasRachfordConvex.lean](AcceleratedDouglasRachfordConvex.lean), with
[setup](../Setups/DouglasRachfordSmoothConvex.lean),
[algorithm](../Algorithms/AcceleratedDouglasRachford.lean) and proofs
([envelope inequalities](../Proofs/DouglasRachfordEnvelope.lean),
[potential](../Proofs/AcceleratedDouglasRachfordPotential.lean),
[execution](../Proofs/AcceleratedDouglasRachfordExecution.lean)).

**Summary.** Consider min f + g with f convex and L-smooth, g closed convex, and access to prox_{γf} and
prox_{γg} at one fixed parameter γ. The fast Douglas–Rachford splitting of Patrinos, Stella and Bemporad
[PSB14, iteration (34a)–(34d)], i.e. Douglas–Rachford with Nesterov momentum on the governing sequence, was
proved to converge at rate O(1/N²) only when f is convex **quadratic** [PSB14, Thm 5]; the same limitation is
recorded in [PZ25, p. 15] ("their analyses establish an accelerated convergence rate of O(1/N²) only in the
quadratic setting") and, in continuous time, in [OJ25] (accelerated rate for Douglas–Rachford dynamics for the
sum of a quadratic and a nonsmooth term). We prove, for **every** convex L-smooth f, every constant relaxation λ ∈ (0, 1] and every
γ with 4γL ≤ λ,

  F(y_N) − F* ≤ 2‖w₁ − w*‖² / (λγN²),  F = f + g,

for the same iteration with the same momentum coefficients, where y_N is the N-th prox_{γg} output and w* is a
fixed point of the Douglas–Rachford operator. Hence 2⌈√(2R²/(λγε))⌉ prox evaluations give F(y_N) − F* ≤ ε
when ‖w₁ − w*‖ ≤ R. The result is about this iteration. It is **not** an improvement of the oracle complexity
of the problem class: with a gradient oracle for f, FISTA has the bound 2L‖x₀ − x*‖²/(N+1)², and methods with
varying prox parameters reach O(1/N²) with the two prox oracles (see "Relation to prior results"). The
stepsize range γ ≤ 1/L and the exact constant conjectured in [PZ25, Conjecture 4] remain open.

## Setup and proved guarantee

- **Space.** E is a real Hilbert space of any dimension.
- **Objective.** f : E → ℝ is differentiable with, for all x, y,

    0 ≤ f(y) − f(x) − ⟨∇f(x), y − x⟩ ≤ (L/2)‖y − x‖²,

  i.e. f is convex with L-Lipschitz gradient. g is a convex function on a convex set C ⊆ E (the domain of an
  extended-valued g; indicator functions, norms and their sums are included). F = f + g has a minimizer x*
  on C. No strong convexity, no growth condition, no bounded domain; f is not assumed quadratic or twice
  differentiable. Example with interacting coordinates: f(x) = Σᵢ log(1 + exp(aᵢᵀx − bᵢ)), g = μ‖x‖₁ + indicator
  of a box.
- **Oracle.** Two queries, both at the same public γ > 0: `proxF w` returns the minimizer of
  f(x) + ‖x − w‖²/(2γ) over E, `proxG v` returns a point of C minimizing g(y) + ‖y − v‖²/(2γ) over C. The setup
  states these as `IsMinOn` conditions on the oracle's replies; existence of the minimizers is part of
  admissibility. The algorithm never evaluates ∇f; the proof uses that ∇f(prox_{γf}(w)) = (w − prox_{γf}(w))/γ,
  which is derived from the minimality condition.
- **Distance.** R ≥ ‖w₁ − w*‖ with w* = x* + γ∇f(x*). This is the distance of the governing sequence to a
  fixed point of the Douglas–Rachford operator, the quantity used in [PSB14] and [PZ25]. It is not the
  distance ‖x₀ − x*‖ of proximal-gradient methods: it contains γ‖∇f(x*)‖.
- **Cost and success.** Cost = number of prox evaluations (two per iteration, both counted). Success means
  y_N ∈ C and F(y_N) − F(x*) ≤ ε, for the last iterate.
- **Information.** The algorithm receives γ, λ and w₁. It does not use L, R, ε; these enter only the validity
  condition and the budget.
- **Validity.** L > 0, γ > 0, 0 < λ ≤ 1, 4γL ≤ λ, R > 0, ε > 0.

**Algorithm** (fast DRS, [PSB14, (34a)–(34d)] with constant relaxation). Set u₁ = w₁ and for i = 1, 2, …

  x_i = prox_{γf}(w_i),
  y_i = prox_{γg}(2x_i − w_i),
  u_{i+1} = w_i + λ(y_i − x_i),
  w_{i+1} = u_{i+1} + β_i (u_{i+1} − u_i),  β₁ = 0, β_i = (i−2)/(i+1) for i ≥ 2.

In the indexing of [PSB14] (k = i − 1 ≥ 0) this is β₀ = 0, β_k = (k−1)/(k+2). The output after N iterations
is y_N.

**Guarantee** (Lean: `result`, via `execute_accuracy`). Under the validity conditions, for every N ≥ 1,

  F(y_N) − F* ≤ 2‖w₁ − w*‖²/(λγN²),

and the budget `2 * ⌈√(2R²/(λγε))⌉₊` prox calls suffices for F(y_N) − F* ≤ ε. At λ = 1, γ = 1/(4L) the bound
is 8L‖w₁ − w*‖²/N².

## Mechanism

Write ∇_i = ∇f(x_i) = (w_i − x_i)/γ, G_i = (x_i − y_i)/γ (the fixed-point residual divided by γ) and

  Q_i = f(x_i) + g(y_i) + ⟨∇_i, y_i − x_i⟩ + ‖y_i − x_i‖²/(2γ) ≥ F(y_i) + (γ/2)(1 − γL)‖G_i‖².

Q_i is the value of the Douglas–Rachford envelope at w_i. For quadratic f the envelope is convex and smooth
in a scaled metric and [PSB14] apply Nesterov's method to it. For general f the envelope is not convex and
G_i is not its gradient. The proof replaces convexity of the envelope by an inequality that holds for any two
Douglas–Rachford points a, b (lemma `env_ineq`):

  Q_a ≥ Q_b + ⟨G_b, w_a − w_b⟩ + (γ/2)‖G_a − G_b‖² − (Lγ²/2)‖G_a + G_b‖².

It follows from two interpolation inequalities (cocoercive lower bound for f between x_a and x_b, subgradient
inequality for g between y_a and y_b); the difference of the two sides, minus the two slacks, equals
‖∇_b − ∇_a + Lγ(G_a + G_b)‖²/(2L) (lemma `env_identity`). The last term is the price of non-quadratic f. Taking
b = iteration i and a = iteration i − 1 or a = the fixed point gives

  (A) Q_i − Q_{i−1} ≤ ⟨G_i, w_i − u_i⟩ − (γ/2)(λ − 2γL)(‖G_{i−1}‖² + ‖G_i‖²),
  (B) Q_i − F* ≤ ⟨G_i, w_i − w*⟩ − (γ/2)(1 − γL)‖G_i‖².

(A) provides less than the −(λγ/2)‖G_i‖² that a FISTA-type potential consumes, but it also provides a negative
multiple of the *previous* residual. With t₁ = 1, t_i = i/2 (i ≥ 2), v_{i+1} = t_i u_{i+1} − (t_i − 1)u_i,
a = (γ/2)(λ − 2γL), b = (γ/2)(1 − γL), c_i = t_{i+1}(t_{i+1} − 1), the potential

  Φ_i = t_i²(Q_i − F*) + ‖v_{i+1} − w*‖²/(2λγ) − (c_i a + (t_i² − c_i) b)‖G_i‖²

subtracts in advance the bonus that step i + 1 will return. It satisfies Φ₁ ≤ ‖w₁ − w*‖²/(2λγ),
Φ_{i+1} ≤ Φ_i (lemmas `first_step`, `potential_step`, `good_step`; this is where 4γL ≤ λ is used) and
t_N²(F(y_N) − F*) ≤ Φ_N (lemma `good_final`).

## Relation to prior results

N denotes the number of iterations (prox pairs); R_w = ‖w₁ − w*‖.

| Source | Method, oracle | Assumption on f | Guarantee |
|---|---|---|---|
| [PSB14, Thm 5] | fast DRS (34), fixed γ < 1/L, λ = (1−γL)/(1+γL) | convex **quadratic** | F(z^k) − F* ≤ 2R_w²/(γλ(k+2)²); z^k is produced by iteration N = k+1, so 2R_w²/(γλ(N+1)²); best constant 2/(γλ) = 11.66 L at γ = (√2−1)/L |
| **this note** | the same iteration, fixed γ ≤ λ/(4L), any constant λ ∈ (0,1] | convex L-smooth | F(y_N) − F* ≤ 2R_w²/(λγN²); best constant 8L at λ = 1, γ = 1/(4L) |
| [PZ25, Conjecture 4] | DRS with momentum k/(k+3), γ ≤ 1/L, λ ∈ (0,1] | convex L-smooth | conjectured 2R_w²/(γ((N²+7N−8)λ+8)); no proof |
| [PZ25], [DY16, DY17] | DRS without momentum | convex L-smooth | O(1/N)-type objective rates |
| [Kim21] | accelerated proximal point applied to the DR operator, fixed γ | none | squared fixed-point residual O(1/N²); no O(1/N²) objective rate |
| FISTA [BT09] | gradient of f, prox of g | convex L-smooth | 2L‖x₀ − x*‖²/(N+1)² |
| accelerated primal–dual / ADMM [CP11, CP16, Xu17, TZ18, ST22] | the two prox oracles with **varying** parameters | one term strongly convex (dual of smooth) | O(1/N²) for ergodic gaps, feasibility or non-ergodic primal rates, depending on the paper |

Precise comparison with [PSB14, Thm 5]. The function class is enlarged from convex quadratics to all convex
L-smooth functions. The admissible parameters are different: [PSB14] allow γ < 1/L with the relaxation rule
λ(γ) = (1−γL)/(1+γL); we allow any constant λ ∈ (0,1] with γ ≤ λ/(4L). The rule λ(γ) is covered for
γL ≤ (√41 − 5)/8 ≈ 0.175; the choice γ = (√2−1)/L, optimal in [PSB14], is not covered. So the theorem is not a
strict generalization of Theorem 5. In terms of best tuned constants, 8L/N² is smaller than
11.66L/(N+1)² for N ≥ 5 and larger for N ≤ 4.

What is not claimed. (i) No improvement of the complexity of the problem class: FISTA uses a cheaper oracle
and has a smaller constant, and the varying-parameter methods in the last row already reach O(1/N²) with the
two prox oracles. (ii) The theorem does not prove Conjecture 4 of [PZ25]. The same argument applied to the
momentum k/(k+3) of [PZ25, Algorithm 3] (t_i = (i+2)/2; the first step then costs a factor 1 + λ) gives
F(y_N) − F* ≤ 2(1+λ)R_w²/(λγ(N+1)(N+3)) for 4γL ≤ λ, i.e. the conjectured order and the conjectured scaling
1/(γλN²) on a quarter of the conjectured stepsize range; this variant is a paper computation, checked
numerically, and is **not** formalized. Our PEP computations reproduce the conjectured value to six digits
for N ≤ 10. (iii) ADMM. Douglas–Rachford splitting applied to the dual of min H(u) + G(v) s.t. Au + Bv = b is
ADMM, and f is then L-smooth when H is strongly convex. Read through this correspondence, the theorem is a
statement about momentum ADMM with fixed penalty when only one block is strongly convex, whereas the fast
ADMM theorem of [GOSB14, Thm 2] assumes both blocks strongly convex and G quadratic. This is a remark only: we
have not verified the correspondence with [GOSB14, Algorithm 7] line by line, and for the problem class the
same paper already gives an O(1/k²) dual rate with one strongly convex block by fast AMA [GOSB14, Thm 5]
(accelerated proximal gradient on the dual, cf. [BT14]).

## Why the range γ ≤ λ/(4L) and what remains open

A convex function f is L-smooth with L ≤ 1/γ if and only if f is the Moreau envelope e_γφ of a closed convex
function φ (equivalently f* − (γ/2)‖·‖² is convex), and then prox_{γf}(w) = (w + prox_{2γφ}(w))/2. So the
conjectured range γ ≤ 1/L is a statement about two arbitrary nonsmooth convex functions φ and g, while
γL < 1 strictly corresponds to φ being smooth with constant L/(1 − γL). The restriction 4γL ≤ λ is where the
potential above closes: the step inequality needs t²(4γL − λ) − (t + ¼)(1 − λ + γL) ≤ 0 for all t = t_i, which
forces 4γL ≤ λ as i → ∞. Numerical performance-estimation experiments (not part of the formal development)
indicate that at γL = 1 no potential of the form "weight × value + ‖v − w*‖² + quadratic form in (∇_i, s_i)"
that is independent of u_i certifies a horizon-uniform O(1/N²) bound, and that the exact worst-case
certificate has horizon-dependent weights. Proving O(1/N²) for γ up to 1/L, and the exact constant of
[PZ25, Conjecture 4], is open.

## Lean correspondence

- `spec` ([setup](../Setups/DouglasRachfordSmoothConvex.lean)): `Public` = (E, γ, lam, w1); `Params` adds
  L, R, ε. `admissible` contains exactly the assumptions listed above; `successful` asks for a minimizer x* on C
  with y_N ∈ C and F(y_N) − F(x*) ≤ ε for every seed.
- `acceleratedDouglasRachford` ([algorithm](../Algorithms/AcceleratedDouglasRachford.lean)): a state machine
  that alternates the queries `proxF w_i` and `proxG (2x_i − w_i)`; the momentum coefficient after iteration
  i is `((i − 2 : ℕ) : ℝ) / (i + 1)` with truncated subtraction, which is 0 for i = 1, 2.
- `budget q = 2 * ⌈√(2R²/(lam·γ·ε))⌉₊`; `result : Convergence spec budget`. Every prox call is one oracle call;
  the execution uses exactly `budget q` calls.

## References and verification level

- [PSB14] P. Patrinos, L. Stella, A. Bemporad, *Douglas–Rachford splitting: complexity estimates and
  accelerated variants*, CDC 2014, [arXiv:1407.6723](https://arxiv.org/abs/1407.6723) v2. Read in full
  (Theorems 2, 3, 5, 6, iteration (34)).
- [PZ25] H. Abbaszadehpeivasti, M. Zamani, *On the convergence rate of the Douglas–Rachford splitting
  algorithm*, [arXiv:2509.06676](https://arxiv.org/abs/2509.06676) v2 (preprint). Read in full (Algorithm 3,
  Conjectures 1–4, Section 5.2).
- [GOSB14] T. Goldstein, B. O'Donoghue, S. Setzer, R. Baraniuk, *Fast alternating direction optimization
  methods*, SIAM J. Imaging Sci. 7 (2014). Theorems 2 and 5 were checked in the UCLA CAM report 12-35 version
  by the reviewer of this note.
- [OJ25] I. K. Ozaslan, M. R. Jovanović, *Accelerated forward–backward and Douglas–Rachford splitting
  dynamics*, Automatica (2025), [arXiv:2407.20620](https://arxiv.org/abs/2407.20620). Abstract level
  (found by the reviewer of this note).
- [Kim21] D. Kim, *Accelerated proximal point method for maximally monotone operators*, Math. Program. 190
  (2021), [arXiv:1905.05149](https://arxiv.org/abs/1905.05149). Abstract level by the author; the reviewer
  of this note checked in the arXiv text that the rate is for the fixed-point residual.
- [DY16] D. Davis, W. Yin, *Convergence rate analysis of several splitting schemes*,
  [arXiv:1406.4834](https://arxiv.org/abs/1406.4834); [DY17] *Faster convergence rates of relaxed
  Peaceman–Rachford and ADMM under regularity assumptions*, Math. Oper. Res. 42 (2017),
  [arXiv:1407.5210](https://arxiv.org/abs/1407.5210). Abstract level by the author; the reviewer checked
  in the arXiv text of [DY17] that the objective rates for DRS/PRS are O(1/k) and o(1/k), without momentum.
- [BT09] A. Beck, M. Teboulle, *A fast iterative shrinkage-thresholding algorithm for linear inverse
  problems*, SIAM J. Imaging Sci. 2 (2009). [BT14] *A fast dual proximal gradient algorithm for convex
  minimization and applications*, Oper. Res. Lett. 42 (2014). From memory of the standard statements.
- [CP11] A. Chambolle, T. Pock, *A first-order primal-dual algorithm for convex problems with applications to
  imaging*, J. Math. Imaging Vis. 40 (2011); [CP16] *On the ergodic convergence rates of a first-order
  primal–dual algorithm*, Math. Program. 159 (2016). From memory of the standard statements.
- [Xu17] Y. Xu, *Accelerated first-order primal-dual proximal methods for linearly constrained composite
  convex programming*, SIAM J. Optim. 27 (2017), [arXiv:1606.09155](https://arxiv.org/abs/1606.09155).
  [TZ18] Q. Tran-Dinh, Y. Zhu, *Augmented Lagrangian-based decomposition methods with non-ergodic optimal
  rates*, [arXiv:1806.05280](https://arxiv.org/abs/1806.05280). [ST22] S. Sabach, M. Teboulle, *Faster
  Lagrangian-based methods in convex optimization*, SIAM J. Optim. 32 (2022),
  [arXiv:2010.14314](https://arxiv.org/abs/2010.14314). Abstract level by the author; the reviewer checked
  in the arXiv texts that the O(1/N²) rates of [Xu17], [TZ18] and [ST22] use adapted (iteration-dependent)
  parameters.

Search coverage for a prior general-f proof of fast DRS: arXiv math.OC 2025-08 to 2026-10 (keyword pull of
about 900 abstracts), targeted searches on accelerated Douglas–Rachford / ADMM / envelope methods, citations
of [PSB14] and [PZ25]. None found. OpenReview and paywalled journal versions were not accessible.
