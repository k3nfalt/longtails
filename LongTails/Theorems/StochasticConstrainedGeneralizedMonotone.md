# Finite-variance constrained generalized-smooth variational inequalities

The [main theorem](StochasticConstrainedGeneralizedMonotone.lean) gives a high-probability **strong tangent-residual** guarantee for general monotone variational inequalities with generalized smoothness, an unbiased finite-variance stochastic operator, and exact projection. The contribution is a projected stochastic contraction that handles cancellation by boundary normals without multiplying the variance cost by generalized curvature. Accumulative regularization, metric confidence amplification, and their composition are established tools.

Formal entry points are the [setup](../Setups/StochasticConstrainedGeneralizedMonotone.lean), [algorithm, tuning, and named output](../Algorithms/ProjectedClippedExtragradient.lean), [projected stability mechanism](../Proofs/ProjectedClippedStability.lean), and [execution guarantee](../Proofs/ProjectedClippedPublic.lean).

## Setup and guarantee

Let E be an arbitrary finite-dimensional real Hilbert space, X a nonempty convex set supplied through its exact Euclidean projection, and x₀∈X. Existence of this projection implies closedness; the proof derives it. The continuous operator F:E→E is globally monotone and satisfies the 1-symmetric generalized Lipschitz condition

\[
\|F(x)-F(y)\|\le (L_0+L_1\sup_{z\in[x,y]}\|F(z)\|)\|x-y\|.
\]

The Lean specification quantifies over every upper bound on the segment, equivalently to this supremum. There is a VI solution x⋆∈X with −F(x⋆)∈N_X(x⋆), ‖x₀−x⋆‖≤R, and ‖F(x⋆)‖≤G. These bounds concern the **same** solution. The normal cone uses ⟨η,w−x⟩≤0 for every w∈X. Unlike unconstrained root finding, F(x⋆) may be nonzero.

The jointly measurable oracle g(x,ω) obeys

\[
\int g(x,\omega)\,dp(\omega)=F(x),\qquad
\int\|g(x,\omega)-F(x)\|^2\,dp(\omega)\le\sigma^2,
\]

with vector and squared-error integrability. The path law is an abstract IID probability measure; independence and marginal laws, rather than a prescribed product representation, appear in the setup. No finite sample-space restriction, bounded noise, light tails, samplewise smoothness or monotonicity, paired sample queries, quasi-sharpness, bounded domain, or global operator bound is imposed. The global assumptions extend outside X. Public parameters satisfy L₀>0, L₁,G,σ≥0, R>0, ε>0, and 0<δ<1. The algorithm knows these bounds and x₀, but neither x⋆ nor F(x⋆).

Set q=L₁R, A₀=L₀+L₁G, C=(A₀+L₁ε)(1+q), and

\[
D=\frac{A_0(1+q)^2R}{\varepsilon}+(1+q)^4,\quad
V=\frac{\sigma^2}{\varepsilon^2},\quad
L=1+\log(2+CR/\varepsilon),\quad
L_\delta=1+\log((2+CR/\varepsilon)/\delta).
\]

The explicit budget is K=⌈2¹²⁸(D+V)L³Lδ⌉ **for each of the two oracle channels**. The returned point Y, named `ProjectedClippedExtragradient.output`, satisfies

\[
\Pr\bigl(\neg[Y\in X\ \land\ \exists\eta\in N_X(Y):
 \|F(Y)+\eta\|\le\varepsilon]\bigr)\le\delta.
\]

The output is measurable. This is a strong residual at one actually returned feasible point, not a restricted gap, an average gap, or a minimum selected using unavailable exact residuals. The probability includes the explicit algorithm/oracle product law. The formal proof bounds the bad set by a measurable failure event and does not assume measurability of an existential normal-cone description.

The total execution uses at most 2K calls, counting both stochastic operator and projection queries and all padding after the useful plan terminates. Projection positions consume IID tape entries even though projection ignores the samples; subsequent batches skip those entries. Thus the total complexity is

\[
\widetilde O\!\left(\frac{(L_0+L_1G)(1+L_1R)^2R}{\varepsilon}
 +(1+L_1R)^4+\frac{\sigma^2}{\varepsilon^2}\right).
\]

The displayed logarithms, including L³ on the deterministic terms, are part of the proved guarantee. Constants are deliberately conservative. There is no additional dimension factor beyond the parameters.

## Algorithm and proof mechanism

Let M=G+16A₀R+ε(1+8q), N=⌈log₂(2+2²⁰CR/ε)⌉+1, and k=⌈log₂(2N/δ)⌉+1. Stage s uses

\[
r_s=\frac{2^s\varepsilon}{2^{20}NR},\quad d_s=R2^{-s},\quad
S_s=2^{20}\bigl[C(1+L_1d_s)+r_s(1+L_1d_s)^4\bigr],
\]
\[
m_s=\max\{1,\lceil2^{23}\sigma^2/(r_sS_sd_s^2)\rceil\},
\qquad T_s=\lceil2^{16}S_s/r_s\rceil.
\]

At anchor a and feasible center c, restart k independent Tₛ-step trials from c. For the first regularized batch mean Ĥ₁(x), take γ=1/(16 max{Sₛ,L₁‖Ĥ₁(x)‖}), then

\[
y=P_X(x-\gamma\widehat H_1(x)),\qquad
x^+=c+\operatorname{clip}_{2d_s}\bigl(P_X(x-\gamma\widehat H_2(y))-c\bigr).
\]

The second batch is fresh and independent. Each step uses 2mₛ operator evaluations and two projections. Radial clipping toward feasible c preserves feasibility by convexity. Select a metric-majority trial center, with fallback c, and radially clip it about c. Set the next center to this point and the next anchor to its midpoint with a. After the last stage, preserve the anchor instead of changing it.

Finally use k fresh means of size max{1,⌈2²⁰σ²/ε²⌉}, with metric selection threshold ε/16, to estimate F at the last center. Return its projected regularized step with γfinal=1/[64(L₀+L₁M+L₁ε+r_{N−1})]. This final projection is what produces the strong tangent-residual certificate.

The new obstruction is that clipping saturation no longer forces a nonzero half-step displacement: projection can cancel a large normal component. The [stability proof](../Proofs/ProjectedClippedStability.lean) combines the projection variational inequality with a one-point monotonicity probe to show that this cancellation is controlled by boundary-normal coercivity. Either the projected displacement supplies descent, or the squared first-batch error pays for the failed displacement. After the fresh second-batch conditional expectation, the [stage proof](../Proofs/ProjectedClippedStage.lean) obtains, for the regularized VI solution pₛ,

\[
\mathbb E[\|x^+-p_s\|^2\mid x]
\le\left(1-\frac{r_s}{16S_s}\right)\|x-p_s\|^2
 +\frac{\sigma^2/m_s}{8S_s^2}.
\]

No cancellation of E[γe₁] is asserted: γ depends on the first batch. The uniform noise coefficient is essential. It yields stage cost O(Sₛ/rₛ+σ²/(rₛ²dₛ²)) before repetitions, instead of their product. Since rₛdₛ=ε/(2²⁰N), the summed statistical cost is O(kN³σ²/ε²). The q⁴ overhead absorbs the projected saturation geometry.

The analysis proves regularized VI existence, root transport, a polynomial root-operator bound M, and an invariant controlling cumulative regularization bias. These are analysis objects, not extra oracle information. [Adaptive IID sampling](../Proofs/ProjectedClippedSampling.lean), [first-failure accounting](../Proofs/ProjectedClippedProcess.lean), and [safe execution](../Proofs/ProjectedClippedExecution.lean) connect the mathematical process to the framework. [Budget algebra](../Proofs/ProjectedClippedBudget.lean) includes all rounds, batching, projections, and ceilings.

## Closest comparisons and reduction checks

- [Ji–Lan–Zhu, arXiv:2609.04188v2](https://arxiv.org/html/2609.04188v2), revised 17 September 2026, is the constrained globally Lipschitz baseline. Proposition 1 supplies accumulative regularization; Theorem 2.2 gives expected residual complexity Õ(LR/ε+V), and Theorem 4.2 gives high probability under light tails. Their Assumption 2, equations (2.27)–(2.28), requires an appropriate subsolver; the SOE bound in Lemma 4, equation (3.23), depends on the Lipschitz constant. We replace global Lipschitzness by generalized smoothness, retain finite variance, and quantify boundary magnitude by G. This is not an improvement in the globally Lipschitz subclass L₁=0; it extends its order up to logarithms.
- [Greenberg–Loizou, arXiv:2610.16886v1](https://arxiv.org/html/2610.16886v1), 12 October 2026, gives deterministic constrained generalized-smooth EG/PEG guarantees. Theorems 3.1–3.2 concern restricted averaged gaps; constrained strongly monotone bounds have exponential radius dependence, while polynomial Corollaries 3.5 and 3.7 are unconstrained. Section 5 identifies stochastic monotone extensions. Our guarantee uses a stochastic oracle and strong tangent residual; it does not supersede their different accuracy guarantees or broader deterministic analyses.
- [Vankov–Nedić–Sankar, arXiv:2410.12334v2](https://arxiv.org/html/2410.12334v2), accepted in [TMLR](https://openreview.net/forum?id=EjqSpbUBWU), has generalized-smooth stochastic constrained VIs but imposes global p-quasi-sharpness (Assumption 2.4, equation (6)); Theorem 4.4's expectation-rate range is α≤1/2 and its metric is solution distance. We impose global monotonicity and handle α=1 without quasi-sharpness. Their full nonmonotone structured class and ours are incomparable. The change is not simply removal of all their assumptions.
- [Alacaoglu–Kim, ICML 2026](https://proceedings.mlr.press/v306/alacaoglu26a.html), arXiv:2602.05531v1, treats globally Lipschitz monotone/weak-Minty stochastic VIs (Assumption 1.1) with a different, ε⁻⁴-type guarantee and affine-in-distance variance. [Alacaoglu, arXiv:2609.08380v1](https://arxiv.org/html/2609.08380v1), 8 September 2026, uses global Lipschitzness and Blum–Gladyshev assumptions with natural residual. Neither directly supplies this strong-residual polynomial/additive bound. These are scope comparisons, not universal dominance claims.
- The repository's existing [unconstrained stochastic result](StochasticGeneralizedMonotone.md) already combines accumulative regularization, stochastic clipping, and additive variance with Õ(L₀R/ε+q²+V). Its unprojected half-step has fixed displacement when clipping saturates. The present contribution is the constrained extension requiring boundary-normal saturation; additive variance and stochastic saturation in general are not new here. Its [exact constrained result](ConstrainedGeneralizedMonotone.md) has better deterministic dependence, O(A₀(1+q)R/ε+(1+q)² log), and parameter adaptation absent here. We pay an extra factor (1+q) in the leading deterministic term and a q⁴ transient for the finite-variance guarantee.

Standard ball localization followed by a Lipschitz theorem may require Lloc≈A₀ exp(O(q)). A polynomial root norm does not imply polynomial Lipschitzness throughout that ball: for Fᵢ(x)=sinh(xᵢ), X={x₂≥b}, and root/anchor p=(0,b,…), the root norm stays sinh(b) while ball Jacobians grow exponentially with radius. Thus the polynomial regime matters when q is large. When V dominates both methods, it need not improve the leading statistical order.

For a penalty reduction F+(I−P_X)/λ, a conservative transfer estimate of order Lloc λG suggests the sufficient choice λ of order ε/(LlocG), even granting applicable smoothness. Substitution into a Lipschitz solver cost O((Lloc+1/λ)R′/ε+V) can introduce O(Lloc G R′/ε²), where the localized radius R′ must also account for displacement of order λG and approximate-solve errors. This calculation does not prove that such a λ is necessary or that optimized penalty reductions must pay this cost. Direct robust simulation with per-stage error O(rₛdₛ) multiplies Sₛ/rₛ by a variance term of order σ²/(rₛ²dₛ²); the contraction above separates them. These are checks of specified reductions, not lower bounds against every possible reduction.

Nor can the existing unconstrained theorem simply be applied to a projection normal map. For X={x₂≥0} and monotone F(x₁,x₂)=(−x₂,x₁), the map F(P_Xz)+(z−P_Xz)/γ equals (0,z₁+z₂/γ) below X. Two such points differing by (1,−γ/2) give monotonicity inner product −γ/4. The required monotonicity is lost. An exact resolvent of F+N_X is not provided by the two available oracles.

## Motivation, assumptions, and limitations

Constrained equilibrium and constrained convex minimization naturally produce nonzero boundary normals. Global monotonicity, 1-symmetric generalized smoothness, projection access, and finite-variance sampling are established assumptions in the papers above. G is a public bound on a solution's normal magnitude, also used in the existing exact constrained setup; it is not a global bound on F. This added quantitative information and global assumptions outside X are material restrictions. We do not claim parameter-free adaptation or a theorem with unknown G. R>0 and L₀>0 are explicit; no zero-radius or zero-L₀ extension is asserted.

For a nonlinear interacting family in every dimension n≥2, choose a dense invertible matrix A, b>0, φ(t)=t²−log(1+t²), and

\[
f(x)=\phi((Ax)_1)+\sum_{i=2}^n(\cosh((Ax)_i)-1),\quad
F=\nabla f,\quad X=\{x:(Ax)_2\ge b\}.
\]

Then x⋆=A⁻¹(0,b,0,…), F(x⋆)=sinh(b)Aᵀe₂≠0, and valid constants are L₀=3‖A‖² and L₁=‖A‖²/smin(A). Dense A couples coordinates in the original geometry. Along x⋆+A⁻¹(t,0,…), any global p-quasi-sharpness ratio is proportional to |t|^{4−p}/(1+t²), requiring p≥4 near zero and p≤2 at infinity, which is impossible. This family is not globally Lipschitz and illustrates the newly covered regime. Independent additive mean-zero finite-variance noise satisfies the oracle assumptions. The theorem itself is not restricted to gradients, this family, separable objectives, quadratics, or a fixed dimension.

The proof requires finite dimension for regularized-root existence. Optimal q and G dependence, removal of the public G bound, sharper logarithms, and minimax optimality remain unresolved. At σ=0 the method is valid but less efficient than the exact-oracle comparator. Large constants make the explicit tuning a complexity certificate rather than a practical recommendation.

## Literature coverage

The Researcher and independent Reviewer surveyed current sources separately on 23–24 October 2026 UTC before candidate selection: publicly available ICML, ICLR, and NeurIPS 2025/2026 lists, roughly two years of arXiv submissions/revisions, and cited older foundations. Official proceedings/OpenReview were used to distinguish acceptance from preprints. The September/October 2026 monotone papers above are preprints unless a conference status is explicitly stated. NeurIPS download catalogues supplied titles when its proceedings root did not expose the main track. Some virtual pages were inaccessible; official catalogues and primary arXiv full texts supplied the relevant comparisons. This was a targeted optimization survey, not an exhaustive reading of all conference papers. No critical comparison above rests on an inaccessible full text or a missing search hit.

The survey also rejected routine Hölder regularization composition and screened stronger stochastic generalized-smooth convex acceleration results, including arXiv:2610.23301v2 (19 October 2026), before selecting the VI direction. Latest-version checks included the correction in arXiv:2404.02378v2 retracting its earlier fully stochastic acceleration claim; that unrelated claim is not used as a baseline here. Formal verification supports correctness, but the novelty claim rests on the projected boundary-normal contraction and the explicit comparable-assumption reductions above.
