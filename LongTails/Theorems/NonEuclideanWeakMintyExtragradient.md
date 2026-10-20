# First-order extragradient under native non-Euclidean weak Minty

The [main theorem](NonEuclideanWeakMintyExtragradient.lean) gives an explicit first-order residual guarantee for Lipschitz operators satisfying the ordinary quadratic weak-Minty condition in an arbitrary finite-dimensional norm. The contribution is a dimension-independent admissible weak-Minty parameter without a smoothness assumption on the mirror map. It is a new analysis of a non-Euclidean extragradient construction, not a claim that mirror descent, spectral linear minimization, or extragradient itself is new.

## Formal problem and guarantee

The [setup](../Setups/NonEuclideanWeakMinty.lean) takes a finite-dimensional real normed space E, an exact operator F:E→E*, and a known differentiable mirror h. It assumes

- L>0 and ‖F(x)−F(y)‖*≤L‖x−y‖;
- a root x* with F(x*)=0 and ⟨F(x),x−x*⟩≥−ρ‖F(x)‖*² for every x;
- 0≤ρ≤1/(20L), and D_h(u,x)≥(μ/2)‖u−x‖² with μ>0;
- D_h(x*,x₀)≤D, D≥0, and ε>0.

The assumption provenance is [Diakonikolas, Daskalakis and Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), §2.1 Eq. (a1) for primal-to-dual Lipschitz continuity, Assumption 1 Eq. (a2) for weak Minty, and §2.3/Definitions 2.1–2.2 for strong convexity and Bregman geometry. Their weak-Minty right side is −ρ_paper‖F(x)‖*²/2, so our convention is ρ=ρ_paper/2. D is a bound on the standard initial Bregman potential. The sufficient threshold 1/(20L), the displayed step tuning, and the theorem for a general strongly convex differentiable mirror are the choices and guarantee established here.

Here D_h(u,x)=h(u)−h(x)−Dh(x)[u−x]. Mirror differentiability and this strong-convexity inequality are global; no Lipschitz bound on Dh is assumed. The space, norm, h, x₀, L, ρ, and μ are public. The operator, root, D, and ε are not available to the update rule. The private accuracy and radius enter only the execution budget. The exact oracle may have seed fields, but its answer is required to equal F(x) at every call and seed. The guarantee therefore holds pointwise in all seeds, and hence almost surely under the probability measure in the repository framework. This is an unconstrained root-residual result, not a global saddle-value guarantee.

The [algorithm](../Algorithms/NonEuclideanExtragradient.lean) uses a norming direction J(g) satisfying ‖J(g)‖≤‖g‖* and ⟨g,J(g)⟩=‖g‖*². At base point x it queries g=F(x), sets

    y = x − J(g)/(2L),
    x⁺ = argmin_z { (μ/(10L))⟨F(y),z⟩ + D_h(z,x) },

and returns the base point with smallest observed dual residual. Each iteration queries F twice. The second query and final correction are paid for even when the corrected point is not returned. Norming directions and mirror minimizers are proved to exist in finite dimension; neither is an additional oracle assumption. Exact mirror minimization is free in this operator-oracle model, so this is not an arithmetic-complexity bound for arbitrary h.

For K=1+⌈400L²D/(με²)⌉ iterations, the public budget is exactly

    2 + 2⌈400L²D/(με²)⌉ operator calls.

The returned, actually queried point has ‖F(output)‖*≤ε. The extra iteration covers D=0 without a zero-iteration output assertion. The [geometry proof](../Proofs/NonEuclideanWeakMintyGeometry.lean), [step proof](../Proofs/NonEuclideanExtragradientStep.lean), and [execution proof](../Proofs/NonEuclideanExtragradientRun.lean) establish this from the assumptions and `execute`.

## Spectral interpretation and relation to Muon

The [spectral specialization](../Proofs/SpectralExtragradient.lean) realizes E as linear maps between Euclidean spaces, with their genuine operator norm. The [matrix geometry](../Proofs/SpectralMirrorGeometry.lean) proves the trace pairing, the Frobenius-quadratic Bregman identity, strong convexity with μ=1, and

    D_h(X*,X₀) = ‖X*−X₀‖F²/2 ≤ min(m,n) ‖X*−X₀‖op²/2.

The nuclear norm is represented by its standard dual definition: the operator norm of the trace functional on the spectral-normed matrix space. The formal trace identity connects this functional to matrix coordinates. Consequently the guarantee is O(L²‖X*−X₀‖F²/ε²), or O(rL²Rop²/ε²) when r=min(m,n) and ‖X*−X₀‖op≤Rop, for nuclear-norm residual ε. Here r is the smaller matrix dimension, not an assumed rank of F or its iterates.

The predictor uses a spectral-ball maximizing direction scaled by the nuclear norm. The corrector is proved to be X−F(Y)/(10L) when the oracle is represented through the Frobenius trace pairing. This supplies a substantive connection to Muon-style spectral geometry while retaining arbitrary nonlinear matrix operators and noncommuting matrices. The formal algorithm fixes an arbitrary norming selection. It does not identify that selection with the canonical compact polar factor: maximizers can differ on null spaces. A polar factor is a familiar mathematical realization of spectral linear maximization, but no guarantee for the exact canonical-polar trajectory or standard momentum Muon is claimed. No `allowedAlgorithm` restriction is imposed on the problem class.

## New mechanism and closest comparisons

With a=‖F(x)‖*, the norm-steepest predictor gives ‖F(y)−F(x)‖*≤a/2 and ⟨F(y),J(F(x))⟩≥a²/2. Combining these directly with ordinary weak Minty at y yields

    ⟨F(y),x−x*⟩ ≥ 11a²/(80L).

Mirror optimality and strong convexity then give

    D_h(x*,x⁺) ≤ D_h(x*,x) − μa²/(400L²).

The technical distinction is obtaining alignment in the native dual residual before the mirror correction. Previous smooth-mirror analyses use a bound on the mirror derivative to recover residual control from displacement. That route introduces a geometry-dependent restriction on ρ. The final Young inequality and telescoping argument here are classical.

| Primary baseline | Relevant distinction |
|---|---|
| [Diakonikolas, Daskalakis and Jordan, AISTATS 2021](https://proceedings.mlr.press/v130/diakonikolas21a.html), eg_p+ and Remark 4.2 | The non-Euclidean ρ>0 extension is left unresolved there. For 1<p<2, the predictor/quadratic-Bregman-corrector construction is already their algorithm; the contribution here is its tuning and analysis under ordinary weak Minty, not a new algorithm in that regime. |
| [Zhang and Dai, arXiv:2108.12070](https://arxiv.org/abs/2108.12070), Theorem 5.2; published JORSC 13 (2025), 83–113 | Requires a mirror that is both strongly convex and gradient-Lipschitz. Its admissible nonmonotonicity depends on the strong-convexity/smoothness ratio. The printed threshold and proof denominator differ by a constant factor; neither version removes that geometry dependence. |
| [Lee and Kim, arXiv:2105.15042v3](https://arxiv.org/abs/2105.15042v3), SA-MGDA | Uses smooth, strongly convex Legendre geometry. It does not supply the stated native-norm range for a nonsmooth-gradient mirror. |
| [Alizadeh, Hamedani and Jalilzadeh, arXiv:2405.10735v3](https://arxiv.org/abs/2405.10735v3), Assumption 5 and Eq. (36); OMS 41(1), 2026 | The nonmonotone analysis retains mirror-gradient smoothness and its constant. |
| [Pethick, Mavrothalassitis and Cevher, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), “Efficient Interpolation Between Extragradient and Proximal Methods for Weak MVIs” | Gives stronger Euclidean admissible constants, approaching ρ<1/L, and the separating-halfspace viewpoint. Its formal oracle realization is Euclidean. The O(1/ε) squared-residual statement is O(1/ε²) for residual norm ε. The present contribution is the explicit native-norm first-order separator, not invention of halfspace descent. |
| [Oblique weak-Minty PPPA, arXiv:2305.03605v2](https://arxiv.org/abs/2305.03605v2) | A fixed symmetric weak-Minty matrix and a full-domain resolvent do not by themselves give the nonlinear dual-norm quadratic condition or a two-call first-order implementation. |
| [Vyas and Bullins, arXiv:2603.13491v1](https://arxiv.org/abs/2603.13491v1), “Beyond First-Order Methods for lp-Structured Non-Monotone VIs” | Uses higher-order information and changes the weak-Minty exponent. This is an unreviewed preprint, not an ordinary quadratic first-order theorem under the same assumptions. |

A generic Euclidean norm conversion with distortion A can require ρL=O(A⁻²); at the spectral endpoint A=√r. Thus the native condition ρL≤1/20 covers a larger established problem class than that conversion. This is a sufficient-condition comparison, not a lower bound or proof that a Euclidean algorithm diverges. An instance-specific preconditioner may improve the conversion. The result neither optimizes the admissible constant nor claims that the chosen mirror minimizes D/μ.

A standard cutting-plane reduction must also be counted. Set ρ̄=1/(10L). For a base residual above ε, the predictor produces a separating halfspace retaining the norm ball of radius ε/(40L) about x*. Exact center-of-gravity cuts with a known initial radius R therefore give O(1+d log(1+LR/ε)) first-order calls in ambient dimension d, with two calls per cut and potentially substantial arithmetic cost. The present ε⁻² bound is not universally oracle-optimal. In m-by-n spectral geometry it improves this oracle count in the high-dimensional/moderate-accuracy regime where (LRop/ε)² is smaller than max(m,n) times the corresponding logarithm, up to universal constants.

## Nonlinear scope and limitations

A concrete interacting two-player family illustrates the ordinary weak-Minty regime. Take α,c,τ≥0 and β>α+c. For u,v∈ℝᵈ, write a=mean(u), b=mean(v), ψ(t)=−αt²/2+c log cosh(t), and

    f(u,v) = ψ(a) − ψ(b) + βab
             + τ[logsumexp(u−a1) − logsumexp(v−b1)].

For F=(∇u f,−∇v f), use the maximum ℓ∞ norm across the two players and its sum-ℓ1 dual. Centered log-partition gradients are monotone and sum to zero. Hence ⟨F(z),z⟩≥−α(a²+b²), while summing the two gradient blocks gives ‖F(z)‖*≥(β−α−c)√(a²+b²) when β>α+c. One can take ρ=α/(β−α−c)² and L≤2(α+c+β+τ). For α=.001, c=.25, β=τ=1, ρL<.009. This family has a root at zero, genuinely interacting nonlinear coordinates, and arbitrary dimension. It is a stationary-game example, not a global saddle-value problem: its own-player tails are unbounded.

For symmetric matrices, replace centered logsumexp by the convex shift-invariant function

    H_A(X) = log tr exp(X+A) − tr(ρ_A X),   ρ_A=exp(A)/tr exp(A),

with fixed nonscalar symmetric A, and replace means by normalized traces. Its gradient is traceless, vanishes at zero, and generally does not commute with X. The derivative of the normalized matrix exponential gives the conservative operator-to-nuclear Lipschitz bound 2: its integral term and normalization term each have nuclear norm at most the perturbation's operator norm by Schatten Hölder. The same mean/contrast argument gives L≤2(α+c+β+2τ) and the same ρ, still ρL<.012 for those parameters. These are mathematical illustrations of the general specification, not additional restrictions or separately exported Lean convergence results. A mean/contrast preconditioner can exploit this particular family; it is not evidence of per-instance state-of-the-art complexity.

The theorem covers general nonlinear finite-dimensional operators, not only these examples, separable maps, or quadratics. It does not cover stochastic oracles, constrained mirror subproblems, approximate mirror solutions, infinite-dimensional spaces, or a power-uniformly-convex mirror without quadratic strong convexity. No such extension is claimed.

Literature screening used UTC 2026-10-20, the publicly available 2026/2025 ICML, ICLR and NeurIPS material and approximately two years of arXiv submissions/revisions, followed by the older primary baselines above. Accepted status was distinguished from submissions and preprints. Direct OpenReview access was blocked for a relevant ICLR source; its official proceedings PDF was checked instead. Latest checked nearby work includes [Mirror-Free Proximal Methods, arXiv:2603.20918v1](https://arxiv.org/abs/2603.20918v1), whose monotone averaged-gap statements do not give this weak-Minty residual result. Search coverage supports the comparison but does not guarantee absolute priority. The strongest novelty objection is that the final descent resembles known halfspace methods; the substantive claim is the native-norm first-order realization and its enlarged admissible ordinary weak-Minty regime.
