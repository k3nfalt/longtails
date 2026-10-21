# Local acceleration of LoRA-GD by scalar silver steps

The [main theorem](SilverLoraLocalConvergence.lean) proves a local, high-accuracy improvement for simultaneous two-factor gradient descent. It covers general nonlinear, continuously differentiable outer objectives with Lipschitz gradients, without a Hessian continuity assumption. The contribution is an analysis of LoRA-GD with different scalar step sizes, as requested; it is not an improvement of the general nonconvex stationarity exponent in *On the Convergence of Stochastic Low-Rank Adaptation*.

## Problem, information, and algorithm

The [setup](../Setups/LocalSmoothStronglyConvexLora.lean) considers real matrices of arbitrary finite dimensions, with `1 ≤ r < min(m,n)`, and minimizes `f(BA)`. Matrix norms are Frobenius norms; the joint factor norm is the Euclidean sum of the two squared Frobenius norms. The outer function is globally μ-strongly convex and has a globally ρ-Lipschitz gradient, with `0 < μ ≤ ρ`. Its unconstrained optimum is exactly representable as `X⋆ = B̄Ā`, where both `B̄` and `Āᵀ` have smallest singular value at least `s > 0`. Let `R ≥ s` bound the operator norm of the derivative of `(B,A) ↦ BA` at `(B̄,Ā)`. One may take `R² = ‖B̄‖op² + ‖Ā‖op²`; this introduces no explicit rank factor.

The initial factors satisfy

\[
\|(B_0,A_0)-(\bar B,\bar A)\|\leq \frac{\mu s^2}{256\rho R}.
\]

The reference factors and optimum are existential instance data, unavailable to the algorithm. The dimensions, μ, ρ, s, R, accuracy ε, and initial factors are public. Each oracle call supplies the exact ambient gradient `G = ∇f(BA)`. There are no value, Hessian, inverse, or optimum queries. An arbitrary pretrained offset is accommodated by translating the outer objective: `f(X)=ℓ(Wpre+X)`; exact rank refers to the optimal adaptation X.

The [algorithm](../Algorithms/LoraSilver.lean), using [LoRA-GD](../Algorithms/LoraGd.lean), takes simultaneous updates

\[
B_{t+1}=B_t-\eta_tG_tA_t^\top,\qquad
A_{t+1}=A_t-\eta_tB_t^\top G_t.
\]

Both updates use the current factors and the same positive scalar. There is no momentum, alternating update, factor rebalancing, projection, or matrix preconditioning. `gdFamily` formally enforces these updates, product queries, initialization, and return of the final factors, while allowing the algorithm to choose positive scalar steps. Thus the setup does not prescribe the silver implementation as the only allowed algorithm.

Set

\[
L=8\rho R^2,\quad \alpha=\mu s^2/8,\quad
\kappa=L/\alpha=64\rho R^2/(\mu s^2),\quad \tau=1+\sqrt2,
\]
\[
k=\left\lceil\frac{\log(1+8\kappa)}{\log\tau}\right\rceil,
\quad K=128\lceil\kappa\rceil(k+1),\quad
q=\left\lceil\frac{\log(1+4LR^2/\varepsilon)}{\log4}\right\rceil.
\]

Take K warmup steps of size `1/L`, followed by q copies of the silver block `Hk/L`, defined by `H0=[]` and `H(j+1)=Hj ++ [1+τ^(j−1)] ++ Hj`. The middle entry is `1+τ^j/τ`, including j=0. The block has `2^k−1` entries and sum `τ^k−1`. The returned output is the last factor pair after all blocks, with no best-iterate oracle calls.

## Guarantee and improvement regime

The theorem proves `f(Bout Aout)−f(X⋆) ≤ ε` for every exact-oracle execution (and hence almost surely under the framework's seed law), using exactly

\[
T=128\lceil\kappa\rceil(k+1)+(2^k-1)q
=O\!\left(\kappa\log\kappa+
\kappa^{\log_{1+\sqrt2}2}\log(1+LR^2/\varepsilon)\right)
\]

full-gradient calls. The public Lean budget expands every quantity into μ, ρ, s, R, ε in one line. [Execution lemmas](../Proofs/LoraExecution.lean) connect this count to `execute`, and prove membership in the scalar GD family. No initialization or warmup calls are omitted. Arithmetic and storage costs are not bounded by this oracle theorem.

The exponent is approximately 0.7864. Under the same local assumptions, ordinary safe steps contract the gap by `1−1/(4κ)` per call and can use the actual initial gap E0. Over the stated initialization basin, `E0 ≤ C0 := α²/(256ρ) = LR²/(32κ²)`, giving the sharper worst-case baseline `O(κ log(1+C0/ε))` in the high-accuracy regime (and no calls are needed when ε already exceeds E0). Comparing against this baseline, the displayed bound improves condition dependence when `log(1+C0/ε)` is much larger than `κ^(1−0.7864) log κ`: replacing C0 by LR² in our logarithm adds only `O(log κ)`. This is a worst-case basin comparison, not a claim of faster execution on every initialization. It is not uniformly faster: the conservative warmup dominates at moderate accuracy. The nominal accuracy-dependent exponent gap to a square-root bound in κ is about 0.2864, but this understates the gap to unrestricted ambient optimization when factor conditioning is poor. This is a method-specific contribution, not an unrestricted problem-class complexity improvement.

The strongest elementary unrestricted comparison is ambient AGD followed by one rank-r truncation. Write `κout=ρ/μ` and let `D_X` bound `‖B0A0−X⋆‖F`; the initialization above permits the public choice `D_X=μs²/(128ρ)`. [Nesterov acceleration, as stated and proved in Bubeck, Section 3.7](https://arxiv.org/html/1405.4980v2), reaches ambient objective gap `δ=με/(4ρ)` in `O(1+√κout log(1+ρ²D_X²/(με)))` full-gradient calls. If X̃ is that point and X̂ its best rank-r approximation, rank-r representability gives `‖X̂−X⋆‖F ≤ 2‖X̃−X⋆‖F`; strong convexity and smoothness then give `f(X̂)−f⋆ ≤ 4κout δ = ε`. SVD factors of X̂ provide an output with r-column factors without additional gradient calls. This reduction uses dense iterates, momentum and final truncation, outside the simultaneous scalar-factor-GD family. Ignoring logarithmic scales and warmup, the ratio of our accuracy-dependent coefficient to this comparator is `κ^a/√κout = 64^a κout^(a−1/2) (R/s)^(2a)`, where `a=log_τ 2≈0.7864`. Even at fixed factor conditioning, a polynomial gap remains. The significance claimed here is that scalar LoRA-GD itself admits a rigorously faster local nonlinear analysis than short-step GD under C1,1 assumptions, not that it matches AGD or improves the best algorithm for this objective class.

## What the proof adds

The silver schedule and its convex certificates are established results. The new mechanism here is a quantitative extension to the nonlinear bilinear pullback, with a nonisolated set of exact factorizations and only C1,1 outer regularity, including the entire long-step trajectory and polynomial-cost entry into its stable neighborhood.

1. [Factor repair](../Proofs/LoraFactorRepair.lean) constructs an exact factorization z near a given x using an orthogonal projection and a linear solve **in the proof only**. Within distance s/2 of the reference, `‖x−z‖² ≤ 8‖BA−X⋆‖²/s²`. No balance constraint or isolated factor minimizer is assumed. [Error bounds](../Proofs/LoraErrorBounds.lean) then give `α(f(BA)−f⋆) ≤ 2‖∇(f∘product)(x)‖²` when the outer gradient is sufficiently small.
2. [Warmup](../Proofs/LoraWarmup.lean) establishes descent and a finite path length before using the next local descent inequality. This avoids assuming that the trajectory stays in the neighborhood. After K steps, an exact center is within distance `D = [R/(2κ)] 2^(−12(k+1))` of the actual iterate. This apparently small radius is inverse polynomial in κ; reaching it costs `O(κ log κ)`, not an exponential number of calls.
3. [Local interpolation](../Proofs/LoraSilverLocal.lean) derives a convex interpolation defect for the actual normalized factor gradient: in a radius-a tube about an exact center, its negative part is at most `(a/R)‖u−v‖²`. This follows from outer convex cocoercivity and the exact quadratic remainder of the product map, not a Hessian expansion.
4. [Silver stability](../Proofs/SilverStability.lean) controls every recursive prefix as well as the endpoint. The primitive certificate's coefficient mass is at most `3(2+2τ)^k`; a recursive radius bound uses `4·3^k D`. Their product is polynomial in κ. A completed left block controls the joining long step before the right block is analyzed, so no interpolation inequality is invoked at an unverified outside point.
5. [Epochs](../Proofs/LoraEpochs.lean) repair the endpoint to a new exact center, halve its distance bound, and sum center drift. They prove the last-iterate gap bound `4LR²/4^q`. All actual iterates stay inside the original s/2 neighborhood. [Tuning](../Proofs/LoraSilverTuning.lean) and [assembly](../Proofs/LoraSilverConvergence.lean) supply the explicit constants and rounding.

A direct appeal to the convex silver theorem is invalid because `f(BA)` need not be convex. Local PL plus ordinary smooth descent gives the linear-in-κ baseline, not the fractional exponent. A quadratic/Hessian linearization needs additional regularity absent here. A naive per-step perturbation estimate for the long steps can grow exponentially in the block length; the recursive certificate and prefix argument are what retain polynomial entry cost. Regularization, batching of an exact oracle, or applying an ambient optimizer do not reproduce the stated simultaneous factor-GD execution.

## Assumptions, examples, and limitations

Strong convexity and smoothness of an outer matrix objective, exact low-rank representability, nondegenerate factors, and local initialization are established assumptions in local matrix-factorization theory. In particular, Park, Kyrillidis, Caramanis and Sanghavi, [arXiv:1606.03168v3](https://arxiv.org/html/1606.03168v3), Definitions 2.1–2.2, state the same smoothness and strong-convexity inequalities (we take the convexity domain to be the whole matrix space). Their problem (1), Assumption A1 and Theorem 4.2 motivate low-rank minimizers and local factor initialization. Their algorithm includes a balancing regularizer and covers approximate rank with residual error; our theorem omits that regularizer but requires an exact rank-r optimum. Their basin scales as `s/√(ρ/μ)` for balanced factors, larger than ours even with well-conditioned factors. Our individual singular-value lower bounds express nondegeneracy without enforcing balance; the derivative bound R is a conditioning parameter, not a new functional restriction. The precise radius and its constants above are new sufficient restrictions of this analysis, not claimed standard or necessary. The proof uses them for safe warmup and preservation of conditioning. It does not establish entry from random or zero-factor LoRA initialization. Global strong convexity excludes underdetermined matrix sensing with a noninjective measurement map, despite its restricted convexity on low-rank directions. Exact representability excludes approximate rank-constrained optima with nonzero ambient gradient. Singular or overparameterized optimum factors are also excluded. The bounds depend on the chosen factor representative; no invariance under arbitrary invertible factor changes is claimed.

A nonlinear family in arbitrary dimension is

\[
f(X)=\frac\mu2\|X-X_\star\|_F^2+
\frac{\rho-\mu}{2}\max\{0,\langle H,X-X_\star\rangle\}^2,
\qquad \|H\|_F=1,
\]

with any rank-r X⋆ and a dense H. This has coupled coordinates, a globally Lipschitz gradient and the required strong convexity. For ρ>μ its Hessian fails to exist on a hyperplane through the optimum. It demonstrates why a theorem for quadratics or twice differentiable objectives does not imply this result. The theorem covers the full specified C1,1 class, not merely this family. Dimensions enter through factor conditioning and derivative bounds, not through a hidden fixed-dimensional constant. The nontrivial issue is controlling changing factor subspaces and cross-coordinate curvature during long steps.

## Closest primary results

- Wang, Liu and Lui, [*On the Convergence of Stochastic Low-Rank Adaptation*, arXiv:2607.21975v2](https://arxiv.org/html/2607.21975v2), Theorem 3.1, gives a general smooth, lower-bounded LoRA-GD factor-stationarity guarantee with its adaptive scalar steps. Its `ε^−4` criterion and arbitrary initialization are different from this local objective-gap theorem. We retain the simultaneous LoRA-GD updates, change their scalar schedule, and analyze a recognized stronger local problem; we do not improve that theorem on its whole class. The related [Mu–Klabjan ICML 2026 paper](https://proceedings.mlr.press/v306/mu26a.html), arXiv:2512.18248v3, is not used as a weaker baseline in place of the later result.
- Grimmer, Shu and Wang, [arXiv:2410.16249v2](https://arxiv.org/html/2410.16249v2), Appendix A, Lemma 15, equations (29)–(32), and Proposition 6, supply the convex primitive identity used here. Altschuler and Parrilo's [silver schedule](https://arxiv.org/abs/2309.16530) and [strongly convex hedging](https://arxiv.org/abs/2309.07879) already attain the fractional exponent in convex optimization. Neither the schedule nor that exponent is claimed new. Zhang, Lee, Du and Chen's [anytime stepsize result](https://arxiv.org/abs/2411.17668), COLT 2025, also makes clear that prefix questions themselves are established; our prefix estimate handles local nonlinear interpolation defects.
- Ma, Li and Chi, [*Beyond Procrustes: Balancing-Free Gradient Descent for Asymmetric Low-Rank Matrix Sensing*](https://users.ece.cmu.edu/~yuejiec/papers/RectangularMF.pdf), Theorem 1 and equation (10), arXiv:2101.05113, analyze unregularized simultaneous GD for RIP least squares, with an accuracy-dependent factor condition number of first power. For balanced representatives, our κ is proportional to `(ρ/μ)κ(X⋆)`; our radius scales as `s/[(ρ/μ)√κ(X⋆)]`. Their basin and RIP class differ, so there is no universal inclusion or dominance claim. This comparison supports the fixed-method improvement while preserving the nonlinear and initialization qualifications.
- Zhang, Liu and Chen, [*LoRA-One*, ICML 2025](https://proceedings.mlr.press/v267/zhang25ax.html), arXiv:2502.01235v3, Theorem C.17, proves `O(κ(X⋆)³ log(1/ε))` convergence of plain GD for its linear regression model and spectral initialization; this is not the strongest older local plain-GD baseline. Theorem C.21 and Theorem 4.2 use matrix preconditioning, including for their nonlinear teacher model. Their condition-independent preconditioned rate is a stronger option in its setting, but is not the shared-scalar update family here. Our theorem supplies no competing initialization procedure.
- Zhou, Cao and Gu, [AISTATS 2020](https://proceedings.mlr.press/v108/zhou20b/zhou20b.pdf), Corollary 4.3, obtains accelerated local convergence with momentum and projection; the asymmetric extension uses balancing. Tong, Ma and Chi's [ScaledGD, JMLR 2021](https://jmlr.org/papers/v22/20-1067.html) uses matrix preconditioning and treats general losses under restricted smoothness/convexity. These are essential stronger outside-family comparisons, not results superseded by this theorem.

- Park, Roy, Siegel and Bhattacharya, [*Acceleration via silver stepsize on Riemannian manifolds*, NeurIPS 2025](https://papers.neurips.cc/paper_files/paper/2025/file/347dae37f42ba41506cf7af753f98560-Paper-Conference.pdf), [arXiv:2506.06160v2](https://arxiv.org/html/2506.06160v2), Theorems 4.1–4.2, proves acceleration for vector-transported updates (4.1) under transport-relative convexity and smoothness (Definitions 3.4–3.5). The latest revision explicitly corrects the earlier ordinary-RGD claim. Its update uses exponential/logarithm maps at a fixed base; it is not the simultaneous Euclidean factor update above. Taking Euclidean identity transport would require convexity of the factor objective, which fails here. The present proof instead controls a vanishing interpolation defect and moving exact-factorization centers.

The literature assessment used the current date, 20 October 2026, recent ICML, ICLR and NeurIPS proceedings/OpenReview and roughly two years of arXiv work, then followed older foundational results. Version checks included the target's September 2026 revision and the June 2025 LoRA-One revision. Relevant finite-horizon inexact-PEP investigations such as [Vernimmen–Glineur, arXiv:2506.09730v3](https://arxiv.org/abs/2506.09730v3) do not themselves provide the uniform nonlinear trajectory theorem proved here. Some OpenReview direct PDF accesses were unavailable during screening. The potentially close Riemannian-silver paper was subsequently checked through its accessible latest arXiv version and official NeurIPS proceedings, as detailed above. The novelty claim is the complete local C1,1 factor-GD guarantee with polynomial warmup and actual-call accounting, not absence of a matching search result or the formalization alone.
