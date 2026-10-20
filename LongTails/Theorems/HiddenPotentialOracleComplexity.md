# The oracle cost of hiding a potential decomposition

## Problem and guarantees

Let \(F=\nabla\phi+S\) on a real Hilbert space. Assume that \(F\) is
\(\mu\)-strongly monotone, \(\mu>0\), that \(\nabla\phi\) is \(L\)-Lipschitz,
and that \(S\) is \(s\)-Lipschitz. A root \(x_\star\) satisfies
\(\|x_0-x_\star\|\le R\). The algorithm knows \(\mu,L,s,R,\varepsilon,x_0\)
and can query **only the combined vector \(F(x)\)**. It receives neither
component separately, function values, Jacobian products, nor transpose
products. The decomposition is an existential property of the instance.
The upper bound does not require convexity of \(\phi\) or monotonicity of
\(S\).

The [setup](../Setups/HiddenPotentialStronglyMonotone.lean) states this model
directly. The [main theorem](HiddenPotentialOracleComplexity.lean) constructs
[hiddenPotentialOutput](../Algorithms/HiddenPotential.lean) and guarantees
that its final returned point satisfies \(\|x_{\mathrm{out}}-x_\star\|\le
\varepsilon\), with the explicit oracle budget

\[
K=\left\lceil
2^{21}\frac{\sqrt{(\mu+s)(L+\mu+s)}}{\mu}
\log(2+s/\mu)\log(2+R/\varepsilon)
\right\rceil .
\]

Here juxtaposition denotes multiplication, including between the square-root
factor and both logarithms. The guarantee is deterministic; the setup writes
it almost surely under the explicit execution probability measure. The
algorithm is independent of the private decomposition. No admissible-method
restriction is imposed. The upper theorem covers complete real Hilbert
spaces, hence arbitrary finite dimension, and nonlinear fields.

The accompanying
[combined_oracle_lower_bound](../Proofs/HiddenDecompositionLowerBound.lean)
proves a different, complementary statement. For every \(N\)-query
deterministic algorithm with arbitrary adaptive queries and arbitrary output,
when \(0<\mu\le s\le L/4\) and \(R>0\), there is a real finite-dimensional
affine instance for which

\[
\|x_{\mathrm{out}}-x_\star\|
\ \ge\ \frac{R}{3}\exp\!\left(
-\frac{12(N+1)\mu}{\sqrt{Ls}}\right).
\]

The space has real dimension \(8N+14\). This is a worst-case,
query-dependent-dimension lower bound, not a claim for a fixed dimension as
\(N\) tends to infinity. The formal lemma quantifies over an algorithm and a
fixed seed before constructing its instance; it establishes the deterministic
lower bound and does **not** establish a randomized minimax lower bound.
The hard instance satisfies the same Lean specification. Moreover its
potential has a \(\mu\)-strongly monotone, \(L\)-Lipschitz gradient and its
residual is monotone and \(s\)-Lipschitz. Thus the oracle comparison below
takes place on the same established subclass.

Consequently, accuracy \(\varepsilon<R/3\) on every such instance requires
\[
N+1\ge
\frac{\sqrt{Ls}}{12\mu}\log\frac{R}{3\varepsilon}.
\]
In this regime the upper polynomial factor is
\(\Theta(\sqrt{Ls}/\mu)\); an additional
\(\log(2+s/\mu)\) remains in the upper bound. Constants, including the
conservative public-budget constant, are not optimized.

## Contribution and closest comparisons

The contribution is the quantitative information separation between combined
and split access, together with a nearly matching nonlinear upper bound.
It is not a new acceleration primitive, a new resisting-oracle framework,
or novelty arising from Lean formalization.

On the subclass with a strongly convex smooth potential and a monotone
Lipschitz residual, separate access to \(\nabla\phi\) and \(S\) permits
\[
O\!\left((\sqrt{L/\mu}+s/\mu)\log(R/\varepsilon)\right)
\]
component evaluations, up to universal constants and the usual harmless
logarithmic conventions. Both component evaluations are charged; a constant
number per iteration changes no parameter rate. This follows from the
restarted AG-EG analysis of
[Yuan et al., NeurIPS 2023](https://proceedings.neurips.cc/paper_files/paper/2023/file/69ce18ad9f53f28e8e7ac1649ae02337-Paper-Conference.pdf),
Assumption 2.1, Definition 2.1, Theorem 2.5 and its restarting discussion
(with zero stochastic variance). Theorem 2.3 gives the related direct
approach. The more recent
[Lee–Ryu–Yun NOD manuscript, arXiv:2604.11105v1](https://arxiv.org/html/2604.11105v1),
Theorem 4.1, provides another split-access baseline. It was a preprint at
the literature check, not treated here as an accepted conference paper.

For \(\kappa=L/\mu\ge16\) and \(s=\sqrt{L\mu}\), the split polynomial factor
is \(2\sqrt{\kappa}\), while the combined lower factor is
\(\kappa^{3/4}\). This gives an asymptotic quarter-power oracle separation.
More generally, the mixed term is consequential when
\(\mu\ll s\ll L\). No universal separation is claimed at the endpoints or
outside the proved lower-bound regime. In particular, the broader upper
class is not compared against a split theorem that assumes stronger
component monotonicity.

Other close results delimit the novelty:

| Primary result | Relation to this result |
|---|---|
| [Wang–Li, NeurIPS 2020](https://papers.nips.cc/paper_files/paper/2020/hash/331316d4efb44682092a006307b9ae3a-Abstract.html), [arXiv:2006.06359v2](https://arxiv.org/html/2006.06359v2), Theorem 3 | Already gives a mixed square-root upper expression for nonlinear strongly convex–strongly concave problems with a public two-block partition. That structure and its permitted block queries differ from a private decomposition of a general monotone field. The numerical mixed expression itself is not new. |
| [Azizian et al., AISTATS 2020](https://proceedings.mlr.press/v108/azizian20a/azizian20a.pdf), Proposition 3 and §5.3 | Supplies spectral polynomial lower-bound machinery and ellipse analyses. Proposition 3 alone is not an arbitrary adaptive-algorithm lower bound; the present proof includes that lifting. |
| [Spillane–Szyld, arXiv:2504.05723v2](https://arxiv.org/abs/2504.05723v2), §4, equation (26); [IMA Journal of Numerical Analysis, 2026](https://doi.org/10.1093/imanum/drag051) | Gives rectangle conformal characterizations and numerical rates using classical approximation theory. The inspected statement does not give the explicit uniform mixed-parameter oracle separation established here. Rectangle approximation theory is prior work. |
| [Dereziński–Epperly–Meyer, COLT 2026](https://proceedings.mlr.press/v336/derezinski26a.html), [arXiv:2602.04842v4](https://arxiv.org/abs/2602.04842v4) | Studies one-sided versus two-sided matrix-vector access, including randomized lower bounds on general matrix classes. Those results do not supply the present strongly monotone, separately controlled symmetric/skew parameter theorem. The present lower bound is only deterministic. |

NOD §4.2 discusses a narrower public-partition saddle-point question. This
result does not resolve that question. A known partition can permit
component recovery in special bilinear cases. Similarly, white-box
automatic differentiation can supply transpose/Jacobian products; the
lower bound does not apply to that richer access model.

## Proof and execution

For the upper bound, regularize each root problem with
\(\beta=512s\). Strong monotonicity of \(F\) and Lipschitzness of \(S\)
imply that \(\nabla\phi\) is \((\mu-s)\)-strongly monotone, so the
regularized potential has curvature \(m=\mu+511s\). Set
\(\ell=L+\mu+512s\), and use
\[
T=\lceil16\sqrt{\ell/m}\rceil,\qquad
H=\left\lceil\frac{\log(2(\mu+\beta)/\mu)}{\log2}\right\rceil,\qquad
N=\left\lceil\frac{2(\mu+\beta)}{\mu}\log(2+R/\varepsilon)\right\rceil .
\]
Each inner routine is projected acceleration on a ball. For analysis only,
freeze the residual at the ball center and absorb it into a linear
potential term. Combined-oracle replies then have gradient error at most
\(s\) times the ball radius. A bounded-error energy estimate contracts that
radius by one half. After \(H\) stages the proximal error is small enough
to obtain outer contraction \(1-\mu/(2(\mu+\beta))\).
Proximal-root existence is derived, not assumed.

This is a standard inexact-acceleration/proximal reduction; related
approximate-gradient analysis appears in
[d’Aspremont, SIAM Journal on Optimization 2008](https://www.di.ens.fr/~aspremon/PDF/SmoothSparseSDP.pdf),
condition (2.3) and Theorem 2.2. The proof here establishes the particular
bounded-ball error estimate and all radius and execution conditions.
See [energy lemmas](../Proofs/HiddenDecompositionEnergy.lean),
[nonlinear convergence](../Proofs/HiddenPotentialConvergence.lean),
[tuning and budget](../Proofs/HiddenPotentialBudget.lean), and
[execution](../Proofs/HiddenPotentialExecution.lean).
The nested routine uses \(NHT\) informative combined calls. The public
budget dominates this product. Execution may make further ignored replies
after the routine finishes; every one of the \(K\) calls is charged.

The quantitative lower-bound step is an explicit finite spectral witness.
A trace transformation \(z\mapsto z+z^{-1}\) and Chebyshev interpolation
place nodes inside the admissible spectral rectangle. The normalized
exterior displacement is of order \(\mu^2/(Ls)\), yielding exponential
scale \(n\mu/\sqrt{Ls}\). Absolute interpolation coefficients define one
fixed set of nonnegative weights that simultaneously obstructs every
normalized real polynomial of degree at most \(n\). No choice of weights
depending on the algorithm's polynomial is made.
See [finite interpolation](../Proofs/HiddenDecompositionPolynomial.lean)
and [real linear realization](../Proofs/HiddenDecompositionLinear.lean).

The [resisting-rotation proof](../Proofs/HiddenDecompositionResistance.lean)
then handles arbitrary adaptive queries and arbitrary output selection.
This lifting is classical: Chou's factor-two optimality is explicitly
reproduced in
[Traub–Woźniakowski, §4.4, pp. 9–10](https://iiif.library.cmu.edu/file/Traub_box00014_fld00017_bdl0004_doc0001/Traub_box00014_fld00017_bdl0004_doc0001.pdf).
Its use here is credited as an adaptation, not a new lower-bound framework.
The [final bridge](../Proofs/HiddenDecompositionLowerBound.lean) connects
the witness to actual `execute` and to the setup's admissibility conditions.

## Natural nonlinear instances and limitations

One motivating family is a directed interaction game with scalar-player
costs
\[
c_i(x)=a_i(x_i)+\sum_{j\ne i}w_{ij}\log\cosh(x_i-x_j),\qquad w_{ij}\ge0.
\]
Write \(q_{ij}=(w_{ij}+w_{ji})/2\),
\(d_{ij}=(w_{ij}-w_{ji})/2\), and
\(r=\max_i\sum_{j\ne i}|d_{ij}|\).
The own-gradient field decomposes into the gradient of
\(\sum_i a_i(x_i)+\sum_{i<j}q_{ij}\log\cosh(x_i-x_j)\) and a residual
with Lipschitz constant at most \(2r\).
If \(\mu+r\le a_i''\le a_{\max}\), the full field is
\(\mu\)-strongly monotone and the potential has smoothness at most
\(a_{\max}+2\max_i\sum_{j\ne i}q_{ij}\).
These bounds follow from the symmetric and skew parts of the Jacobian:
the residual's off-diagonal entries are skew, its diagonal is bounded below
by \(-r\), and its row and column absolute sums are at most \(2r\).
This supplies interacting nonlinear examples in arbitrary finite dimension;
the estimates do not insert an additional dimension factor. This example
calculation is explanatory and is not a separate formalized application
theorem.

The principal unresolved gap is the upper conditioning logarithm.
Randomized lower bounds, noisy oracles, richer derivative access, and the
public-partition saddle-point question are outside this result.

The literature check used UTC 2026-10-20, screened the publicly available
2025/2026 ICML, ICLR and NeurIPS editions and roughly two years of arXiv
submissions/revisions, then followed older primary results. This was not
an exhaustive theorem-level reading of those proceedings. Candidate-specific
versions and theorem references are given above. Original full texts of
Chou (1987) and Nemirovski (1992) could not be accessed; the relevant
classical lifting was checked through the accessible primary reproduction
and related primary sources. The novelty claim concerns the explicit
uniform separation and nonlinear guarantee, not the absence of a search hit.
