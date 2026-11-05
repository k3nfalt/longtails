# Accelerated Wasserstein proximal gradient with ordinary JKO solves

The [Lean result](WassersteinAcceleratedProximal.lean) concerns minimization of
\(G(\mu)=\int V\,d\mu+H(\mu)\) on probability measures with finite second moment
in arbitrary finite dimension. Its [setup](../Setups/WassersteinSmoothComposite.lean)
and [algorithm](../Algorithms/WassersteinAcceleratedProximal.lean) distinguish the
hidden objective from the available population operations.

## Problem and oracle model

The potential \(V:\mathbb R^d\to\mathbb R\) is convex, differentiable, and has an
\(L\)-Lipschitz gradient, with \(L>0\). The finite-value domain \(Q\) of \(H\)
consists of absolutely continuous measures. Generalized-geodesic convexity has
its selected-plan meaning: for every base measure and two endpoints in \(Q\),
there exists one joint plan with optimal base-to-endpoint marginals whose entire
interpolation stays in \(Q\) and satisfies the convexity inequality. This does
not require convexity along arbitrary couplings. A minimizer \(\mu_\star\in Q\)
exists, \(\mu_0\in Q\), and \(W_2(\mu_0,\mu_\star)^2\le R^2\).

These are the smooth-potential and regular-domain assumptions used in
[Di Marino–Naldi–Villa, arXiv:2505.23517v2, Definition 2.9 and Section 4](https://arxiv.org/html/2505.23517v2).
Here the oracle explicitly supplies actual finite proximal minimizers; lower
semicontinuity is consequently unnecessary for the conditional convergence
implication. This omission is not a new wellposedness theorem. Absolute
continuity is a standard sufficient regularity condition; the algebra itself
uses the certified transport maps supplied by the oracle.

The oracle accepts a requested step size, positive for JKO queries. The
algorithm chooses \(h=1/(2L)\). The operations are:

1. The forward law \((\operatorname{Id}-h\nabla V)_\#\mu\).
2. An ordinary JKO minimizer of \(H(\rho)+W_2(\rho,\nu)^2/(2h)\) over \(Q\).
3. An optimal transport map from a source in \(Q\) to a specified target.

Forward and JKO replies contain only the resulting law. They do not reveal the
whole gradient field or objective. Transport replies certify their endpoints,
measurability, pushforward, and finite cost; admissibility requires optimality
against all actual couplings. Correctness is exact at every history and seed.
The public parameters are \(d,L,R,\varepsilon,\mu_0\); the objective, domain,
and minimizer remain hidden. This algorithm uses only \(d,L,\mu_0\) in its
updates; \(R,\varepsilon\) determine the execution budget and are also available
for competing algorithms to tune their queries.
There is no restriction on competing algorithms in the specification.

The result is conditional on these oracles existing for every requested positive
step size, not just the step used by this algorithm. This availability permits
competing algorithms to choose their own tuning. It neither constructs a
numerical JKO/OT solver nor bounds particle, sample, point-gradient, or arithmetic
complexity. Extrapolated and forward laws may be singular. Only the initial and
proximal-output laws must lie in \(Q\).

## Algorithm and guarantee

The first iterate is one forward operation followed by one JKO operation.
For \(k\ge1\), obtain an optimal map \(A_k:\mu_k\to\mu_{k-1}\), and set
\[
 \beta_k=\frac{k-1}{k+2},\qquad
 y_k=((1+\beta_k)\operatorname{Id}-\beta_k A_k)_\#\mu_k,\qquad
 \mu_{k+1}=\operatorname{JKO}_{hH}\bigl((\operatorname{Id}-h\nabla V)_\#y_k\bigr).
\]
The returned output is the last completed proximal iterate. The bound is
\[
 G(\mu_k)-G(\mu_\star)\le\frac{4LR^2}{(k+1)^2},\qquad k\ge1.
\]
For \(\varepsilon>0\), the public theorem uses
\(K=1+\lceil2R\sqrt{L/\varepsilon}\rceil\), with the single explicit pooled budget
\[
 2+3\lceil2R\sqrt{L/\varepsilon}\rceil=3K-1.
\]
Execution uses exactly \(K\) forward operations, \(K\) JKO operations, and
\(K-1\) OT operations. The implementation still requests the transport at
\(k=1\), where the momentum coefficient is zero. When \(R=0\), the budget still
performs the initial two operations. The setup expresses almost-sure feasible
output and objective accuracy; the proof establishes the bound for every seed
sequence under the universal exact-oracle contract.

## Mechanism and contribution

The split variational inequality is established from actual proximal minimality,
generalized-geodesic convexity, and the smooth potential assumptions:
\[
 2h(G(u)-G(v))\le W_2(y,v)^2-W_2(u,v)^2-(1-hL)W_2(y,u)^2.
\]
This inequality is already known: see
[Di Marino–Naldi–Villa, Lemma 4.2](https://arxiv.org/html/2505.23517v2#S4).
The formal proof derives it rather than assuming it. In particular, the forward
map has a continuous inverse for \(hL<1\); pulling an optimal coupling through
that inverse justifies the smooth-cost cancellation even for singular inputs.

The acceleration argument uses \(t_k=(k+1)/2\) and the potential
\[
 P_k=2ht_k^2(G(\mu_k)-G_\star)+t_kW_2(\mu_k,\mu_\star)^2
 -(t_k-1)W_2(\mu_{k-1},\mu_\star)^2
 +t_k(t_k-1)W_2(\mu_k,\mu_{k-1})^2.
\]
Two optimal maps from the current law provide a common-base squared-norm
identity. The induced coupling of their targets need not be optimal: its cost
is used only as an upper bound on the corresponding squared Wasserstein
distance, with the correct negative coefficient. This proves both the
extrapolation bound and nonnegativity of the distance part of \(P_k\).
Weighted applications of the split inequality give descent; the linear weight
schedule leaves an additional nonpositive multiple of the old objective gap.
Initialization gives \(P_1\le R^2\).

The substantive claim is an accelerated discrete optimization guarantee using
ordinary \(H\)-JKO solves and inter-iterate OT maps. The new contribution is not
the forward–backward inequality, free-flow extrapolation by itself, the
\(k^{-2}\) exponent in a different oracle model, or its Lean formalization.

## Closest comparisons and limitations

- [Salim–Korba–Luise, arXiv:2002.03035v3, Theorem 9 and Corollary 10](https://arxiv.org/html/2002.03035v3#S4.SS4)
  give ordinary Wasserstein proximal-gradient gap \(R^2/(2\gamma k)\), with
  \(\gamma<1/L\), without an inter-iterate OT operation. The present result
  improves its dependence on accuracy from \(\varepsilon^{-1}\) to
  \(\varepsilon^{-1/2}\) in population operation counts, while adding OT solves.
  It does not uniformly dominate that baseline in runtime or at coarse accuracy.
- [Ushiyama et al., arXiv:2611.03524v1, Theorems 8 and 12](https://arxiv.org/html/2611.03524v1)
  already obtain accelerated rates using a proximal oracle on a fixed-reference
  cone of optimal maps. That oracle is not an ordinary JKO oracle. The present
  guarantee changes the required proximal operation and uses a moving reference;
  its smooth term is restricted to a convex smooth potential integral. It does
  not improve the best exponent available with the different fixed-reference cone-proximal oracle,
  nor cover every smooth functional treated there.
- [Gallouët–Natale–Todeschi, arXiv:2209.14622v3, Section 4.1 and Proposition 4.3](https://arxiv.org/html/2209.14622v3)
  already study free-flow extrapolation. Their Theorem 1.3 concerns convergence
  of a BDF2 time discretization to an EVI flow, not the above split-oracle
  accelerated optimization bound.
- [Chang–Iyadomi–Wang, author-hosted preprint](https://taroiyadomi.netlify.app/pdfs/Accelerated_Proximal_Optimization_in_Wasserstein_and_Sobolev_Spaces.pdf)
  studies accelerated proximal optimization using a proximal operation for the
  whole objective. It does not supply the same split oracle guarantee. Its
  arbitrary-map convexity step is not used here: the present proof retains the
  selected-plan distinction and the coupling-cost inequality. The retrieved PDF
  has no verified conference acceptance status or arXiv version identifier.

For an explicit cost comparison, put \(T=LR^2/\varepsilon\), and let operation
costs be \(c_F,c_J,c_{OT}\). Our bound costs
\(K(c_F+c_J)+(K-1)c_{OT}\). A strongest-step ordinary WPG comparison can take
\(n=\lfloor T/2\rfloor+1\) and
\(\gamma=(1+T/(2n))/(2L)<1/L\), costing \(n(c_F+c_J)\).
These formulas permit a finite-parameter comparison without dropping rounding.
In leading order as the baseline step approaches \(1/L\), improvement requires
\(\sqrt T>4(1+c_{OT}/(c_F+c_J))\); equal unit operation costs give the
leading-order crossover \(T>36\), not an exact rounded threshold. No adaptivity
improvement is claimed.

A nonquadratic family in arbitrary dimension is
\(V(x)=a\|x\|^2/2+b\sum_j\log\cosh((Bx)_j)\), with \(a>0,b\ge0\), a dense matrix \(B\), and
\(H\) equal to entropy with coefficient \(\tau>0\) plus an even convex interaction
energy with coefficient \(\lambda>0\), for
example one generated by \(\sqrt{1+\|C(x-y)\|^2}\). The Lipschitz constant is at
most \(a+b\|B\|^2\). Dense matrices and the interaction term couple coordinates;
this is not a scalar or quadratic theorem. The standard regularity and
wellposedness facts for these examples are mathematical motivation, not additional
example formalizations. Dimension enters through problem constants and the costs
of the population operations, not an extra factor in the iteration bound.

The targeted literature search included official proceedings and OpenReview
queries for the two latest publicly available editions of ICML, ICLR, and
NeurIPS as of 2026-11-05, recent arXiv work and revisions, and older foundational
results. This was not an exhaustive theorem-level review of every conference
paper. The OpenReview page WPz5e5V85k was inaccessible to browser verification;
no acceptance status is inferred from it. The 2025–2026 arXiv comparisons above are preprints,
not asserted accepted conference papers. The claim remains limited to the exact
oracle model and assumptions stated here; it does not establish optimality or a
lower bound, and it does not resolve numerical implementation costs.
