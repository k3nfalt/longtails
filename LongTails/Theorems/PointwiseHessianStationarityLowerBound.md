# Oracle complexity under pointwise Hessian growth

The [lower theorem](PointwiseHessianStationarityLowerBound.lean) and its [upper counterpart](PointwiseHessianStationarity.lean) characterize the polynomial oracle complexity of first-order stationarity for general nonconvex objectives with gradient-dependent third derivatives. The new mathematical claim is the lower bound, especially its dependence on the relative-growth parameter. The upper theorem transfers an existing algorithm to exactly the same joint oracle and expected-accuracy specification; it is not claimed as a new algorithm or rate.

## Problem and precise bounds

The single [setup file](../Setups/PointwiseHessianStationarity.lean) defines `broadSpec` and the canonical `spec`. For arbitrary finite dimension, the objective is a real-valued C³ function on Euclidean space, with

\[
f(0)-f(x)\le\Delta,\qquad
\|D^3f(x)\|\le L_0+L_1\|\nabla f(x)\|\quad\text{for every }x,
\qquad \|\nabla f(0)\|\le G.
\]

Here \(L_0,L_1\ge0\), \(L_0+L_1>0\), and \(\Delta,\varepsilon>0\). There is no convexity, globally bounded Hessian, bounded domain, or bounded-query restriction. One call returns the full value, gradient and Hessian at any chosen point. The algorithm knows the displayed parameters and dimension. All adaptive randomized algorithms and output rules are permitted; `allowedAlgorithm` imposes no method restriction. Success requires a measurable output, integrability of its gradient norm, and \(\mathbb E\|\nabla f(X)\|\le\varepsilon\).

Write
\[
S=\frac{\Delta\sqrt{L_0+L_1\varepsilon}}{\varepsilon^{3/2}},\qquad
B=\left\lceil\frac{\log(1+L_1G/(L_0+L_1\varepsilon))}{\log(4/3)}\right\rceil.
\]

* The upper supporting guarantee, under `broadSpec`, is \(\lceil100000S\rceil+2B+200\) joint calls, with deterministic gradient-norm accuracy, hence also the stated expected accuracy.
* For the common public `spec`, assume additionally \(G\ge16\varepsilon\), \(S\ge2^{39}\), and \(d\ge2^{140}(1+\lceil S\rceil)^4\). For every algorithm and every integer budget \(0\le b\le\lfloor S/2^{39}\rfloor\), a fixed admissible objective defeats the expected-accuracy guarantee at that budget. The objective may depend on the algorithm and budget, but not its realized seed.

Since \(\sqrt{L_0+L_1\varepsilon}\) lies between the maximum and sum of \(\sqrt{L_0}\) and \(\sqrt{L_1\varepsilon}\), the polynomial rate is
\[
\Theta\!\left(\Delta\sqrt{L_0}\,\varepsilon^{-3/2}
+\Delta\sqrt{L_1}\,\varepsilon^{-1}\right).
\]
Both public results use this same nontrivial regime as their canonical `spec`, as required by the repository audit interface. The upper proof module additionally establishes the broader `broadSpec` guarantee without the dimension, S or G≥16ε restrictions. Thus those restrictions are not necessary for the upper algorithm. The remaining discrepancy is the displayed additive logarithm and universal constants. This is a high-dimensional oracle-complexity statement, not a fixed-dimensional minimax characterization. The large universal constants were chosen for transparent formal estimates; no numerical usefulness is claimed. No hardness is claimed when the initial point already guarantees accuracy, in particular when \(G\le\varepsilon\). `pure_relative_nonempty` in [the tuning module](../Proofs/RelativeHessianTuning.lean) verifies a nonempty regime with \(L_0=0,L_1=1\).

## Closest results and what changes

[Fang, Marumo and Takeda, arXiv:2607.10741v1](https://arxiv.org/html/2607.10741v1), Assumption 1(a,b), studies this pointwise third-derivative condition and finite initial gap with full second-order queries. Corollary 1, equation (130), gives a parameter-free upper bound for gradient and curvature tolerances \((\varepsilon,\delta)\). Section 7 explicitly asks whether its \(\Delta\sqrt{L_1}/\varepsilon\) and \(\Delta L_1/\delta\) terms are necessary. The present lower bound resolves the former question for expected first-order stationarity in the stated high-dimensional regime. It does not resolve the independent curvature-tolerance term. Their assumption takes \(L_0>0\); the specification also includes \(L_0=0\). Their paper is a preprint, not represented here as an accepted conference paper.

[Carmon, Duchi, Hinder and Sidford, *Lower Bounds for Finding Stationary Points I*, arXiv:1710.11606v3](https://arxiv.org/abs/1710.11606v3), Theorem 2 and the randomized construction in Section 5, establish the classical Lipschitz-derivative lower bound. Taking derivative order two supplies the \(\Delta\sqrt{L_0}\varepsilon^{-3/2}\) term. That result permits even stronger derivative information, but its uniform derivative bound alone supplies no positive relative-growth term when \(L_0=0\). Its constant-probability hardness at a constant multiple of ε also obstructs expected ε accuracy by the elementary norm-expectation bound. Their classical randomized construction uses sufficient dimension of order the squared complexity scale times a logarithm. Our fourth-power dimension requirement is weaker in this respect. The classical term and the use of robust chains are not new claims here.

The repository already contains [EnergyHessianReuse](EnergyHessianReuse.lean), introduced in [PR #16](https://github.com/k3nfalt/longtails/pull/16), with an upper bound under the same pointwise growth condition and separate gradient/Hessian channels. The companion upper theorem uses that method at reuse length one, replaces its positive absolute parameter by \(L_0+L_1\varepsilon\), and pays one joint call for every old channel call. This is a proved standard reduction, with all output-selection and initialization costs retained. It does not assert the parameter-free adaptivity of Fang–Marumo–Takeda: the formal algorithm uses the public parameters.

The lower bound is newly informative when \(L_1\varepsilon\gg L_0\), where the classical term is smaller by a factor comparable to \(\sqrt{L_1\varepsilon/L_0}\). It also covers the pure relative-growth boundary. Setting a classical Hessian-Lipschitz constant to \(L_1\varepsilon\) is not a valid lower-bound reduction: the global relative condition must hold at points with gradient norm below \(\varepsilon\), including stationary points. Adding a generic quadratic guard to an ordinary chain can create a stationary point with nonzero third derivative, violating that condition. Batching, clipping or an upper-bound composition does not repair this hard-instance defect.

## New construction and proof mechanism

The hard instances are nonlinear chains with interacting adjacent coordinates, a common quadratic guard, and a compact radial cutoff. The key scalar profile is \(\Phi(t)=\pi/2+\arctan t\), with \(q(t)=\Phi'(t)=1/(1+t^2)\) and \(a=3\sqrt3/4\). The factorization
\[
at-q(t)=a(t-1/\sqrt3)\frac{t^2+t/\sqrt3+4/3}{1+t^2}
\]
places the zero of the guarded gradient at a zero of \(q''\). [RelativeHessianArctan](../Proofs/RelativeHessianArctan.lean) proves \(|q''(t)|\le12|at-q(t)|\).

A monotone C³ gate is zero below \(1/10\) and one above \(1/5\). The signed chain has nonpositive gradient contributions. If a coordinate has small magnitude, its first such occurrence has an active predecessor and gradient component at most \(-0.7\), even after the guard. If every coordinate has large magnitude, all gate derivatives vanish and the third derivative is diagonal; the scalar cancellation estimate then controls its operator norm by the full gradient norm. Bounded overlap of adjacent links makes the absolute third-derivative bound independent of chain length. The actual multivariate gradient and tensor calculations are in [Geometry](../Proofs/RelativeHessianGeometry.lean), [FirstSmall](../Proofs/RelativeHessianFirstSmall.lean) and [JetBounds](../Proofs/RelativeHessianJetBounds.lean).

For \(N\) coordinates, use radius \(R=2^{60}N\) and multiply the chain, but not its quadratic guard, by \(\chi(\|x\|^2/R^2)\). The resulting function \(F\) satisfies globally
\[
F(0)-F(x)\le4N,\quad \|\nabla F(0)\|=1,\quad
\|D^3F(x)\|\le2^{56},\quad
\|D^3F(x)\|\le2^{56}\|\nabla F(x)\|.
\]
Outside radius \(R\), the guard dominates the cutoff perturbation. Outside radius \(2R\), the full oracle reply is a common quadratic reply. Boundary jets are checked explicitly, rather than inferred from equality on a closed ball. [Localized](../Proofs/RelativeHessianLocalized.lean) proves these global facts; [Oracle](../Proofs/RelativeHessianOracle.lean) proves exact joint-reply hiding.

At each budget \(b\), choose \(N=2(b+1)\), frequency \(\beta=\sqrt{L_0+L_1\varepsilon}/(2^{30}\sqrt\varepsilon)\), and amplitude \(A=16\varepsilon/\beta\). The scaled objective \(AF(\beta x)\) has initial gradient norm \(16\varepsilon\). Combining its absolute and relative third-derivative estimates gives the required \(L_0+L_1\|\nabla f\|\) bound everywhere; this compatibility is the essential new mechanism.

The remaining information argument reuses existing finite coordinate-exposure and averaging tools. It is not claimed as independently novel. A finite injection of hidden coordinate axes produces a fixed family. Prefix simulation handles every adaptive query and the final arbitrary output. At least three quarters of the family remains hidden under the stated dimension bound, and a hidden output has normalized gradient norm at least \(0.7\). A finite-sum/integral contradiction selects one objective independent of the seed. No measurability of intermediate queries is assumed: if all fixed-instance outputs succeeded, their error integrability alone would justify the finite averaging. [LowerBound](../Proofs/RelativeHessianLowerBound.lean), [Instance](../Proofs/RelativeHessianInstance.lean) and [Hardness](../Proofs/RelativeHessianHardness.lean) connect this argument to actual `OracleTemplate.execute`.

## Naturalness, scope and limitations

The problem is the established nonconvex stationarity question with full Hessian access. The growth assumption replaces a uniform third-derivative bound with a pointwise allowance for growing curvature. It is imposed on every admissible objective, independently of the construction. The quadratic guard, gates and cutoff are features of hard instances, not restrictions on the problem class or algorithms.

For a concrete interacting nonlinear family, let \(A\) be invertible with \(\|A\|\le M\) and smallest singular value at least \(s>0\), and consider
\[
f(x)=\tfrac14\|A(x-u)\|^4+c\cos\langle v,x-u\rangle,\qquad c\ge0.
\]
Dense \(A\) couples coordinates. When \(c>0\) and \(v\ne0\), the Hessian at \(x=u\) has a negative direction, so the objective is nonconvex. Put \(r=\|x-u\|\), \(V=\|v\|\). Direct differentiation yields \(\|D^3f(x)\|\le6M^4r+cV^3\) and \(s^4r^3\le\|\nabla f(x)\|+cV\). For any \(L_1>0\), maximizing \(6M^4r-L_1s^4r^3\) gives the valid choice
\[
L_0=4\sqrt2 M^6/(s^2\sqrt{L_1})+cV^3+L_1cV.
\]
The function is bounded below and admits initial gap at most \(\|Au\|^4/4+2c\). These bounds have no implicit dimension factor. This example explains the objective class; it is not used as a substitute for the chain hardness proof.

The public bound G only controls the initial gradient, whose size also enters the baseline initialization logarithm; it is not a global gradient bound. The extra lower-regime conditions concern accuracy, initial-gradient allowance and sufficient dimension. They are explicit proof regimes, not asserted necessary for the class. Reducing the dimension, constants or \(G/\varepsilon\) threshold is not established. The theorem does not address stochastic derivative noise, Hessian-vector-only costs, third-order oracle access, or second-order stationarity. No constant-success versus expected-accuracy substitution is made.

Literature and PR screening was conducted as of 2026-11-17 UTC, covering the public 2025/2026 ICML, ICLR and NeurIPS catalogues, roughly November 2024–November 2026 arXiv submissions/revisions, and older cited baselines. Both agents independently searched before selection. The closest preprint was checked at its available v1; the classical lower-bound source at v3. The search also checked later higher-order finite-sum, Hessian/gradient-tradeoff and minimax results, whose models differ. Open and closed repository PRs were checked, including #16, #19, #66, #119, #145 and #167. No matching closure was located. This is targeted primary-source coverage, not a claim of exhaustive priority certification. The closest primary sources were accessible; no critical comparison is based solely on an inaccessible theorem.
