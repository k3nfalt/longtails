# Variance reduction from symmetric first-moment gradient noise

The [Lean theorem](MedianFirstMomentNonconvex.lean) gives an expected-stationarity guarantee for general smooth nonconvex objectives with stochastic gradients whose variance may be infinite. Its distinguishing condition is **first-moment continuity of the centered noise**, combined with symmetry of each coordinate's marginal distribution. Coordinatewise medians of three paired samples turn this into second-moment continuity suitable for variance reduction.

The [setup](../Setups/SymmetricFirstMomentNonconvex.lean) and [algorithm](../Algorithms/MedianGradient.lean) cover arbitrary finite dimension and general nonlinear objectives. The setup imposes no algorithm-family restriction.

## Problem, information, and guarantee

Let \(f:\mathbb R^d\to\mathbb R\) have an \(L\)-Lipschitz gradient, \(L>0\), and let \(f(x_0)-f(x)\le\Delta\) for every \(x\). Write \(\zeta(x,\xi)=g(x,\xi)-\nabla f(x)\). The jointly measurable oracle is integrable and unbiased, with

\[
\mathbb E\|\zeta(x,\xi)\|\le\sigma,\qquad
\mathbb E\|\zeta(x,\xi)-\zeta(y,\xi)\|\le\Lambda\|x-y\|.
\]

For each fixed \(x\) and coordinate \(j\), \(\zeta_j(x,\xi)\) and \(-\zeta_j(x,\xi)\) have the same law. Coordinates need not be independent. Neither joint symmetry of the whole stochastic field nor symmetry of paired differences is assumed. No density, moment of order greater than one, finite variance, bounded gradient, or samplewise Lipschitz bound is required.

One query supplies \((g(x,\xi),g(y,\xi))\) with a fresh IID sample shared between the endpoints. The sampling law is an abstract probability measure satisfying the repository's IID structure; product representations are derived internally. The algorithm knows \(L,\Lambda,\sigma,\Delta,\varepsilon,x_0\), but not objective gradients or latent samples. Here \(\Lambda,\sigma,\Delta\ge0\) and \(\varepsilon>0\).

Define

\[
R=1+\log_2\!\left(2+\frac{16L\Delta}{\varepsilon^2}\right),\qquad
N=3\left\lceil14400R^2\left(
1+\frac{L\Delta+\sigma^2}{\varepsilon^2}
+\frac{\Lambda\sigma\Delta}{\varepsilon^3}\right)\right\rceil.
\]

The theorem proves

\[
\int \|\nabla f(x_{\rm out}(\omega))\|\,dP_{\rm execution}(\omega)\le\varepsilon.
\]

**\(N\) counts paired oracle queries.** Each pair evaluates two stochastic gradients, so execution uses \(2N\) gradient evaluations, including padding after the useful iterates are formed. Each median reply costs three paired queries, hence six gradient evaluations. This is an oracle-complexity upper bound, not a bit-complexity, high-probability, or optimality claim.

## Algorithm and new mechanism

For independent samples \(\xi_0,\xi_1,\xi_2\), form a coordinatewise median

\[
\widetilde g(x)=\operatorname{med}\{g(x,\xi_0),g(x,\xi_1),g(x,\xi_2)\},
\]

reusing the triple at \(y\). Marginal symmetry makes this estimator unbiased. Apply the existing normalized dyadic variance-reduction method to this oracle, using step length \(\eta=\varepsilon/(4L)\), \(K=\lceil16L\Delta/\varepsilon^2\rceil\), and a uniformly selected output among \(x_0,\ldots,x_K\). Anchor/difference batches use the explicit existing tcfg formulas with

\[
M=18\Lambda\sigma,\quad \nu=\tfrac12,\quad \sigma_{\rm VR}=2\sigma.
\]

More explicitly, set

\[
J=\max\!\left(\{0\}\cup
 \{j\in\mathbb N:j\le\lfloor\log_2(K+1)\rfloor,
       18\Lambda\sigma\,2^j\eta\le4\sigma^2\}\right),
\]

\[
b_A=\left\lceil128\sigma^2/\varepsilon^2\right\rceil+1,
\qquad
b_j=\left\lceil576(J+1)\Lambda\sigma\,2^j\eta/\varepsilon^2\right\rceil+1.
\]

An anchor is formed every \(2^J\) iterations. At other iterations, the estimate uses the predecessor \(k-2^{v_2(k\bmod2^J)}\) and a paired-difference batch of size \(b_{v_2(k\bmod2^J)}\). The explicit fallback \(J=0\) covers the case where no level passes the inequality. All tuning depends only on public inputs. The factor two upper-bounds \(\sqrt3\); it is not an extra oracle assumption.

The key dimension-free coupling inequality for coordinatewise median \(m\) is

\[
\begin{aligned}
\|m(a,b,c)\|^2&\le\|a\|\|b\|+\|b\|\|c\|+\|c\|\|a\|,\\
\|m(a,b,c)-m(a',b,c)\|^2&\le\|a-a'\|\|b-c\|.
\end{aligned}
\]

For a scalar, median is projection onto the interval between its other two inputs. The change is bounded by both input displacement and interval width. Summation and Cauchy–Schwarz yield the vector inequality. Independence then gives

\[
\mathbb E\|\widetilde g(x)-\nabla f(x)\|^2\le3\sigma^2,
\]

\[
\mathbb E\|[\widetilde g(x)-\nabla f(x)]-
[\widetilde g(y)-\nabla f(y)]\|^2
\le18\Lambda\sigma\|x-y\|.
\]

The second bound uses three replacements and full triple independence, including mixed-endpoint terms. Integrability is proved before unbiasedness is used. See [MedianCoupling](../Proofs/MedianCoupling.lean) and [MedianOracleMoments](../Proofs/MedianOracleMoments.lean).

This is a **centered noise** bound. Deterministic gradient differences cannot simply be absorbed into a global half-Hölder bound. [CenteredDyadicMoments](../Proofs/CenteredDyadicMoments.lean) and [CenteredDyadicDescent](../Proofs/CenteredDyadicDescent.lean) prove the required centered version, reusing existing batching, trajectory, and normalized-descent lemmas. [MedianConvergence](../Proofs/MedianConvergence.lean) connects actual batched execution and IID triples and proves the simplified public budget. The existing dyadic method and its logarithmic overhead are not claimed as new.

## Closest results and improvements

The contribution is coupled-endpoint regularization and the resulting \(\widetilde O(\varepsilon^{-3})\) complexity under first moments. Unbiased median aggregation and marginal variance repair are established ideas.

- [Puchkin et al., AISTATS 2024](https://proceedings.mlr.press/v238/puchkin24a.html), Proposition 4.1 and Corollary 5.3, use coordinate medians under symmetric density/tail-envelope conditions. Their median variance argument does not supply the paired spatial bound. Ordinary SGD after marginal variance repair yields the nonconvex stochastic term \(L\Delta\sigma^2/\varepsilon^4\).
- [Vukovic and Jakovetic, arXiv:2605.07634v1](https://arxiv.org/html/2605.07634v1), Assumption 2 and Theorems 2–3, analyze medoids with absolute continuity, joint symmetry, and finite \(p>1\) moments; their nonconvex SGD stationarity exponent is four. We remove those density/higher-moment restrictions and use coordinate symmetry, while **adding spatial coupling**. These classes are not nested. The median replacement inequality cannot automatically be assigned to discontinuous medoid selection.
- [Armacki et al., arXiv:2507.09093v2, February 10, 2026](https://arxiv.org/html/2507.09093v2), Assumption 2, Theorem 1 and Corollary 2, allow state-dependent symmetric densities uniformly positive near zero and obtain high-probability nonlinear-SGD guarantees without our moment/coupling conditions. Their stationarity exponent is four. Our expected guarantee adds first-moment/coupling restrictions and removes the density requirement; it does not dominate their scope or confidence guarantee.
- [Fradin et al., arXiv:2512.18713v2, March 31, 2026](https://arxiv.org/html/2512.18713v2), Assumption 2.7 and Theorem 4.2, study centered \(q\)-moment similarity and bounded \(p>1\) central moments. Our spatial condition is their \(q=1\) similarity. Their stochastic term is \(\Lambda\Delta\varepsilon^{-2}(\sigma_p/\varepsilon)^{p/[q(p-1)]}\), alongside initialization/deterministic terms. At \(p=2,q=1\), the exponent is four; the generic guarantee deteriorates as \(p\downarrow1\). We additionally exploit symmetry and reach the first-moment endpoint. Their nonsymmetric lower bounds do not apply here.
- [Shulgin et al., ICML 2026, “Understanding MARS”](https://proceedings.mlr.press/v306/shulgin26b.html), Theorem 1, already uses centered second-moment similarity. Our raw oracle need not satisfy it. Merely changing raw to centered smoothness is not the contribution.
- The repository's [DyadicVarianceReductionHolder](DyadicVarianceReductionHolder.md) already gives an \(\varepsilon^{-3}\) rate for finite-variance raw mean-squared Hölder oracles. It cannot directly cover this model. The median bridge supplies the centered condition; the centered dyadic extension is supporting analysis.

For fixed positive \(\sigma,\Lambda\), the stochastic leading term improves from \(L\Delta\sigma^2\varepsilon^{-4}\) after median-SGD preprocessing to \(\widetilde O(\Lambda\sigma\Delta\varepsilon^{-3})\). This matters when these terms dominate initialization/deterministic terms and \(\varepsilon\) is below \(L\sigma/\Lambda\), allowing for the displayed logarithmic factor. Large \(\Lambda/L\), coarse accuracy, or initialization can erase the advantage. The budget retains remaining terms at \(\Lambda=0\) and \(\sigma=0\); it is not claimed sharp in every degenerate regime.

## Reduction checks and nonlinear instances

Joint sign symmetry of the entire noise field makes differences symmetric, permitting direct robust median-difference constructions. Common additive heavy-tailed noise admits robust anchor estimation. Known finite-rank affine noise can sometimes be canceled with finitely many anchors. Dithering a deterministic gradient already yields finite-second-moment Hölder increments. None of these simpler examples establishes the claimed contribution.

Fixed coordinatewise clipping at threshold \(B\) also makes increments square-integrable: \(\mathbb E\|T_Bg(x)-T_Bg(y)\|^2\le2B\sqrt d(L+\Lambda)\|x-y\|\). Its mean is generally not \(\nabla f\); marginal symmetry supplies alignment rather than exact unbiasedness. Applying an unbiased-gradient dyadic theorem is therefore invalid. A separate biased-field analysis may yield related exponents with other parameter or dimension dependence; no impossibility claim for clipping is made. The median bridge preserves unbiasedness and gives \(18\Lambda\sigma\) without a clipping threshold, additional dimension factor, or deterministic \(L\) term.

A broader illustrative family is fixed-precision quantization of state-dependent heavy-tailed stochastic gradients. Let \(T\) be a continuously distributed frequency with \(\|T\|\le1\), and let independent symmetric \(Z\) satisfy \(\mathbb E|Z|<\infty\), \(\mathbb E Z^2=\infty\). Consider losses

\[
f(x)+Z\cos\langle T,x\rangle.
\]

Apply coordinatewise lattice quantization of step \(h\) with independent subtractive uniform dither \(U\), sharing \(Z,T,U\) across endpoints. A decoder may know \(U\); the algorithm ignores it and does not access unquantized gradients. The centered oracle has coordinate symmetry and

\[
\sigma\le\mathbb E|Z|+h\sqrt d/2,\qquad
\Lambda\le\sqrt d(L+\mathbb E|Z|)+L.
\]

The latter follows from \(\mathbb E_U|Q_h(a+U)-Q_h(b+U)|=|a-b|\) and comparison of one- and two-norms. Application dimension dependence is explicit; the theorem adds none beyond its parameters.

For a nonlinear interacting objective in every dimension, take

\[
f(x)=\tfrac12\|x\|^2+\kappa\sum_{i=1}^d[1-\cos(x_i+x_{i+1})],
\qquad x_{d+1}=x_1,\quad\kappa>1/4.
\]

It is lower bounded, \(L\le1+4\kappa\), and has negative curvature at the vector whose coordinates equal \(\pi/2\). If a random-feature gradient increment is nonzero with positive probability, its raw paired second moment is infinite: bounded quantization error cannot remove the heavy tail. A coordinate of a quantized pair difference lies in \(h\mathbb Z\). When its mean is \(h/4\), centered support and reflected support are disjoint. Pointwise symmetry therefore does not ensure difference symmetry.

This is an illustrative family, not an established benchmark claim. [UVeQFed](https://arxiv.org/abs/2006.03262) independently motivates subtractively dithered gradient communication; it does not analyze this exact heavy-tailed model. The lattice is unbounded, so no fixed-bit guarantee is claimed. Quantizing differences at the encoder or changing precision changes oracle access. We do not rule out more sophisticated calibration for particular latent models or claim lower bounds for this application.

## Literature coverage and limitations

The literature check used October 18, 2026 UTC. Researcher and Reviewer independently screened ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2024/2025 through official proceedings/OpenReview, plus approximately two years of arXiv submissions/revisions and relevant older references. ICML 2026 MARS status was checked in PMLR; the 2026 medoid work is cited as an arXiv preprint. Some direct OpenReview/NeurIPS virtual pages were inaccessible; official proceedings and primary arXiv versions supplied relevant theorem texts. Search coverage is not proof of novelty.

Open questions include optimality, removal of dyadic logarithms, adaptation to unknown parameters, and quantitatively controlled asymmetry. Coordinate medians are basis-dependent. The application/comparison calculations explain scope; Lean formalizes the general oracle guarantee, not a quantizer implementation or a literature novelty assertion.
