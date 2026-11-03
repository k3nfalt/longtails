# Ordinary-start convolutional perceptron acceleration on many samples

The result proves logarithmic dependence on inverse contrast for the actual cyclic, simultaneous two-tap quadratic perceptron, initialized with filter `(√2, 0)` and zero output weights. It permits arbitrarily many samples whose centered defects have a common separating direction after differencing. Their derivative directions need not lie in a small cap, and their pairwise inner products need not be positive.

This is a contribution about learned filter dynamics. It is not a new unrestricted oracle-complexity frontier, a finite-step logistic-gradient-descent theorem, or a claim of nonlinear expressivity in the input. The predictor is bilinear in its trained parameters and linear in its input.

## Specification, algorithm and guarantee

See the [Lean theorem](DerivativeConvolutionalPerceptronAcceleration.lean), [setup](../Setups/DerivativeConvolutionalPerceptron.lean), [algorithm and output](../Algorithms/DerivativeConvolutionalPerceptron.lean), and [execution guarantee](../Proofs/DerivativeConvolutionalPerceptronConvergence.lean). The setup's `samples` parameter is one less than the number of examples: write $N=\mathtt{samples}+1$.

Let $P$ be the cyclic coordinate shift in dimension $d\ge1$, and $e=d^{-1/2}\mathbf1$. Signed samples satisfy

\[
D_i=\frac{\alpha_i}{\sqrt2}e+\mu u_i,
\quad g\le|\alpha_i|\le R,
\quad \langle e,u_i\rangle=0,
\quad \|u_i\|\le\tfrac12.
\]

There exists a unit vector $w$ with

\[
\left\langle\frac{u_i-Pu_i}{\sqrt2},w\right\rangle\ge\kappa
\quad\text{for every }i.
\]

The parameter conditions are $0<g\le R$, $0<\kappa\le1$, and

\[
0<\frac\mu R\le 2^{-400}\kappa^{20}(g/R)^{24}.
\]

The oracle returns the exact signed margin and its full parameter gradient for one requested sample at one requested point. The decomposition, separator, and individual samples are not public inputs. Public inputs are the dimension, sample count and the four bounds $g,R,\mu,\kappa$. There is no random oracle, sampling assumption, or hidden distribution.

For filter $c=(c_0,c_1)$ and head $v\in\mathbb R^d$, the margin is

\[
f_i(c,v)=c_0\langle D_i,v\rangle+c_1\langle PD_i,v\rangle.
\]

Starting from $c=(\sqrt2,0),v=0$, cyclically query every sample. If its margin is nonpositive, update **both** filter and head by $\eta\nabla f_i(c,v)$, evaluated at the same old point; otherwise leave the point unchanged. Always advance the cursor. The constant step is

\[
\eta=\frac{\kappa^2g^2}{2^{40}R^3}.
\]

The last point after

\[
B=N\left(\left\lceil
\frac{2^{140}R^{10}}{\kappa^8g^{10}}
\left(1+\log\frac R\mu\right)
\right\rceil+1\right)
\]

oracle calls strictly separates every signed sample. This counts correct queries, mistaken queries and the final scan. There is no free search for a misclassified sample, uncounted certification, reference-sample call or directed perturbation. `output_separates` explicitly names this algorithm, its `execute` output and this budget. The public `result : Convergence spec budget` constructs that algorithm. The problem specification is unrestricted; it does not exclude faster competing algorithms.

For fixed $\kappa$ and $g/R$, the cost is $O(N\log(R/\mu))$. Dimension enters through these geometric parameters and $N$, not as an additional factor. The constants and sufficient contrast threshold are deliberately conservative; they do not establish a practical rate.

## What changes relative to prior results

[Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv v2, May 21, 2026](https://arxiv.org/abs/2512.11587v2), Theorems 5.1–5.2, establishes acceleration on the particular two-example dataset (5). The upper theorem uses a perturbed, prioritized two-sample quadratic perceptron, a nonzero initial eigendirection correlation, and a high-probability stopping bound. Its proof follows the interaction of two matrices. Section 6 extends the model representations and gives spectral bounds, rather than a many-sample convergence theorem. Theorem 2.1 is a limiting GD-to-perceptron reduction; it does not give the finite-GD guarantee omitted here.

Our derivative-separator condition excludes dataset (5)'s pure constant sample. Thus this theorem extends the phenomenon to a different many-sample class; it is not a literal instance-class superset of Theorem 5.1. It replaces that special geometry, perturbations and initialization condition with a deterministic cyclic algorithm and an explicit ordinary initialization, under the stated derivative margin and strong contrast condition.

The repository already has many-sample results, so neither sample count nor logarithmic contrast dependence alone is new:

| Closest repository result | Restriction or mechanism retained there | Change here |
| --- | --- | --- |
| [Clustered convolutional perceptron](ClusteredConvolutionalPerceptronAcceleration.lean) | Defects lie within radius $\kappa/64$ of a common center; initialization is biased toward differencing | Remove the cap and start from the raw one-tap filter; replace pointwise favorable Gram bounds with coupled energy control |
| [Many-sample convolutional perceptron](ManySampleConvolutionalPerceptronAcceleration.lean) | Pure reference sample and directed interventions | No reference sample, interventions or special update selection |
| [Cyclic full-width perceptron](CyclicFullWidthPerceptronAcceleration.lean) | Different full-width architecture and a small offset slab | Actual two-tap convolution and arbitrary centered derivative-separable defects |

These are not universal improvements over the earlier rates. This proof uses a smaller step and a stronger sufficient contrast threshold than the clustered analysis. On the shared norm and parameter regime it removes the cap. The norm normalization also differs: the earlier cap permits defects as large as $1/2+\kappa/64$, whereas this setup requires norm at most $1/2$. The complete parameterized instance classes are therefore not globally nested. The new mathematical claim is convergence of the unmodified coupled trajectory without cap positivity, a prepared filter, or corrective kicks.

Related continuous-time results do not provide this discrete count. [Yun, Krishnan and Mobahi, corrected arXiv v3](https://arxiv.org/abs/2010.02501v3), Corollaries 3–4, treats full-length convolutional gradient flow and a single-example short-filter case. [Diederen, Rauhut and Terstiege, arXiv v1](https://arxiv.org/abs/2601.08547v1), Theorems 3.4 and 3.8, uses loss/coercivity or full-rank regression conditions for convergence of convolutional gradient flow to critical points. Neither yields finite strict separation for this switched discrete trajectory. [Arora, Cohen and Hazan, ICML 2018](https://proceedings.mlr.press/v80/arora18a.html) already develops implicit acceleration through overparameterization; the general theme is not a novelty claim here.

## Why standard reductions do not prove this trajectory theorem

Differencing immediately removes the constant background. The normalized differenced samples have norm at most one and margin at least $\kappa$. Ordinary perceptron therefore takes $O(\kappa^{-2})$ mistakes, or $O(N/\kappa^2)$ cyclic sample inspections including certification. The smooth accelerated perceptron takes $O(\sqrt{\log(2N)}/\kappa)$ full-data rounds; see [Wang et al., arXiv v1](https://arxiv.org/html/2210.09371v1), Assumption 1, Algorithm 1 and Theorem 3 (also Theorem 4 for its accelerated ERM counterpart). Each round performs $O(N)$ component work, so it is not a single indexed oracle call. With stored samples this work needs no further oracle calls. Such preprocessing changes the learned trajectory and cannot establish that the prescribed ordinary-start simultaneous updates learn the useful filter.

The exact oracle makes the unrestricted comparison even clearer: at filter `(√2, 0)` and zero head, the head gradient is $\sqrt2D_i$. In $N$ queries one can recover all samples, then perform offline separation without additional oracle calls. Consequently the displayed budget is not optimal for the problem specification: its gap to this $N$-call reconstruction procedure is a factor $O(\kappa^{-8}(R/g)^{10}[1+\log(R/\mu)])$, logarithmic in inverse contrast at fixed geometry. The matched frozen-filter lower bound below isolates the effect of training the filter; it does not lower-bound adaptive, preconditioned, accelerated or data-caching linear algorithms. No `allowedAlgorithm` restriction is used to conceal these alternatives.

## Mechanism and proof dependencies

Write $h=\eta R$, $r=g/R$, $\rho=rh$, $x=\mu/R$, and $\delta=h^2x^2$. After a change of coordinates, every **mistaken update** has state $(a,q,t,z)$, initially $(1,0,1,0)$, and recurrence

\[
\begin{aligned}
a^+&=a+bq+\delta\langle p,z\rangle,&q^+&=q+ba,\\
t^+&=t+\delta\langle r_i,z\rangle,&z^+&=z+ap+tr_i,
\end{aligned}
\]

where $p=(u_i+Pu_i)/\sqrt2$, $r_i=(u_i-Pu_i)/\sqrt2$, and $\rho\le|b|\le h$. The actual gate is $baq+\delta(a\langle p,z\rangle+t\langle r_i,z\rangle)\le0$.

The [scalar control proof](../Proofs/DerivativePerceptronControl.lean) derives contraction over two mistaken updates from their gates. A global coarse bootstrap and a geometric warmup then suppress the background coordinates, without assuming favorable signs for residual increments. Two jointly propagated barriers, on $q^2-a^2$ and $q^2-h^2a^2$, control the leakage that a single barrier does not control. The [trajectory proof](../Proofs/DerivativePerceptronTrajectory.lean) combines these with scaled energy $\delta\|z\|^2+a^2$ and separator projection. The [counting proof](../Proofs/DerivativePerceptronCounting.lean) retains initialization, leakage and cubic $\delta K^3$ terms; the [parameter proof](../Proofs/DerivativePerceptronParameters.lean) discharges every numerical inequality from the explicit formulas.

The [ordinary-start convergence proof](../Proofs/DerivativePerceptronConvergence.lean) assumes no trajectory envelope or convergence hypothesis. The [compressed trace](../Proofs/DerivativePerceptronTrace.lean) records only actual mistakes. The [scan proof](../Proofs/DerivativePerceptronExecution.lean) separately accounts for every oracle call and retains a dirty-scan flag because an update can invalidate earlier margins. No contraction is asserted for skipped updates.

## A growing-rank family and matched comparison

The [instance proofs](../Proofs/DerivativePerceptronInstances.lean) use $m\ge1$, dimension $d=2m+8$, coordinate vectors $E_j$, and

\[
\begin{aligned}
B_0&=(E_0-E_{d-1})/16,\\
F&=(E_0+E_{d-1}-2E_1)/16+(E_3-E_4)/4,\\
T_j&=E_{6+2j}-E_{7+2j},\\
u_{j,\sigma}&=B_0+\sigma(F+T_j/32),\qquad j<m,\ \sigma\in\{-1,1\}.
\end{aligned}
\]

These defects are centered, have squared norm $81/512$, and have common derivative margin $\kappa=\sqrt2/16$ with witness $E_0$. The positive-sign derivative vectors are linearly independent, so the rank grows at least as $m$. Opposite defects have squared distance $77/128$, excluding any common cap of the old radius. The geometry permits conflicting directions: direct coordinate expansion gives opposite derivative inner product $-211/1024$, while plus-channel projections on $E_0$ have opposite signs. All samples train the same two filter parameters; this is not a collection of independent scalar optimizations.

Take raw positives $e+\mu u_{j,+}$ and raw negatives $(1+\mu)e-\mu u_{\pi(j),-}$, for any permutation $\pi$, in alternating order. A cyclic permutation for $m\ge2$ avoids the exact pairwise tail cancellation of identity pairing. These are precisely the signed data represented by `data_even` and `data_odd`.

Set $g=\sqrt2$, $R=2\sqrt2$, and $\mu=2^{-500}/(m+1)^2$. `parameters_valid` proves the setup conditions. The nonlinear bound is $O(m\log m)$, with fixed universal constants. In contrast, the [frozen-filter proof](../Proofs/DerivativePerceptronLowerBound.lean) and `family_frozen_mistakes` show that the zero-head, constant-positive-step perceptron with the same initial filter makes both updates in each pair whenever $k\mu\le1/4$. Hence it needs \(\Omega(1/\mu)=\Omega(m^2)\) calls. The scaling proof covers every positive constant step size, including the nonlinear algorithm's step. For general parameters, this comparison is advantageous only when $N\kappa^{-8}(R/g)^{10}\log(R/\mu)=o(1/\mu)$; it is not a uniform advantage in $N,\kappa,g/R$.

## Assumptions, provenance and limitations

The convolutional architecture, signed-margin oracle and simultaneous quadratic-perceptron update come from the primary model above. Centering separates the constant shift-invariant background, and the norm bound fixes scale. Common derivative separability is a substantive structural margin assumption: it models label information surviving a simple high-pass filter, and is stronger than raw-data separability. Its precise quantitative form here, the uniform nonzero background lower bound and the contrast threshold are sufficient assumptions of this result, not claims about necessary conditions or a universally adopted data model. The construction demonstrates nonemptiness and scope; the independent motivation is learning suppression of a shared nuisance background from an unprepared filter.

The proof does not cover pure-background samples, arbitrary/random initialization, noise, larger kernels, nonlinear input features, or arbitrary separable data. In particular, eliminating the lower background bound or substantially relaxing the contrast requirement remains unresolved. The severe threshold and large constants are limitations of this proof; no matching impossibility claim is made.

The literature assessment used targeted independent surveys of the publicly available ICML, ICLR and NeurIPS 2025–2026 material and approximately two years of arXiv submissions/revisions, followed by older primary comparisons. The latest target-paper version was checked on October 30, 2026; its HTML timed out, but its v2 PDF was downloaded and its theorem statements and proof revisited. The NeurIPS 2026 manuscript *Classification at the Edge of Stability* remained inaccessible behind an OpenReview challenge despite verification of its listing; its exact theorem has not been excluded. This is a stated coverage limitation, not evidence of novelty. Conference acceptance is not asserted for arXiv-only sources. The novelty claim concerns the particular cap-free, ordinary-start discrete trajectory mechanism established here, not the general idea of implicit acceleration or its Lean formalization.
