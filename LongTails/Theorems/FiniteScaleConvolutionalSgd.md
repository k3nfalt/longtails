# Finite-scale logistic SGD learns a separating convolutional filter beyond two samples

[Main theorem](FiniteScaleConvolutionalSgd.lean) · [Setup](../Setups/FiniteScaleConvolutionalSgd.lean) · [Algorithm and output](../Algorithms/FiniteScaleConvolutionalSgd.lean)

This result gives a quantitative, finite-initialization guarantee for joint logistic SGD on a two-tap convolutional model with an arbitrary finite, derivative-separable sample cloud. The cloud can contain conflicting directions and need not consist of two samples or lie in an acute cluster. The contribution is a uniform feature-adaptation guarantee for an explicitly restricted regime, not a new best oracle complexity for this problem class. A fixed derivative filter is already a faster problem-class solution.

## Statement and oracle model

The motivating data model has a large approximately constant nuisance background and weak label-bearing spatial variation. Cyclic differencing removes the common mode. After labels are absorbed into signed examples, the background can have either sign even when unsigned examples have similar backgrounds. The question is whether jointly trained sigmoid SGD suppresses this nuisance mode automatically, rather than being supplied a fixed differencing filter.

Let $e\in\mathbb R^d$ be the unit constant vector and $P$ the cyclic coordinate shift. The $N\ge1$ signed examples have the form
\[
b_i=\frac{\alpha_i}{\sqrt2}e+\mu u_i,
\qquad g\le |\alpha_i|\le R,
\qquad \langle e,u_i\rangle=0,
\qquad \|u_i\|\le1/\sqrt2.
\]
Here $d\ge1$, $0<g\le R$, and $\mu>0$. Labels are absorbed into the signed inputs. Define
\[
p_i=(u_i+Pu_i)/\sqrt2,
\qquad r_i=(u_i-Pu_i)/\sqrt2.
\]
There must exist a unit vector $v_\star$ with $\langle v_\star,r_i\rangle\ge\kappa$ for every example, where $0<\kappa\le1/4$. The separator and the decomposition of the samples are proof witnesses, unavailable to the algorithm. The numerical bounds and the sample count are public.

For jointly trained filter and readout $\theta=(h_1,h_2,v)$, the margin is
\[
m_i(\theta)=h_1\langle b_i,v\rangle+h_2\langle Pb_i,v\rangle,
\]
and the component loss is $\log(1+\exp(-m_i(\theta)))$. The loss is nonlinear and nonconvex in the jointly trained parameters even though the resulting predictor is linear in the input. The theorem does not cover arbitrary nonlinear activations or arbitrary neural networks.

One component oracle call returns the margin and its full parameter gradient. The supporting geometry module proves the logistic derivative identity and recovery of this information from exact component logistic value and gradient. This is a value-and-gradient model, not a gradient-only claim. Each validation query and each training query costs one call.

Sampling is uniform IID over the finite index set. The setup uses the repository's shared `IID` structure: measurable sample variables, `iIndepFun`, and the specified marginal pushforwards under an abstract probability measure. The source probability space is unrestricted; only the dataset is finite. Product laws for finite blocks are derived internally.

Put
\[
\eta=\frac{\kappa}{1000R},\quad
\rho=\eta g,\quad \delta=(\eta\mu)^2,\quad
L=\log(24/\delta).
\]
The additional contrast restriction is
\[
\delta\le1,
\qquad
\delta L^2\le\frac{\kappa^3\rho^4}{10^{22}N^3}.
\]
Equivalently, the second inequality reads
\[
\mu^2\log^2\!\left(\frac{24\cdot10^6R^2}{\kappa^2\mu^2}\right)
\le\frac{\kappa^5g^4}{10^{28}N^3R^2}.
\]
This is an extremely small-contrast regime, not an unrestricted small-contrast theorem. For fixed positive $g,R,\kappa,N$, it holds for sufficiently small positive $\mu$. The proof does not establish that this restriction, its constants, or the exclusion of zero-background samples is necessary for the algorithm.

The two-tap bilinear predictor and the common-background/small-defect question come from Tyurin's model and two-sample analysis (Theorems 2.1 and 5.1). Ordinary margin separability is standard, but its use for this entire signed derivative-feature cloud is a structured generalization, not a claim that this exact data class is a standard neural-network assumption. The repository's [ManySample setup](../Setups/ManySampleConvolutionalPerceptron.lean) already uses derivative separability for defects against a pure reference; the present class instead requires every signed example to have a separating derivative. Centering fixes the decomposition, and the defect norm fixes its scale. Two-sided nonzero background bounds, the particular broad filter-initialization region, and the quantitative contrast inequality are explicit restrictions of the present analysis, not consequences asserted by the cited paper. The lower background bound supplies nuisance-entry contraction; zero-background examples can still learn, and no intrinsic impossibility is claimed. Uniform IID sampling is the usual finite-sum model. The unusually strong contrast condition controls interaction between background suppression and residual learning; its powers and constants are only sufficient proof conditions.

## Initialization, execution, and guarantee

The public initial readout $v_0$ is arbitrary. Choose public filter coordinates $a_0\in[-1,1]$, $t_0\in[1,3/2]$. Define
\[
T_0=\left\lceil48N\rho^{-2}L\right\rceil,
\quad H=10000N\rho^{-2}L,
\quad T=T_0+\left\lceil96NH/\kappa\right\rceil,
\quad B=T+1,
\]
\[
s^2=\frac{B(\eta+\|v_0\|^2)}{\delta},
\qquad
\theta_0=\left(\frac{s(a_0+t_0)}{\sqrt2},
                    \frac{s(a_0-t_0)}{\sqrt2},v_0\right).
\]
The amplitude is large, explicitly tuned, and depends on the public readout norm. This is not arbitrary full-parameter initialization. The formal setup uses positive $t_0$; it does not quantify over a negative-sign branch.

Every retained training step is ordinary component logistic SGD with constant step $\eta$:
\[
\theta_{k+1}=\theta_k+
\frac{\eta}{1+\exp(m_{i_k}(\theta_k))}\nabla m_{i_k}(\theta_k).
\]
Correctly classified examples still update the parameters. There is no hard-threshold approximation, clipping, or assumed trajectory margin gap.

Before each training query, the algorithm checks all $N$ margins at the current point. It freezes the first point with all margins strictly positive. Each unsuccessful run validates states $0,\ldots,T$, retains $T$ updates, and then discards one queried training reply at the restart boundary. Thus a complete run is charged exactly $B(N+1)$ calls. Subsequent calls after freezing are harmless dummy validation queries. Restarts use the same initialization and disjoint fixed IID sample blocks. Step size, initialization, and restart period do not depend on the private requested failure probability.

For any $0<q<1$, the named `tunedOutput`, run through `execute`, satisfies
\[
\Pr\{\exists i:\ m_i(\mathrm{tunedOutput})\le0\}\le q
\]
after the public budget
\[
\left\lceil
10^{14}N^3\left(\frac Rg\right)^2\kappa^{-3}
\log\!\left(\frac{24\cdot10^6R^2}{\kappa^2\mu^2}\right)
\left(1+\log\frac1q\right)
\right\rceil.
\]
The probability in the Lean specification explicitly includes both algorithm and oracle seed laws. The deterministic admissible oracle makes the latter immaterial. The cost proof covers $\lceil\log(1/q)\rceil+1$ complete runs, all validation calls, discarded boundary queries, rounding, and any excess calls in the simplified budget. The setup's `allowedAlgorithm` enforces the scanned, periodically restarted SGD update and frozen-output rule while leaving its positive tuning parameters free.

## New mechanism

The proof works with exact finite sigmoid weights, not convergence to a hard perceptron trajectory. In normalized coordinates, the parameter update is
\[
\begin{aligned}
a^+&=a+c_iwq+\delta w\langle p_i,z\rangle,&
q^+&=q+c_iwa,\\
t^+&=t+\delta w\langle r_i,z\rangle,&
z^+&=z+w(ap_i+tr_i),
\end{aligned}
\]
where $c_i=\eta\alpha_i$, $w=(1+\exp(Ks_i))^{-1}$, $K=s^2/\eta$, and
$s_i=c_i aq+\delta\langle ap_i+tr_i,z\rangle$.
The finite-temperature error obeys $ws_i\le1/K\le\delta/B$.

The first phase contracts the nuisance potential
$W=a^2+q^2+2|a^2-q^2|$, stopped at either classification or entry below an explicitly retained floor $F=1000N\delta(4T_0+1)/\rho^2$. The floor is linear in $\delta$; discarding this term would invalidate the drift argument.

After entry, the proof controls cumulative discretization work using the coupled energy and imbalance identities. In particular, the quadratic update work is charged to positive background work, forcing, and entry energy, with a small coefficient proportional to the background step bound. This closes a simultaneous bootstrap for nuisance energy, the difference-filter coordinate, and readout radius even for conflicting residual directions. A pointwise moving-comparator contraction or an unweighted elapsed-time Cauchy bound does not provide this control.

The late phase bounds cumulative sigmoid weight by $6H/\kappa$. An adapted indicator records entry by time $T_0$ and nonseparation through the current time. Conditional expected weight before separation is at least $1/(2N)$. Integrating this adapted process yields a one-run failure probability at most $1/4$; independence of fixed restart blocks amplifies it. No conditioning on future failure or assumed trajectory stability is used.

The interpretation is a dichotomy: either separation happens early, or the normalized nuisance filter coordinate becomes small and the derivative component drives separation. An early returned separator need not itself be approximately a pure derivative filter.

## Literature comparison and significance

[Tyurin, *Gradient Descent as a Perceptron Algorithm: Understanding Dynamics and Implicit Acceleration*, ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv v2, 21 May 2026](https://arxiv.org/abs/2512.11587v2), is the starting point. Its Theorem 2.1 gives a fixed-time large-initialization correspondence with a quadratic perceptron for almost all initializations, with nonzero margins along the limiting trajectory; Theorem 5.1 develops the noisy two-sample convolutional example. These statements do not directly supply the present uniform finite-sigmoid, arbitrary-cloud SGD guarantee. The new analysis avoids a trajectory-gap assumption and the acute-cloud restriction, while adding the explicit derivative-separation, nonzero-background, and severe contrast conditions above. It is not a superset of every earlier setup: pure anchor examples with zero derivative are excluded.

The existing [ManySampleConvolutionalPerceptronAcceleration](ManySampleConvolutionalPerceptronAcceleration.lean) already proves a deterministic, polylogarithmic-contrast finite-call guarantee for arbitrarily many derivative-separable defects. It uses a pure reference sample, mistake-selected quadratic-perceptron updates, a directed reference kick, zero readout, and a finite-prefix stability argument. [ClusteredConvolutionalPerceptronAcceleration](ClusteredConvolutionalPerceptronAcceleration.lean) removes the pure reference and kick and proves a coupled many-sample bound plus a matched fixed-step perceptron lower trace, but requires a narrow residual cap and a filter initialized close to differencing. Our class admits conflicting clouds outside that cap, our filter-direction interval has fixed width, and our head is arbitrary. The substantive new argument is the uniform **finite sigmoid** stochastic dynamics and weighted-work/entry analysis, not many-sample scope or logarithmic contrast dependence alone. These results have different assumptions and algorithms; none is claimed to dominate all the others, and their perceptron lower traces do not establish a logistic-SGD lower bound here.

The strongest unrestricted oracle upper bound is just **$N$ calls**. At filter $(1,0)$ and zero readout, the oracle's readout-gradient component is exactly $b_i$. One query per index therefore caches the entire dataset. Offline compute $(b_i-Pb_i)/\sqrt2=\mu r_i$, solve its feasible linear separation constraints, and return a pure differencing filter with that readout. Subsequent computation requires no oracle calls under this cost model. The unrestricted solution is deterministic and independent of $\mu$, $\kappa$, and the failure target. Thus our gap to this bound is $O(N^2(R/g)^2\kappa^{-3}L(1+\log(1/q)))$. Enforcing the claimed SGD family does not make that reduction disappear or create novelty.

A stronger same-loss SGD comparator also remains faster than our jointly trained method. Fix the derivative filter and optimize only the normalized readout. For normalized features $r_i$, constant-step logistic SGD with step $h=T$ and zero initial readout satisfies, with $S=\sum_{k<T}w_k$,
\[
\kappa^2 S^2\le S+2/e,
\]
by projection growth and the exact squared-norm recursion. Hence at most $4/\kappa^2$ sampled mistakes occur. A uniform pre-update iterate after $T=\lceil8N/\kappa^2\rceil$ steps is a global separator with probability at least one half. Validate only that returned candidate, then restart. This gives $O((N/\kappa^2+N)\log(1/q))$ calls; the physical readout step rescales by $\mu^{-2}$. Thus our remaining overhead is polynomial, approximately $N^2(R/g)^2\kappa^{-1}L$. We do not call the result near-optimal or a problem-class acceleration over this baseline.

For unprocessed raw-input logistic SGD, applicable general margin-based certificates retain inverse raw-margin-squared dependence. Relevant primary comparisons include [Kale et al., arXiv v2, 27 February 2026, §3.3 Theorem 3.4 and §3.4 Theorem 3.5](https://arxiv.org/abs/2602.18946v2), and [Vaswani and Babanezhad, arXiv v4, 24 February 2026, §6 and Appendix E, Corollary 7](https://arxiv.org/abs/2503.00229v4), whose original paper appears in [ICML 2025](https://proceedings.mlr.press/v267/vaswani25a.html). These include adaptive step-size analyses and require attention to global-loss hitting versus a returned point and to line-search value calls. Their generic certificates do not supply this joint convolutional feature-adaptation guarantee by substituting the raw margin.

The stronger adaptive full-gradient baseline is also relevant: [Zhang, Wu, Lin, and Bartlett, JMLR 27(124), 2026](https://jmlr.org/papers/volume27/25-1941/25-1941.pdf), Theorem 2, obtains arbitrarily small risk at an averaged iterate after at most $\gamma^{-2}$ burn-in steps with a sufficiently large adaptive-step hyperparameter. Those are full-gradient steps, each costing $N$ component calls without caching. Their §4.1/Theorem 11 nonlinear extension trains first-layer weights with fixed output signs and gives a best-iterate risk bound; it does not cover joint convolutional filter/readout training. Assumption 1 of that paper is also precise provenance for ordinary norm-bounded margin separability, applied here to the derivative features rather than the raw inputs.

For families with normalized raw margin $\Theta(\mu\kappa/R)$, the present certificate is logarithmic rather than inverse quadratic in contrast, with $N,R/g,\kappa,q$ fixed. The comparison concerns proved certificates under the stated restricted regime. It is not a lower bound on optimally tuned linear GD/SGD, and special balanced examples can cancel the background very quickly. The independent significance is quantitative automatic nuisance-filter suppression in a genuinely jointly trained model, despite arbitrary conflicting examples and finite sigmoid updates, rather than a claim that preprocessing cannot solve the class.

## Nontrivial instances and limitations

In a real Fourier band where $|\sin(\pi k/d)|\ge1/2$, the operator $D=(I-P)/\sqrt2$ has singular values between $1/\sqrt2$ and $\sqrt2$. Choose a unit vector $v_\star$ and many unit vectors $v_j\perp v_\star$ in that band, spanning multiple directions and with zero in their convex hull. Antipodal tangential pairs allow negative pairwise inner products. Set
\[
u_j=\tfrac12D^{-1}\left(2\kappa v_\star+\sqrt{1-4\kappa^2}\,v_j\right).
\]
Then $\|u_j\|\le1/\sqrt2$ and $\langle v_\star,Du_j\rangle=\kappa$. For every $u_j$, include both signed examples $+\alpha_j e/\sqrt2+\mu u_j$ and $-\beta_j e/\sqrt2+\mu u_j$, with possibly unequal $\alpha_j,\beta_j\in[g,R]$. Within each pair, convex weights proportional to $\beta_j$ and $\alpha_j$ cancel the background. Combining these pairs with weights that cancel the tangential $v_j$ components gives a convex combination $\mu\kappa D^{-1}v_\star$, whose norm is at most $\sqrt2\mu\kappa$. Conversely, $D^*v_\star/\|D^*v_\star\|$ separates the raw signed examples with margin at least $\mu\kappa/\sqrt2$. Thus the raw maximum unit-separator margin is $\Theta(\mu\kappa)$. If $g/R$ is bounded below by a positive constant, or the selected background magnitudes are otherwise comparable to $R$, global normalization by the largest input norm gives $\Theta(\mu\kappa/R)$ for small contrast. Allowing an arbitrary loose upper bound $R$ alone would not justify that denominator. This produces arbitrarily many conflicting examples and interacting coordinates; the shared trainable filter couples their readout dynamics. This construction is illustrative mathematics, not an additional assumption or a separately formalized theorem. Dimension does not enter the call bound, apart from feasibility of the geometry; arithmetic cost per vector oracle call is not counted.

The theorem proves strict empirical classification, not a specified positive margin, logistic-loss tolerance, population accuracy, or implicit-bias direction. It requires known scale/margin bounds, potentially enormous filter initialization, full validation scans, and restarts. It does not prove deterministic full-batch GD convergence, near-optimal dependence on $N$ or $\kappa$, necessity of the contrast restriction, or an actual lower-bound separation from the best tuned raw-input method.

The literature survey used the UTC date 30 October 2026 and independently covered ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2025 plus publicly available accepted NeurIPS 2026 records and preprints, approximately two years of arXiv submissions/revisions, and stronger foundational references. The latest checked Tyurin version was v2; Vaswani–Babanezhad was v4; Kale et al. was v2. Kale et al.'s subsequently published TMLR/OpenReview PDF was inaccessible, so that comparison is explicitly to the accessible arXiv version. The potentially relevant [rank-one edge-of-stability submission](https://openreview.net/forum?id=SpeSts2ED1) and [NeurIPS 2026 logistic-dynamics paper](https://openreview.net/forum?id=VpiPrv9CUK) also had inaccessible full texts; accessible abstracts were not treated as proof-level novelty evidence. The 2026 NeurIPS coverage does not imply that unavailable proceedings were read. This is a targeted, non-exhaustive survey with explicit access limitations. A recent related [Nguegnang et al. preprint, v1, 20 October 2026, Propositions 11–12 and Theorem 13](https://arxiv.org/html/2610.28561v1) concerns regularized squared-loss deep linear networks and Robbins–Monro asymptotic critical-set convergence, not this finite constant-step unregularized logistic classification guarantee. It is an unreviewed preprint, not an accepted-conference baseline.
