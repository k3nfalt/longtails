# A logarithmic horizon barrier for nonconvex corrected endpoint averaging

Lean-verified research result. The novelty assessment is in [scripts/reviews/BirchAveragingDiscovery.md](../../scripts/reviews/BirchAveragingDiscovery.md).

## Result and scope

We study full-client, fresh-anchor corrected local gradient descent followed by endpoint averaging. For a global objective \(F=m^{-1}\sum_i f_i\), a round starting at \(x_r\) computes all local anchor gradients and uses
\[
y_{i,0}=x_r,\qquad
y_{i,k+1}=y_{i,k}-\eta[\nabla f_i(y_{i,k})-\nabla f_i(x_r)+\nabla F(x_r)],
\qquad x_{r+1}=m^{-1}\sum_i y_{i,K}.
\]
The first local query supplies the anchor gradient, so there are exactly \(K\) calls per worker per round. The returned point is uniform over the \(mKR\) queried local points, including \(k=0\) and excluding the unqueried final endpoints. The algorithm accesses gradients through the worker oracles; it has no free global-gradient oracle or function-value oracle.

Assume global \(L\)-smoothness, a finite lower bound with initial gap at most \(\Delta\), differentiable client gradients, and the uniform population Hessian bound
\(\|\nabla^2f_i(x)-\nabla^2F(x)\|_{op}\le\delta\).
The original IID, measurable, unbiased worker-oracle model is retained, with variance parameters explicitly restricted to zero. This gives almost-sure exactness on the queries actually used, rather than assuming pointwise exactness of every admissible oracle. First-order similarity is optional for the upper theorem. The lower construction satisfies it globally as well.

For \(\delta>0\), choose
\[
\eta=\min\left\{\frac1{4L},\frac{\log(1+L/\delta)}{8LK}\right\},\qquad
R=\max\left\{1,\left\lceil\max\left\{\frac{8L\Delta}{K\varepsilon},
\frac{16L\Delta}{\varepsilon\log(1+L/\delta)}\right\}\right\rceil\right\}.
\]
Then the actual returned point satisfies \(\mathbb E\|\nabla F(\widehat x)\|^2\le\varepsilon\), using \(KR\) calls per worker. At \(\delta=0\), every positive horizon is permitted with \(\eta=1/(4L)\) and \(R=\max\{1,\lceil8L\Delta/(K\varepsilon)\rceil\}\). Accuracy means squared gradient norm, not gradient norm.

`OracleTemplate.BirchAveragingDiscovery.result` is the single main `OracleTemplate.Convergence` theorem. Its natural-number index represents \(m=n+1\), covering every positive worker count and arbitrary dimension. The public algorithm witness is `makeAlgorithm`, which explicitly instantiates `correctedAveraging`. The public budget is written out in the definition `budget`. `max 1 localSteps` only makes the witness total on invalid inputs; validity requires a positive local horizon. The setup adapter delegates admissibility and success to the unchanged standalone setup and makes the zero-noise restriction explicit.

## Why the horizon restriction matters

For every construction amplitude \(0<a\le10^{-6}\), consider two clients in two dimensions:
\[
F(x,y)=\tfrac12x^2+\tfrac{x}{50}+\tfrac12y^2-2\log\cosh y
-\tfrac15\tanh x(1-e^{-y^2}),\qquad
f_\pm=F\pm a\tanh x\tanh y.
\]
The certified constants are \(L=8\), first-order similarity \(\zeta=2a\), second-order similarity \(\delta=6a\), and initial gap \(\Delta=9/4\). All bounds are global; no trajectory-only smoothness assumption is used. An explicit exact-gradient worker oracle is fully admissible.

At \(\eta=1/100\) and
\[
K(a)=11002+\left\lceil\frac{\log6250+\log(1/a)}{\log(1009/1000)}\right\rceil,
\]
there exists an anchor \((s,0)\), with \(s\in[4/25,9/50]\), that is an exact fixed point of the server round map. Its true squared gradient norm is at least \(81/2500\). One anchor works for every number of rounds. Consequently the actual uniform local-query output has expected squared gradient norm at least \(81/(2500K(a))\), independently of the positive round count. `admissible_sampled_output_failure` proves failure of the original success predicate below that threshold.

The formal horizon bounds include rounding and show logarithmic growth in \(1/a\). Moreover, \(\eta K(a)\delta\to0\). Thus a sufficiently small product \(\eta K\delta\), even together with a conservative \(\eta L\), cannot by itself guarantee convergence of this averaging method on the stated class. The sampled-output floor decreases with \(K\); it is not the constant server-gradient floor. This is not a lower bound for every algorithm, every stepsize, or every horizon. It establishes an order-level logarithmic obstruction at fixed conservative stepsize, not a fully optimized minimax complexity theorem.

The upper proof bounds endpoint dispersion through finite-path amplification, then absorbs the smoothness cost of averaging. The lower proof exposes the corresponding nonlinear mechanism: tiny client disagreement seeds opposite transverse excursions in a shared region of negative curvature. The local paths enter opposite valleys while their average returns to a nonstationary anchor. Discrete invariant regions, explicit escape and return bounds, reflection symmetry, and a continuous fixed-point argument establish recurrence for all rounds. All gradient and Hessian claims are proved in the setup's Euclidean geometry.

## Relationship to prior work

The original setup request was motivated by [Arjevani–Shamir (2015)](https://arxiv.org/abs/1506.01900), on communication limits under similarity, and [Mishchenko et al. (2022)](https://arxiv.org/abs/2206.07638), on asynchronous SGD. Those works provide context, not a transfer of their convex communication or asynchronous guarantees to this method. Here first-order similarity means the uniform bound \(\|\nabla f_i(x)-\nabla F(x)\|^2\le\zeta^2\), and second-order similarity means the uniform operator-norm bound stated above; these exact definitions govern the comparison. No equivalence to weaker averaged heterogeneity assumptions is asserted.

| Source | Comparison and limitation |
|---|---|
| [Birch SGD, Tyurin–Sivtsov](https://arxiv.org/abs/2505.09218) | Supplies the computation-tree motivation and original formalized context. The present corrected averaging algorithm is analyzed in the standalone non-IID oracle setup, not claimed to be an unmodified raw-tree Birch policy. |
| [SCAFFOLD under similarity, October 26, 2026 preprint](https://arxiv.org/html/2610.35663v1) | Its nonconvex guarantee uses client selection; its experimental discussion and conclusion motivate an averaging extension. Our result identifies a barrier to transferring that guarantee to endpoint averaging. It does not contradict the paper's proved selection theorem. Its controls and stochastic costs must not be identified with our fresh exact controls without a separate argument. Its stochastic convex logarithmic term is distinct from our deterministic nonconvex horizon dependence on \(\log(L/\delta)\). |
| [Luo et al., AISTATS 2025](https://arxiv.org/html/2501.04443v3) | In the zero-noise case their current-anchor controls produce the same deterministic trajectories, after removing redundant evaluations in the stationary control phase. Theorem 4 measures gradients at the mean local iterate, whereas ours averages squared gradients at individual client points. Their averaged similarity assumption is weaker. Their deterministic coefficient includes \(L/K+\sqrt{L\delta}+\rho\), with weak-convexity parameter \(\rho\). Our objective has negative curvature of magnitude one at the origin, so this term does not vanish with amplitude. Theorem 5 imposes additional quadratic structure. No blanket rate dominance is claimed. |
| [Original SCAFFOLD, ICML 2020](https://proceedings.mlr.press/v119/karimireddy20a.html) | Its FedAvg drift example concerns uncorrected updates. Its quadratic similarity result couples weak convexity to dissimilarity; it does not supply the present nonlinear failure of corrected updates with vanishing global similarity. Thus the construction is not a direct reuse of the standard uncorrected client-drift example. |

The proposed contribution is the combination of a logarithmically safe averaging guarantee and a globally smooth, globally similar nonlinear recurrence obstruction. Neither a routine upper bound alone nor formalization effort establishes paper-level novelty. The independent review assesses this distinction against the closest checked prior results. There is no claim of a new algorithm, a noisy-oracle theorem, or a problem-class oracle improvement over gradient descent.

## Formal integration and verification

The original standalone setup is included as `LongTails/Setups/BirchNonIID.lean`. `LongTails/Setups/BirchAveragingDiscovery.lean` explicitly selects the zero-variance, second-order-similarity subclass. Client objectives may differ; temporal oracle sampling remains IID. These results concern client heterogeneity, not temporally dependent samples or a positive-noise extension.

The public algorithm witnesses are in `LongTails/Algorithms/BirchAveraging.lean` and `BirchAveragingDiscovery.lean`. Supporting proofs are grouped into Paths, Replay, Execution, Convergence, Instability, and Counterexample modules under `LongTails/Proofs`. The main worker-indexed theorem is `OracleTemplate.BirchAveragingDiscovery.result`; the counterexample module includes `BirchNonIIDInstability.admissible_sampled_output_failure` and `step_horizon_similarity_tendsto_zero`.

The standalone proofs previously passed Lean builds, declaration and style lint, and three native Comparator checks, using only `propext`, `Classical.choice`, and `Quot.sound`. Library integration passed `./build.sh`, `./lint.sh`, standard `run_comparator.py BirchAveragingDiscovery.lean`, and all three fixed-statement native Comparator checks on the relocated results. The main fixed challenge retains the literal budget and every positive worker count. The full library lint found zero errors; direct transitive-axiom inspection of all three results found only the permitted axioms. Budget-rendering regression tests and website metadata extraction passed for the new indexed result and existing ordinary and online results. Comparator uses the repository's development `fake-landrun.sh` adapter, which provides no OS sandbox; its evidence is statement/dependency checking and Lean kernel replay.

The novelty review is a desktop-session application of the repository's review prompt. Its attempted local runner was blocked by Windows policy and did not complete. Its medium-confidence verdict supports the combined method-specific upper/lower result, not an oracle-complexity improvement or a guarantee of conference acceptance.

The full Comparator regression suite (`python3 -m unittest discover -s tests -p test_comparator.py -v`) passed all 15 test groups, including indexed-family acceptance and rejection cases and existing ordinary/online compatibility cases.
