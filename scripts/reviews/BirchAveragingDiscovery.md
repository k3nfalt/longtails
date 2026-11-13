# Novelty review: a logarithmic horizon boundary for corrected averaging

The [main theorem](../../LongTails/Theorems/BirchAveragingDiscovery.lean), under its [explicit zero-noise setup](../../LongTails/Setups/BirchAveragingDiscovery.lean), proves expected squared-gradient accuracy for [fresh-anchor corrected endpoint averaging](../../LongTails/Algorithms/BirchAveraging.lean), for every positive worker count and arbitrary dimension.

**Execution provenance:** desktop-session assessment using the unchanged `scripts/prompts/novelty_prompt.md` and its positive/negative examples. The local runner was attempted, but its child process could not read files under Windows policy and was stopped. This is not a successful scripted-run report or a new independent-agent review. No remote inference occurred; no proof builds were rerun during that novelty assessment. Subsequent library-integration verification is recorded below.

Let \(L>0\) bound global smoothness, \(\Delta\ge0\) the initial objective gap, \(\delta\ge0\) uniform population-Hessian dissimilarity, \(K\ge1\) the public local horizon, and \(\varepsilon>0\) the target **squared** gradient norm. Calls **per worker**, including anchor queries, satisfy

\[
Q=O\!\left(K+\frac{L\Delta}{\varepsilon}
+\frac{LK\Delta}{\varepsilon\log(1+L/\delta)}\right),
\]

where the last term is zero at \(\delta=0\). This follows from the literal \(K\max\{1,\lceil\max\{8L\Delta/(K\varepsilon),16L\Delta/[\varepsilon\log(1+L/\delta)]\}\rceil\}\); rounding requires the additive \(K\). Total component calls are \(mQ\) for \(m\) workers. The output samples queried client points, not final endpoints; first-order similarity is optional, and variance is explicitly zero. The setup does not exclude competing algorithms.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Full GD; [Ghadimi–Lan, SIAM J. Optim. 2013, Thm. 2.1(a)](https://arxiv.org/pdf/1309.5549), \(\sigma=0,\gamma=1/L\) | \(O(1+L\Delta/\varepsilon)\to O(K+L\Delta/\varepsilon+LK\Delta/[\varepsilon\log(1+L/\delta)])\) | None. GD's proved call bound is never worse in order. | None; GD needs no similarity or differentiable client Hessians. | None; uniform GD-iterate selection meets the same expected criterion. | Averaging can use fewer communication rounds, but communication is not charged in this oracle budget. |
| [Tovmasyan et al., Oct. 26, 2026 preprint, Prop. 2 / Thm. 3](https://arxiv.org/html/2610.35663v1#S3.SS2), client selection | \(O(K+(L+K\delta)\Delta/\varepsilon)\to O(K+L\Delta/\varepsilon+LK\Delta/[\varepsilon\log(1+L/\delta)])\) | None: \(\delta\le L/\log(1+L/\delta)\). | None on the zero-noise overlap; prior theorem also permits noise. | None in required information or expected squared-gradient accuracy. | Prior method selects one endpoint and uses previous-round controls; current method averages endpoints with fresh controls. Its \(B=K\) initialization and at most \(2K\) calls per worker per round are included. |
| [Luo et al., AISTATS 2025, Thm. 4](https://arxiv.org/html/2501.04443v3#S5.SS2), zero noise | \(O(K+[(L+\delta)+K\sqrt{(L+\delta)\delta}+K(L+\delta)]\Delta/\varepsilon)\to O(K+L\Delta/\varepsilon+LK\Delta/[\varepsilon\log(1+L/\delta)])\) | A factor of order \(K\) versus this worst-weak-convexity certificate when \(2\le K\le\min\{\log(1+L/\delta),L\Delta/\varepsilon\}\); not a lower bound on Luo's algorithm. | None: substitute local smoothness and weak convexity \(L+\delta\), implied by the present assumptions. Prior averaged similarity is weaker. | Different output: mean local iterate → individual local query. Both satisfy the setup's unrestricted output criterion. | Same deterministic fresh-control trajectories after redundant control evaluations are removed; the displayed comparison does not preserve gains for small actual weak-convexity parameter. GD and client selection still prevent a problem-class improvement. |

The GD reduction explicitly queries every worker at the same point, averages replies, and uses \(F(x-\nabla F(x)/L)\le F(x)-\|\nabla F(x)\|^2/(2L)\). Thus \(T\ge2L\Delta/\varepsilon\) suffices with \(T\) calls per worker, without a free aggregate-gradient oracle. The repository's `GdNonconvex.lean` has the same budget after replacing its norm tolerance by \(\sqrt{\varepsilon}\); its pointwise oracle statement is not silently identified with the present zero-variance oracle model. Zero variance gives almost-sure exactness along the finitely many adaptive queries.

The substantive candidate is instead [the lower construction](../../LongTails/Proofs/BirchAveragingCounterexample.lean): two nonlinear clients with \(L=8,\Delta=9/4,\zeta=2a,\delta=6a\), \(0<a\le10^{-6}\), at \(\eta=1/100\), stall at a nonstationary server anchor for every round count when
\[
K=11002+\left\lceil\frac{\log6250+\log(1/a)}{\log(1009/1000)}\right\rceil.
\]
The actual sampled-output floor is \(81/(2500K)\), whereas the server floor is \(81/2500\); \(\eta K\delta\to0\). This pairs with a sufficient logarithmic horizon at fixed conservative stepsize, not an all-stepsize or minimax lower bound.

Standard-reduction check: smooth descent and finite-path amplification explain the upper proof; they do not supply the lower proof's globally admissible escape–return construction, reflection symmetry, and recurrent fixed point. [Original SCAFFOLD, Thms. II/IV](https://proceedings.mlr.press/v119/karimireddy20a/karimireddy20a.pdf) concerns uncorrected FedAvg drift or quadratic similarity; [Patel et al. 2026, §4](https://arxiv.org/html/2607.14731v1#S4) treats convex uncorrected Local SGD. [Stationary-bias Thm. 4.1](https://arxiv.org/html/2608.26765v1) requires noisy homogeneous strongly convex dynamics with Option-II controls, and [edge-of-stability §3–4](https://arxiv.org/html/2608.25873v1) gives a different control-error discussion and empirical mechanism. None directly yields this noiseless, small-similarity recurrence.

Search coverage: 2026-11-13 UTC; primary 2013–2026 GD, SCAFFOLD, local-SGD, stationary-bias and stability sources, including work outside the companion's references, plus repository overlap. These inspected works predate this standalone delivery dated 2026-11-13; an introduction commit and exhaustive priority history are unavailable. The companion's narrow mathematical claims agree with the sources; its conference-quality assessment is not a consequence of compilation or of this comparison.

## Conclusion

**No problem-class oracle-complexity improvement is established; the supported novelty is a method-specific logarithmic stability obstruction.** Full GD already achieves \(O(1+L\Delta/\varepsilon)\) calls per worker without similarity, and the 2026 client-selection theorem has the better similarity term. The convergence theorem alone therefore would not justify a substantive-novelty verdict, although its certificate improves on Luo's worst-weak-convexity bound in the regime identified above.

The lower result supplies the independent significance: arbitrarily close client gradients and Hessians can still produce all-round nonstationarity under corrected averaging at a logarithmic horizon and conservative stepsize. The checked prior constructions do not imply this statement: uncorrected drift, noisy stationary bias, and quadratic similarity each miss an essential condition. Paired with the upper guarantee, this identifies a quantitative limit on extending selection-style similarity reasoning to endpoint averaging.

This supports a substantive theoretical contribution as a method-specific exception, not a new algorithm or an improved optimization frontier. Its scope remains exact gradients, full participation, one constructed horizon, fixed stepsize, and a local-output floor shrinking as \(1/K\); literature priority is supported by the checked comparisons rather than exhaustively certified. The defensible claim is a logarithmic safe-horizon analysis paired with a persistent nonlinear averaging counterexample under vanishing similarity.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED. Confidence: medium.**


## Library integration verification

The relocated sources passed the full library build and lint, the standard
`run_comparator.py BirchAveragingDiscovery.lean` audit, and three native
fixed-statement Comparator checks (main convergence with a fixed literal budget,
sampled-output failure, and vanishing step–horizon–similarity product).
All three results use only `propext`, `Classical.choice`, and `Quot.sound`.
The original non-IID setup is byte-identical to the reviewed standalone input;
supporting proof bodies are preserved in the grouped library modules.

The integration adds natural-number-indexed convergence metadata without permitting
extra proof hypotheses, omitted indices, or reordered indices. Indexed online
families remain explicitly unsupported. The budget renderer and actual metadata
extraction were checked for the new theorem and existing ordinary and online
theorems. The independent integration reviewer found no source-level defect.

These checks establish formal integration and preserve the review's scope. They
do not raise its novelty confidence or constitute a new successful automated
novelty-runner invocation. Comparator used the development `fake-landrun.sh`
adapter: kernel replay and dependency checking were performed without an OS
sandbox.

The full Comparator regression suite (`python3 -m unittest discover -s tests -p test_comparator.py -v`) passed all 15 test groups, including indexed-family acceptance and rejection cases and existing ordinary/online compatibility cases.
