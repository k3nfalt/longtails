# Randomized lower bound for constrained smooth quasar-convex optimization

The [lower theorem](HighDimensionalConstrainedQuasarLowerBound.lean) proves an oracle-complexity lower bound for constrained, smooth, γ-quasar-convex minimization against **every randomized algorithm**, covering both the deterministic term and the high-probability noise term:

\[
\Omega\!\left(\frac{1}{\gamma}\sqrt{\frac{LD^2}{\varepsilon}}+\frac{\sigma^2D^2\log(1/\delta)}{\gamma^2\varepsilon^2}\right)
\quad\text{calls per oracle channel.}
\]

The companion [upper theorem](HighDimensionalConstrainedQuasarUpperBound.lean) transfers the repository's existing high-probability method to the same setup. Together the two theorems give the complexity up to the factors \(\log(1/\delta)\log^2(LD^2/(\gamma^2\varepsilon))\) on the deterministic term and \(\log^2(LD^2/(\gamma^2\varepsilon))\) on the noise term.

## Setup

The [setup](../Setups/HighDimensionalConstrainedQuasar.lean) is the repository's [StochasticConstrainedQuasar](../Setups/StochasticConstrainedQuasar.lean) problem, specialized only in its parameters. Its instance type, admissibility predicate and success predicate are literally those of `StochasticConstrainedQuasar.spec`, evaluated at `Params.toStochastic p`.

The problem class is the same as in that setup:

- **Space and feasible set.** The space is \(E=\mathbb R^d\). The feasible set \(X\) is compact and convex, contains \(x_0\) and a constrained minimizer \(x_\star\), and has diameter at most \(D\).
- **Objective.** On \(X\), \(f\) is differentiable with an \(L\)-Lipschitz gradient, and it is γ-quasar-convex with respect to \(x_\star\):
  \[\gamma(f(x)-f(x_\star))\le\langle\nabla f(x),x-x_\star\rangle,\qquad 0<\gamma\le1.\]
- **Two oracle channels.**
  - An unbiased stochastic gradient with variance at most \(\sigma^2\). It is jointly measurable and driven by fresh IID seeds.
  - An exact Euclidean projection onto \(X\).

  Gradient replies are constrained only at points of \(X\).
- **Success.** The returned point must satisfy \(\Pr\{\hat x\in X,\ f(\hat x)-f(x_\star)\le\varepsilon\}\ge1-\delta\), and the output must be measurable.

The parameter strengthenings, all stated in `valid`, are the following.

| Strengthening | Reason |
| --- | --- |
| \(E=\mathbb R^d\) with \(d\ge2^{34}(B+1)^5\), where \(B\) is the budget below | Randomized chain lower bounds need high dimension; the same shape appears in [SmoothAndConvexExpected](../Setups/SmoothAndConvexExpected.lean). |
| Seed space Ω = Bool | Shrinking the admissible-oracle class only strengthens a lower bound. The upper theorem holds for every Ω. |
| \(LD^2/\varepsilon\ge10^8\) | Nontrivial-accuracy regime; HSS use a comparable condition. |
| \(\delta\le1/4\) | Nontrivial-confidence regime. |
| \(\sigma=0\) or \(64\gamma\varepsilon\le\sigma D\) | The noise is either absent or at least the far-field gradient scale. |

Two consequences of these restrictions:

- **The noise band.** In the excluded band \(0<\sigma<64\gamma\varepsilon/D\), the noise term of the upper bound, \(\sigma^2D^2/(\gamma^2\varepsilon^2)\), is below \(4096\) in absolute size. The rare-revelation argument cannot hide gradients of size \(\asymp\gamma\varepsilon/D\) there, so that band is excluded rather than claimed.
- **No new structural assumption.** The objective class, oracle model and accuracy criterion are unchanged.

Regime nonemptiness is proved by `valid_nonempty` in [HighDimensionalQuasarInclusion](../Proofs/HighDimensionalQuasarInclusion.lean). The witness has \(d=2^{34}3^5\), \(L=D=1\), \(\gamma=1/2\), \(\sigma=0\), \(\varepsilon=10^{-8}\) and \(\delta=1/4\).

## Theorem

The public budget, per channel, is

\[
B=\left\lfloor\frac{\sqrt{LD^2/\varepsilon}}{10^4\gamma}+\frac{\sigma^2D^2\log(1/\delta)}{8192\gamma^2\varepsilon^2}\right\rfloor .
\]

`result : NonConvergence spec budget` states the following. For every valid parameter choice, every allowed algorithm and every componentwise budget \(b\le B\), there is an admissible instance and oracle such that the actual `execute` output fails the success criterion. Two properties of the quantifiers:

- **Every budget is covered.** This includes \(b=0\), \(b=B\), and any split of calls between the gradient and projection channels.
- **Seed independence.** The instance may depend on the algorithm and on \(b\), through the chain length and the number of candidate wells. It never depends on the realized algorithm seed or oracle seed.

## Hard instances

Write \(K=b_0+b_1\) for the total number of calls. The proof chooses the instance according to which budget term dominates.

### (A) Deterministic term: a robust quasar-convex zero-chain

This branch handles budgets where the first term dominates.

On a chain \(y\in\mathbb R^T\), the proof uses the following function, from [QuasarHardChain](../Proofs/QuasarHardChain.lean) and [QuasarHardProfiles](../Proofs/QuasarHardProfiles.lean):

\[
F_\sigma(y)=\tfrac14(y_1-1)^2+\tfrac14\sum_{i<T}\big(\max\{|y_i-y_{i+1}|-\eta,0\}\big)^2+\sigma\sum_i\psi(y_i).
\]

- **The bump ψ.** ψ is an explicit piecewise-quadratic function built from `ramp`. It is flat on \([-1/20,1/20]\), has slope \(-10\) on \([0.1,0.9]\), equals \(50(\theta-1)^2\) near and beyond \(1\), and has its unique zero at \(1\). Its key properties are `bump_quasar` and `bump_le_pairing`.
- **The dead zone.** The coupling uses a dead zone of width \(\eta=1/(100T)\). Together with the flat bottom of ψ, this makes \(F\) a **robust zero-chain**: coordinates whose values lie in the dead zone affect neither the value differences nor the gradient.

**Lemma Q** (`quasar_normalized`) is the new analytic step. If \(\sigma\le10^{-4}\), \(T\sqrt\sigma\ge1\) and \(T\eta\le1/100\), then \(F_\sigma\) is \(1/(100T\sqrt\sigma)\)-quasar-convex with respect to its minimizer \(\mathbf 1\). The proof follows the case structure of Hinder–Sidford–Sohoni's Lemma 7, adapted to the dead zone and the flat-bottom bump:

1. \(y_1\) is far from 1.
2. No coordinate lies in \((-0.1,0.1)\).
3. A transition window, handled by a Cauchy–Schwarz bound on the dead-zone differences plus the slope of ψ.

At σ = 0 the function is convex, hence 1-quasar.

**Embedding and scaling.** The chain is placed on hidden coordinates \(\pi:\mathrm{Fin}\,T\hookrightarrow\mathrm{Fin}\,d\), inside \(X=\bar B(x_0,D/2)\), with scale \(a=D/(2\sqrt T)\). For γ ≤ 1/100 the bump weight is \(s^2\), with \(s=1/(100T\gamma)\) and \(T=2K+4+\lceil1/\gamma\rceil\). For γ > 1/100 the convex chain is used, which is γ-quasar for every γ ≤ 1. The relevant modules are [QuasarHardInstance](../Proofs/QuasarHardInstance.lean) and [QuasarLowerAssembly](../Proofs/QuasarLowerAssembly.lean).

**Hiding argument** ([QuasarHardHiding](../Proofs/QuasarHardHiding.lean), [QuasarHardFailure](../Proofs/QuasarHardFailure.lean)):

- **Instance-independent replies.** Queries outside \(X\) receive the gradient reply 0 for every instance, and projection replies do not depend on the instance.
- **Prefix simulation.** A simulated run with prefix-truncated fields reveals at most one new hidden coordinate per call.
- **Counting.** The repository's distinct-word counting (`bounded_prefix_bad_count`) bounds the fraction of embeddings for which some query or intermediate output hits an undiscovered coordinate. That fraction is at most 1/4 under the dimension condition.
- **Gap.** Whenever the run is good, every intermediate output is outside \(X\) or has an objective gap larger than ε.

The bound holds whenever `execute` stops, because [TrajectoryExecution](../Proofs/TrajectoryExecution.lean) shows that the output equals the output of some trajectory state at a step \(t\le b_0+b_1\).

Averaging the success indicators over embeddings shows that some instance fails with probability greater than \(3/4>\delta\).

### (B) Noise term: rare revelation over many wells

This branch handles budgets where the second term dominates ([QuasarNoiseFailure](../Proofs/QuasarNoiseFailure.lean)).

- **Wells.** There are \(M=64K+64\) candidates, with \(f_j(x)=2\varepsilon\,\xi_\beta(((x-x_0)_j-D/4)/(D/16))\) and \(\beta=2\gamma/3\). The even 1-D profile ξ is quadratic near 0, concave in the transition and affine with slope β beyond 2.
- **Quasar property.** `well_quasar` proves \(\xi'(u)u\ge\gamma\xi(u)\) for every γ ≤ 1. Since \(\nabla f_j(x)^\top(x-x_\star^{(j)})=2\varepsilon\,\xi'(u)u\), each well is γ-quasar-convex with respect to its own minimizer.
- **Oracle.** Near its well, the oracle returns the exact gradient. Elsewhere in \(X\) it returns \(\nabla f_j/\nu\) with probability \(\nu=(64\gamma\varepsilon/(3D\sigma))^2\) and 0 otherwise. This is unbiased, with variance \(\|\nabla f_j\|^2(1-\nu)/\nu\le\sigma^2\).
- **Silent event.** On the event that the first \(K\) coin flips are all "silent", the trajectory is identical for every unvisited candidate. The event has probability \((1-\nu)^K\).
- **Counting.** Any point of \(X\) lies in at most 16 near fields. So the silent run visits at most \(16K\) wells, and its outputs can succeed for at most \(16(K+1)\) candidates.
- **Conclusion.** Summing success probabilities over candidates gives \((1-\nu)^K\le2\delta\) if all candidates succeed. This contradicts \(\nu K\le\tfrac29\log(1/\delta)\) with \(\delta\le1/4\).

## What is new, and comparison with prior work

1. **Deterministic term against randomized algorithms.**
   - [Hinder, Sidford, Sohoni, COLT 2020, arXiv:1906.11985v3](https://arxiv.org/abs/1906.11985), Theorem 3 and Appendix E.2, prove \(\Omega(\gamma^{-1}\sqrt{LR^2/\varepsilon})\) only for **deterministic** first-order methods. They use zero-respecting algorithms plus Carmon et al.'s Proposition 1.
   - Their chain is not a robust zero-chain: the quadratic couplings and \(\Upsilon'(t)\ne0\) for small \(t\ne0\) reveal hidden coordinates. So the randomization technique of [Carmon, Duchi, Hinder, Sidford, arXiv:1710.11606](https://arxiv.org/abs/1710.11606) does not apply verbatim.
   - The present result is, to our knowledge, the first lower bound of this order against randomized algorithms. The new step is the dead-zone, flat-bottom chain together with a direct proof of its quasar-convexity (Lemma Q). The randomization itself uses standard hidden-coordinate counting, which is not claimed as new.
2. **Noise term in high-probability form.**
   - [Saad, Lee, Orabona, arXiv:2502.14060v2](https://arxiv.org/abs/2502.14060), Theorem 3.4, prove an expected-gap lower bound of order \(D\sigma/(\tau\sqrt{\ln(2/\tau)T})\), i.e. \(\sigma^2D^2/(\gamma^2\varepsilon^2\log(2/\gamma))\) calls. Their proof uses Gaussian noise, \(d\ge\log_{16/15}(4/\tau^2)\), and a sufficiently large \(T\).
   - The present bound is for the high-probability criterion. It includes the factor \(\log(1/\delta)\) and has no \(1/\log(1/\gamma)\) loss.
   - At γ = 1 it reduces to the folklore convex high-probability bound.
   - The mechanism is a simple rare-revelation argument and is not claimed as a technical novelty.
3. **Full pair.**
   - **Upper side.** With the repository's [StochasticConstrainedQuasarHighProbability](StochasticConstrainedQuasarHighProbability.lean) method, transferred through the proved inclusion, the complexity on this setup is determined up to logarithmic factors.
   - **Where the pair is not tight.** The upper bound carries a factor \(\log(1/\delta)\) on the deterministic term, and the lower bound does not.
     - **Why the gap is plausibly the upper bound's.** With an exact oracle (σ = 0), the success of a *deterministic* algorithm is a 0/1 event. So a deterministic method with a constant-success guarantee would need no δ-dependence at all.
     - **What is not shown.** The repository method is randomized, and whether it can be derandomized in this constrained setting is not checked. The gap is left open.
   - **Which δ-dependence is tight.** The δ-dependence is shown tight only on the noise term.

Not claimed:
- Optimal constants (they are large).
- Bounds outside the stated regime, including the excluded noise band.
- Strongly quasar-convex lower bounds.
- A lower bound for deterministic oracles on low-dimensional problems.

## How the requirements are met

| Requirement | How it is met |
| --- | --- |
| Lower bound for a popular repository setup | Proved for the repository's constrained quasar-convex problem. |
| Parameters only slightly strengthened | Dimension, Bool seeds and regime conditions only; no structural change. |
| Inclusion into an existing setup | Proved in [HighDimensionalQuasarInclusion](../Proofs/HighDimensionalQuasarInclusion.lean) (`Includes StochasticConstrainedQuasar.spec HighDimensionalConstrainedQuasar.spec`). |
| Tight upper and lower bounds up to logarithms | See the comparison above. |
| Not the (L0,L1) setting | The objective has a globally Lipschitz gradient on X. |

## Limitations

- The dimension requirement is polynomially large, and the constants are conservative.
- The noise band \(0<\sigma<64\gamma\varepsilon/D\) is excluded.
- The seed space is fixed to Bool.
- The hard instances are constrained to a ball. The deterministic hard instance is a nonconvex chain; the noise instances depend on one coordinate each.
- The upper bound carries extra \(\log(1/\delta)\log^2\) factors.
