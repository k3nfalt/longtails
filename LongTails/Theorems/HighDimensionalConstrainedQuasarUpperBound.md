# High-probability upper bound on the high-dimensional constrained quasar setup

The [upper theorem](HighDimensionalConstrainedQuasarUpperBound.lean) is the matching upper half of the pair whose lower half is [HighDimensionalConstrainedQuasarLowerBound](HighDimensionalConstrainedQuasarLowerBound.md). It is not a new algorithm.

## Statement

The [setup](../Setups/HighDimensionalConstrainedQuasar.lean) is the repository's [StochasticConstrainedQuasar](../Setups/StochasticConstrainedQuasar.lean) problem. Its parameters are specialized to \(\mathbb R^d\), Bool seeds and the regime stated in `valid`. Its admissibility and success predicates are literally those of the original setup.

[HighDimensionalQuasarInclusion](../Proofs/HighDimensionalQuasarInclusion.lean) proves the inclusion `Includes StochasticConstrainedQuasar.spec HighDimensionalConstrainedQuasar.spec`. The theorem therefore reuses the algorithm and proof of [StochasticConstrainedQuasarHighProbability](StochasticConstrainedQuasarHighProbability.lean) at the mapped parameters. The budget per channel is

\[
\left\lceil2^{96}\,(2+\lceil8\log(8/\delta)\rceil)\,(1+\mathrm{clog}_2\lceil2+LD^2/(\gamma^2\varepsilon)\rceil)^2\left(1+\frac{\sqrt{LD^2/\varepsilon}}{\gamma}+\frac{\sigma^2D^2}{\gamma^2\varepsilon^2}\right)\right\rceil ,
\]

with \(\Pr\{\hat x\in X,\ f(\hat x)-f(x_\star)\le\varepsilon\}\ge1-\delta\).

## Role in the contribution

Compared with the lower budget \(\lfloor\sqrt{LD^2/\varepsilon}/(10^4\gamma)+\sigma^2D^2\log(1/\delta)/(8192\gamma^2\varepsilon^2)\rfloor\), the two theorems agree up to:

- a factor \(\log(1/\delta)\,\log^2(LD^2/(\gamma^2\varepsilon))\) on the deterministic term;
- a factor \(\log^2(LD^2/(\gamma^2\varepsilon))\) on the noise term;
- universal constants.

The lower bound does not match the \(\log(1/\delta)\) on the deterministic term. This term may be removable. With an exact oracle, a deterministic method succeeds either always or never. This method, however, uses private randomness, and its derandomization is not studied here.

The algorithm, its analysis, and the novelty of the original high-probability method are documented in [StochasticConstrainedQuasarHighProbability](StochasticConstrainedQuasarHighProbability.md). Nothing new is claimed for them here. This theorem only places that method on the restricted setup, so that the pair is stated for a single specification.
