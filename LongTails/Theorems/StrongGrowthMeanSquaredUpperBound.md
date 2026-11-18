# Upper half of the tight strong-growth / mean-squared-smoothness characterization

The [main theorem](StrongGrowthMeanSquaredUpperBound.lean) is the upper half of the pair whose contribution is explained in [StrongGrowthMeanSquaredLowerBound.md](StrongGrowthMeanSquaredLowerBound.md). It is **not** a new upper-complexity claim: it transfers the repository's [ProximalStormStrongGrowth](ProximalStormStrongGrowth.lean) theorem to the restricted setup [EuclideanStrongGrowthMeanSquared](../Setups/EuclideanStrongGrowthMeanSquared.lean) through the formal [inclusion](../Proofs/StrongGrowthMeanSquaredInclusion.lean), so that both halves of the characterization are stated for the same specification.

## Statement

The setup is the repository's SGC + mean-squared-smoothness class (convex $f$ on $\mathbb R^d$, minimizer within $R$ of $x_0$, IID same-sample pair oracle $(x,y)\mapsto(g(x,\xi),g(y,\xi))$ with $\int g=\nabla f$, $\int\|g-\nabla f\|^2\le\Gamma^2\|\nabla f\|^2$, $\int\|g(x)-g(y)\|^2\le\bar L^2\|x-y\|^2$), with the parameter restrictions listed in the lower note. The algorithm is the existing accelerated hybrid-proximal-extragradient method with STORM inner solves ([ProximalStorm](../Algorithms/ProximalStorm.lean)), returning its last outer iterate. The theorem proves expected gap at most $\varepsilon$ after

$$
\Big\lceil\sqrt{2\bar L R^2/((1+\Gamma)\varepsilon)}\Big\rceil\cdot\Big\lceil(1+\Gamma)^2\big(4810+3200\log(1+\Gamma)\big)\Big\rceil
$$

oracle calls, every inner and batch call counted. This is exactly the original public budget evaluated at the mapped parameters; the transfer proof (`transfer`) applies the original theorem through the inclusion's validity and admissibility maps, and the success criterion is unchanged.

## Relation to the lower bound

On the restricted regime $2^{26}\sqrt{1+\Gamma^2}\,\varepsilon\le\bar LR^2$ the square root in the first factor exceeds $2^{13}$, so the budget is $O((1+\Gamma)^{3/2}\sqrt{\bar LR^2/\varepsilon}\,\log(e(1+\Gamma)))$, matching the lower theorem's $\lfloor(1+\Gamma^2)^{3/4}\sqrt{\bar LR^2/\varepsilon}/8192\rfloor$ up to $\log(e(1+\Gamma))$ and a universal constant. The method, its analysis, and its comparison with accelerated SGD under strong growth are those of [ProximalStormStrongGrowth.md](ProximalStormStrongGrowth.md); that note's informal lower-bound sketch (zero-respecting algorithms only) is superseded by the formal all-algorithm lower theorem of this pair. Limitations: the dimension and accuracy-regime restrictions of the restricted setup, conservative constants, and the remaining $\log(e(1+\Gamma))$ factor.
