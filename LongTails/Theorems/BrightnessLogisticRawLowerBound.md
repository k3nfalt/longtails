# First fit of linear logistic GD under brightness contrast

For each labeled image, absorb the label into its feature vector and split it into its coefficient in the constant unit direction and its spatial residual. Write the signed rows as pairs $(R d_i,z_i)$. The scalar $R$ changes the strength of image brightness relative to detail. The classifier starts at $(t/R,w)$, which keeps every initial signed score $t d_i+\langle w,z_i\rangle$ fixed as brightness changes. Each query returns the exact average logistic gradient (in descent direction) and whether all signed scores are strictly positive. The readout takes a constant positive step at each query until first fit, then retains the fitting iterate. The step may be arbitrarily large. [Setup](../Setups/BrightnessLogisticRaw.lean) · [Theorem](BrightnessLogisticRawLowerBound.lean)

## Guarantee

Let $m$ and $D$ bound the absolute nonzero brightness coefficients from below and above, and let $H$ bound all residual norms. Two opposite-brightness rows must have a convex combination with zero brightness and initial signed score at most $-s<0$. Write $b$ for the average of $d_i/(1+\exp(t d_i+\langle w,z_i\rangle))$. The averages of $d_i$ over the positive and negative groups, each divided by the full sample count, must be integer multiples of a common spacing $L>0$. Assume $\operatorname{dist}(b,L\mathbb Z)\ge\delta>0$. Quantized pixels imply commensurability. The initial clearance and the balanced pair require separate checks. Zero-brightness rows are permitted.

Set $B=1+|t|D+H\|w\|$. When $\log R\ge1$ and $16D(1+m\delta/(8H^2))\le\delta R^2$, every positive constant step fails to fit every row through

$$
\left\lfloor \frac{R^2m\delta}{8H^2}\min\left\{1,\frac{s}{2B\log R}\right\}\right\rfloor
$$

full-batch calls, including the stated budget and zero. Thus for fixed cohort and initialization the best-tuned first-fit time is $\Omega(R^2/\log R)$. One call processes all $n$ rows and supplies the fit flag. The same deterministic construction works for every allowed realization of the method. [Gradient dynamics](../Proofs/BrightnessLogisticRawDynamics.lean) · [Oracle execution](../Proofs/BrightnessLogisticRawExecution.lean)

## Why step-size tuning cannot evade the bound

With a small step, the initial deficit on the balanced pair can improve by at most $\eta H^2$ per query. With a larger step, divide the brightness readout by $\eta R$ and consider the scalar update obtained by replacing the sigmoid weights on nonzero-brightness images by hard sign indicators. This scalar orbit starts at $b$ and stays on the shifted lattice $b+L\mathbb Z$. At every point, the clearance leaves an entire brightness-sign group misclassified as long as the accumulated spatial displacement stays small enough. The true sigmoid update incurs an exponentially small error in $\eta R^2 m\delta$. The proof sums this error and controls every row's spatial displacement up to the same first-fit horizon. Balancing the two step regimes gives the logarithm. Its necessity remains open.

## Relation to prior work and the images

Tyurin's Section 5 studies a two-sample perceptron comparison. The bound here applies directly to logistic GD with a finite step, to an arbitrarily large fixed cohort, and simultaneously to all positive step choices for that same dataset. Wu, Bartlett, Telgarsky and Yu study large-step logistic loss convergence, including accelerated loss decay with horizon-dependent tuning. Wen, Wen and Teng study the transition to a stable phase as the step tends to infinity on separable logistic regression. The present obstruction concerns strict first fit under contrast scaling even after independently optimizing the step. [Tyurin, v2](https://arxiv.org/abs/2512.11587v2) · [Wu et al., COLT 2024](https://proceedings.mlr.press/v247/wu24b.html) · [Wen et al., October 2026 preprint](https://arxiv.org/abs/2610.01459v1)

The certificate interprets normalized pixel intensities as exact rationals with denominator 255 (999 for Gisette) and the stored initial weights as dyadic numbers. Floating-point training approximates these real inputs and operations. The signed group sums, initial clearance and balanced negative witness were checked on six paper-related draws, also with the raw classifier initialized to match the joint model's effective initial scores. On the 5,000-image CIFAR draw with the ordinary raw initialization, the lattice clearance is about $1.75\times10^{-8}$. The sufficient contrast threshold is consequently far above the measured range. The theorem gives an asymptotic obstruction with explicit data dependence. The native and moderate-contrast timings provide separate experimental evidence for its explanatory scope.

On the common upper/lower family, the signed difference rows have a unit separator with margin $\gamma>0$. Applying the transpose of the circular difference operator to this separator gives a raw spatial predictor with the same margin, norm at most $\sqrt2$ and zero response to brightness. Scale this predictor by $\log(4n)/\gamma$. Its average logistic loss is at most $1/(4n)$, while any nonfitting point has loss at least $\log(2)/n$. The raw loss has gradient Lipschitz constant at most $(R^2D^2+H^2)/4$. The ordinary convex smooth GD comparison inequality at the reciprocal smoothness step therefore gives a raw first-fit upper bound of order $R^2$ for this fixed, separable cohort. The lower bound leaves a logarithm in $R$ between the two guarantees. An exactly zero-sum fixed filter removes the brightness coordinate altogether and can fit much faster.

[Joint theorem and cross-dataset reproduction commands](BrightnessLogisticFirstFit.md) · [Pretraining certificates](../Experiments/BrightnessLogisticFirstFit/diagnostics.py)
