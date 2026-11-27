# Constant-step logistic GD on images: experiments and proof attempts

In Figure 1 of Tyurin, both models can express exactly the same linear classifier. Plain GD trains a readout directly. Joint GD trains a circular two-tap filter and its readout simultaneously. Each method uses the full gradient of mean logistic loss at a **constant** step size. The target is the first iterate with a strictly positive signed score on **every training image**. A single unclassified airplane counts as failure even if the other 4,999 predictions are correct. The proved part of this investigation is a sufficient condition on the data and initialization for plain GD to take many steps. [Theorem and worked example](RareGroupLinearLogisticLowerBound.md) · [Tyurin, ICML 2026, §1.1 and Figure 1](https://proceedings.mlr.press/v306/tyurin26a.html)

## What the experiments show

We drew 2,500 airplanes and 2,500 cars from the CIFAR-10 training split at seed 20261125. The original paper does not identify the subsampling seed. We mapped pixel intensities to $[-1,1]$, flattened in channel-major order, used one circular shift over the flattened vector, and applied no augmentation or bias. The native comparison shares the initial readout between models. The joint model also draws a filter, so its initial predictions differ from plain GD's. The selected-image controls in the contribution note match the models' initial predictions.

| Model | Constant steps, in order | First strictly correct update, in the same order |
|---|---|---|
| Plain | .001, .01, .1, 1, 10, 100 | —, —, —, 328519, **319077**, 323672 |
| Two taps | 1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 1 | 181723, 92786, 46672, **23676**, —, —, — |

A dash means no fit among the first 400,000 checked iterates. The best plotted steps differ by **13.48×** in update count on this draw. These are binary32 measurements on an H100. In the spectral intervention below, the unchanged-data control using a different matrix multiplication layout gave 323,207 and 23,705 at the same two steps. Counting one flagged full-gradient pass per update allows the same loss and gradient information for both models. The joint pass also computes derivatives of the two taps.

| Dataset and training rows | Fastest plain fit on the tested grid | Fastest joint fit on the tested grid |
|---|---:|---:|
| CIFAR-10 airplane/car, 5,000 | 319,077 | 23,676 |
| CIFAR-10 cat/horse (3/7), 5,000 | beyond 400,000 | 90,647 |
| EuroSAT classes 3/7, 5,000 | 91,606 | 6,782 |
| Fashion-MNIST sandal/sneaker (5/7), 5,000 | 375,474 | 115,225 |
| MNIST 0/1, 12,665 | **2,395** | 3,439 |
| MNIST 7/8, 12,116 | **8,230** | 38,398 |

Giving both CIFAR models all 10,000 airplane/car training rows changes feasibility. A positive combination of 3,287 signed, centered images sums to zero. Taking an inner product with any putative strict separator yields a contradiction, so neither parameterization can fit these 10,000 rows. The sample size, feature convention and strict training target matter.

## Ideas tested, and what each established

1. **Brightness as an obstruction for plain GD.** Amplify image means by $A$ and rescale the initial readout to preserve its margins. A signed combination that cancels brightness can retain a negative margin. Small steps then move the residual too slowly, while large steps receive nearly saturated, discrete brightness votes. On a 1,000-image control the best tested plain count went from 18,803 at $A=4$ to 1,186,217 at $A=32$. The quadratic-delay argument has no useful constant at native brightness.

2. **A learned filter that rejects brightness.** A filter with opposite taps keeps adjacent-pixel differences and cancels the mean. On the 5,000 images, an auxiliary calculation minimizing over the brightness coefficient predicted about 22,905 joint updates at step 1/8. A transfer argument for seed 729 at sufficiently large $A$ gives $O(A)$ joint updates against $\Omega(A^2)$ for plain GD. The sufficient sign test failed on the Figure 1 reproduction seed. Fixing a difference filter in advance also removes brightness, so this comparison is specifically with plain GD on the original features.

3. **Which directions oscillate?** At native update 8,192, the fixed step times the leading curvature averaged over the update was about 2. Retaining only the smooth tap and brightness readout gave 1.53; adding both taps and eight image principal directions gave 1.92. Even the first 256 centered image directions, their shifts, brightness and the initial readout and its shift cannot strictly separate all rows. The directions that sustain the oscillation therefore leave something out that matters for the last image.

4. **Progress over two successive updates.** Common separating readouts for pairs of filter orientations, together with bounds on tap displacement, rule out a nonconstant exact two-cycle on this sample up to step 1/8. This leaves long oscillatory transients possible. A proposed invariant sector around the difference filter fails a one-step test even at low loss, with a readout displacement in the cone generated by sample gradients.

5. **A separator robust to oscillations.** One direction constructed from the images keeps the average of the losses at two opposite perturbations small after subtracting the squared perturbation divided by the step. This gives a comparison point valid even for large perturbations at step 1/8. The maximized expression can increase on actual GD steps; ordinary one-step descent does not transfer its margin to those iterates.

6. **A separating readout for every filter.** A single two-column matrix $V$ gives a separating readout $Vc$ for every nonzero tap vector $c$ on these 5,000 images. An integer check verifies one $2\times2$ inequality per row. The readout gradient has a favorable projection onto $Vc$ while a mistake remains, but that direction moves when the filter changes. The unbounded accumulated effect of this motion is the missing part of this argument.

7. **Pair images with their reversals.** Reflection separates smooth and difference features and makes some cross terms cancel. Controls on 7,200 views from 3,600 images satisfy the sufficient margin test. The 10,000 views from all 5,000 originals fail it by a positive-dependence certificate. Reflection changes the training problem.

8. **Change layer scales at fixed initial predictions.** Multiplying the filter by a constant and inversely rescaling the readout changes the updates while preserving all initial scores. A sufficiently large initial difference tap helps control the residual brightness force on amplified images. The required scale and step regime exclude the original initialization at its successful plotted step.

9. **Large steps and failure to fit.** At joint step 1/4 on the native sample, an interval calculation enters a recurrent sequence of 162 classification patterns after 1,750 updates. Every pattern misses at least 1,557 images and the parameter amplitude grows each period. This explains a failed step immediately beside the successful 1/8. It does not estimate the 1/8 hitting time.

10. **Use the same very small step in both models.** On the native 5,000 images, a validated flow comparison gives a joint fit by $\lfloor2095.96875/h\rfloor$ for $0<h\le5\cdot10^{-9}$. An independent raw-margin certificate gives $hT_{\rm plain}>10420$ there. The joint advantage exceeds 4.97 at equal steps in this range. The small-step flow learns two *positive* taps, while the successful 1/8 run learns opposite signs. Extrapolating the bound to 1/8 would erase that difference.

11. **Find images the plain update struggles to correct.** If a signed row points against all the common rows, only the rare group can push plain GD toward correcting it. The formal theorem measures that group's maximum contribution and prices the opening update exactly. A jointly trained filter changes the update directions. On five equally weighted image subsets this gives a test of the mechanism with the starting predictions held fixed. On another 278-image control, merely changing group weights reversed the ranking. This is the approach with the strongest combination of a general Lean result and a direct image experiment. [Bound, finite comparisons and reproduction](RareGroupLinearLogisticLowerBound.md)

12. **Average the two ends of an oscillation.** At center $z$, update the estimated amplitude $a$ by ascending $[F(z+a)+F(z-a)]/2-\|a\|^2/h$, and evolve the center with the two gradients' mean. At joint steps 1/32, 1/16 and 1/8 this predicted 92,772, 46,727 and 23,828 native updates. MNIST 7/8 at 1/16 gave 38,402 predicted against 38,398 measured. For plain GD at step 10, estimates ranged from 321,536 to 372,640 as integration and restart settings varied. Choosing the better of two local amplitude maxima at longer intervals gave no plain fit through 420,000, and the joint predictor missed the escape at 1/4. Selecting the branch and bounding the error in the last margin remain open. [Litman](https://arxiv.org/abs/2604.20446) · [Regis and Chewi, §§3–4](https://arxiv.org/html/2611.08358v1)

13. **Find the stability threshold of that averaged objective.** Its boundedness threshold depends only on the signed images: maximize the norm of a subset sum of adjacent-pixel sums or differences. The resulting critical step lies in $[0.14729,0.14752]$ on native CIFAR and $[0.11356,0.11359]$ on MNIST 7/8. Native GD still fit at 0.20, and the MNIST parameter norm exceeded $10^{20}$ at 0.1134. Global boundedness of the auxiliary optimization is insufficient to decide the behavior from the given initialization.

14. **Reduce just the three largest image directions.** We capped the three largest eigenvalues of the uncentered signed-image second moment $X^\top X/n$ at 40. They were approximately 271, 116 and 54. We adjusted the readout in each model to preserve every opening score. With all 5,000 labels unchanged, plain GD at 10 first fit at **49,702**, and joint GD at 1/8 at **22,941**. In the unchanged-data control with the same numerical layout, the ratio was 13.63; after capping it was **2.17**. This intervention is the strongest direct evidence here about the native gap. It explains which input directions matter empirically. A bound transferring their interaction with the learned filter to the time of the last classification remains open.

## Relation to previous PRs

PR #253 gives finite-radius logistic GD on Tyurin's two-example construction, counting two indexed sample queries per update. PR #279 bounds the remaining iterations after a certified opening through signed spectral work. PR #280 bounds cold-start joint GD on the native split by 28,161 flagged passes using a numerical reference enclosure. The lower bound submitted here instead asks what can be deduced from the signed images and opening predictions before running either method. It gives an all-positive-constant-step obstruction on selected datasets. The native 13.48× ratio remains an experimental result in this contribution. [PR #253](https://github.com/k3nfalt/longtails/pull/253) · [PR #279](https://github.com/k3nfalt/longtails/pull/279) · [PR #280](https://github.com/k3nfalt/longtails/pull/280)
