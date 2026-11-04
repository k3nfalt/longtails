# SharpMomentumFiniteVarianceHighProbability: novelty assessment

The [theorem](../../LongTails/Theorems/SharpMomentumFiniteVarianceHighProbability.lean), under its [setup](../../LongTails/Setups/UscgHighProbability.lean), runs [bias-corrected raw momentum](../../LongTails/Algorithms/UscgSharpConfidence.lean) and proves \(\Pr\{T^{-1}\sum_{t<T}\|\nabla f(x_t)\|_{N,*}>\epsilon\}\le\delta\) for the recorded **pre-update trajectory**.

Here \(f:\mathbb R^d\to\mathbb R\) is globally lower bounded, with initial gap \(\le\Delta\), norm-to-dual smoothness \(L>0\), and Euclidean smoothness \(L_2\). The jointly measurable, unbiased IID single-point oracle has centered Euclidean variance \(\le\sigma^2\). The norm's unit ball has Euclidean radius \(\le R\), and \(\|z\|_{N,*}\le\zeta\|z\|_2\); \(d\) is any finite dimension, \(\epsilon>0\), \(\Delta,\sigma,L_2\ge0\), \(R,\zeta>0\), \(0<\delta<1/2\).

The budget **for each channel—gradients and exact measurable unit-ball LMOs—is**
\[
 O\!\left[
 \left(1+\frac{\zeta^2\sigma^2}{\epsilon^2}\right)
 \left(1+\frac{L\Delta}{\epsilon^2}
       +\frac{\sqrt{L\Delta}}{\epsilon}\log\frac2\delta\right)
 \right].
\]
If \(2L\Delta\le\epsilon^2\), exactly one call per channel records only \(x_1\). Otherwise \(\alpha=(2+65536\zeta^2\sigma^2/\epsilon^2)^{-1}\), \(\eta=4\Delta/(\epsilon T)\), and weights \(\alpha/[1-(1-\alpha)^t]\) start from zero momentum. Tuning/stopping require the displayed bounds; \(R,L_2\) do not enter the budget. Compliance with the algorithm/output restriction is proved; the execution bridge charges both channels and transfers abstract IID sampling.

The table uses identical HP average-gradient accuracy with \(2L\Delta>\epsilon^2\). Rows 1–2 specialize to Euclidean geometry, \(R=\zeta=1\), and canonical normalized directions; all bounds suppress universal constants.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Hübler–Fatkhullin–He, [Thm. 4](https://arxiv.org/html/2410.13849v3#S3.SS2), retuned; [AISTATS 2025](https://proceedings.mlr.press/v258/hubler25a.html), checked revision **2025-07-09** | Gradients: \(O((1+\sigma^2/\epsilon^2)(1+L\Delta/\epsilon^2)\log(2/\delta))\) → \(O((1+\sigma^2/\epsilon^2)[1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon])\). | Factor \(\min\{\log(2/\delta),\sqrt{L\Delta}/\epsilon\}\) for \(L\Delta\ge\epsilon^2\); unbounded only if both grow. Row 3 removes this advantage. | None on this overlap. | None. | Previous LMOs: \(O((1+L\Delta/\epsilon^2)\log(2/\delta))\); current LMOs equal its gradient count. No uniform LMO gain. |
| Repository-only [MuonTraining.training_tuned_tail](../../LongTails/Proofs/MuonTraining.lean), **2026-10-21**, commit 31eb9070; one-row specialization | Gradients and LMOs: \(O((1+\sigma^2/\epsilon^2)[1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log^2(2(1+\sigma^2/\epsilon^2)(1+L\Delta/\epsilon^2)/\delta)/\epsilon])\) → \(O((1+\sigma^2/\epsilon^2)[1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon])\). | Factor \(\log(1/\delta)\) if \(\log(1/\delta)\ge\max\{\sqrt{L\Delta}/\epsilon,\log(2(1+\sigma^2/\epsilon^2)(1+L\Delta/\epsilon^2))\}\); shared terms can mask improvement elsewhere. | None on this overlap; no dominance over matrix row-profile geometry asserted. | None: this training lemma already controls the trajectory average. | Raw EMA already had logarithmic-confidence guarantees; its validated-point theorem is a different output. |
| [Existing fresh-minibatch reduction](../../LongTails/Theorems/FiniteVarianceMuonHighProbability.md), independently checked below; **not a published theorem** | Gradients: \(O((1+\zeta^2\sigma^2/\epsilon^2)[1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon])\) → \(O((1+\zeta^2\sigma^2/\epsilon^2)[1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon])\). | **None: same order.** | None; same problem/oracle class. | None. | Previous LMOs: \(O(1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon)\), fewer by \(1+\zeta^2\sigma^2/\epsilon^2\). Exclusion by allowedAlgorithm cannot establish an advantage. |

Row 1 follows from batch size \(\lceil C(1+\sigma^2/\epsilon^2)\rceil\), step \(c\epsilon/[L\log(2/\delta)]\), \(C(1+L\Delta/\epsilon^2)\log(2/\delta)\) iterations, and initial self-bounding; blindly substituting Corollary 5's tuning gives a weaker comparison. Row 2 substitutes \(e=\epsilon/2,\gamma=\delta,s=\sigma\) in the actual training lemma.

**Reduction check.** With fresh batches \(b=\lceil C(1+\zeta^2\sigma^2/\epsilon^2)\rceil\), the nonnegative LMO alignment deficit has conditional mean \(\le2\zeta\sigma/\sqrt b\), and is \(\le4\sqrt{L\Delta}\) before first exit from \(f\le f(x_1)+\Delta\). Exponential concentration of its stopped total controls every prefix, giving row 3 over \(K\) iterations with step \(4\Delta/(\epsilon K)\). This verifies the note's sample order; it does not prove the persistent path bound, which uses a [tilted quadratic EMA potential](../../LongTails/Proofs/CappedMomentumProcess.lean) and [tracking/localization](../../LongTails/Proofs/UscgSharpProbability.lean). Exponential-potential analysis without a horizon logarithm already exists for clipped SGD: [Nguyen–Ene–Nguyen, Thm. 5.1](https://arxiv.org/html/2304.01119v2#S5).

The separate [execution_frontier](../../LongTails/Proofs/UscgSharpLowerResult.lean) constructs globally admissible scalar convex witnesses, \(R=\zeta=1,L_2=L\), for **every** constant \(0<\alpha<1\), constant \(\eta>0\), and exact LMO, with that bias correction. Failure probability exceeds \(\delta\) when
\[
 \frac{\sigma^2}{\epsilon^2}\ge8192,\quad
 \frac{L\Delta}{\epsilon^2}\ge256,\quad
 \log\frac1\delta\ge256\left(1+\log\frac{\sigma^2}{\epsilon^2}+\log\frac{L\Delta}{\epsilon^2}\right),\quad
 1\le T\le\frac{\sigma^2\sqrt{L\Delta}}{262144\,\epsilon^3}\log\frac1\delta.
\]
Its dependencies combine mixing necessity, insufficient-step ramps, and rare-shock quadratic excursions, then bridge to actual execution with unconditional IID probabilities. The remaining gap is
\[
 O\!\left(1+\frac{\sqrt{L\Delta}}{\epsilon\log(1/\delta)}\right)
 =O(1+\sqrt D/\ell),\qquad D=L\Delta/\epsilon^2,\quad\ell=\log(1/\delta).
\]
Full leading-rate matching additionally requires \(\ell\ge\sqrt D\). The lower does not cover arbitrary schedules allowed by the setup, batching, last-iterate output, constrained SCG, or all algorithms.

Existing [Buzaglo–Kornowski, Thm. 8.20, 2026-10-09 preprint](https://arxiv.org/html/2610.13787v1) instead bounds constrained expected FW gaps; [Suvorikova et al., Cor. A.7, 2026-09-26 preprint](https://arxiv.org/html/2609.32962v1) uses rare contamination for averaged SGD. The additional lower-bound work is uniform tuning necessity, not the shock distribution itself.

**Comparison checks.** [Sfyraki–Wang](https://arxiv.org/html/2506.04192v4), [ICML 2026](https://proceedings.mlr.press/v306/sfyraki26a.html), v4 **2026-08-25**, Thm. 5 clips single-point gradients and bounds true gradients; only Thm. 6 adds samplewise smoothness and paired queries. Their constrained FW gaps and [1-SFW's expected nonconvex gap](https://proceedings.mlr.press/v108/zhang20i/zhang20i.pdf) (AISTATS 2020, Thm. 4/Algorithm 2: two point queries per sample) are not this HP metric; convex objective-error rates cannot substitute. [Hübler–Pethick–Sra](https://arxiv.org/html/2606.14560v1), **v1 2026-06-12 preprint**, Thms. 3.1/3.5 give expectation bounds with native-norm moment/geometry factors. [Chayti–Fakhouri](https://arxiv.org/html/2605.15350v2), **v2 2026-10-09 preprint**, Thms. 1–2 concern expected composite constrained gaps; their GLMO reduces to an ordinary LMO for a scalar linear outer function.

Searches on **2026-11-03 UTC** covered arXiv revisions and official proceedings through **2026-10-31**, including sources beyond the companion: [Armacki et al., v2 2026-02-10, Thm. 3](https://arxiv.org/html/2507.09093v2) bounds a capped stationarity metric with growing batches. Chezhegov–Gorbunov's [accepted-NeurIPS listing](https://eduardgorbunov.github.io/publications.html) yielded no accessible manuscript/version date. The companion's scoped formal claims agree with the inspected dependencies, but the selected files are untracked, so historical priority is uncertain. No compilation or axiom audit was run for this review.

**Supplied ICLR full text checked.** The user-provided `25501_High_Probability_Bounds_.pdf` is [Li–Tang–Zhu–Liu, ICLR 2026](https://proceedings.iclr.cc/paper_files/paper/2026/hash/2b1bb4f09ccb1013a3e68392bd714349-Abstract-Conference.html), *High Probability Bounds for Non-Convex Stochastic Optimization with Momentum* (SHA-256 `0ee6a258a20968bf6104059b002b73f19fdd98e3ff670a0b7f92eaf71a6b2129`). This supplied conference PDF resolves the online-access failure; no unknown later revision is assumed. Algorithm 1 is unnormalized Polyak momentum for empirical risk, with Theorem 3.1 using decreasing steps proportional to \(t^{-1/2}\). Assumption 2.1 requires samplewise smoothness, and Assumption 2.9 requires \(\mathbb E[\exp((\|\text{noise}\|/K)^{1/\theta})]\le2\), \(\theta\ge1/2\). For \(\theta>1/2\), Theorem 3.1 additionally requires Assumption 2.5, \(\eta_t\|\nabla F_S(x_t)\|\le G\); the sub-Gaussian case does not require that condition. Its HP average-squared-gradient guarantee **does** imply our Euclidean average-gradient target by Jensen/Cauchy–Schwarz, so the metric is not an exclusion. However, its tail scale \(K\) cannot be bounded using variance alone: no fair total-call formula in only our \(L,\Delta,\sigma,\epsilon,\delta\) follows. Thus it does not establish the same finite-variance guarantee, and no rate dominance over its stronger-assumption regime is claimed. The resumed reviewer verified these distinctions and retained INCONCLUSIVE; after repeated transport failures, the supervising agent incorporated this correction. The initial report and follow-up log are preserved separately.

**Conclusion**

**The result sharpens persistent momentum, but establishes no problem-class optimization advantage.** Fresh-minibatch normalized descent matches its sample order under identical assumptions and HP trajectory accuracy,
\[
 N_{\rm batch},N_{\rm momentum}
 =O\!\left((1+\zeta^2\sigma^2/\epsilon^2)
 [1+L\Delta/\epsilon^2+\sqrt{L\Delta}\log(2/\delta)/\epsilon]\right),
\]
while batching omits the noise multiplier from its LMO count. No better total-call order survives that comparison; at \(\sigma=0,L\Delta\ge\epsilon^2\), deterministic normalized descent uses \(O(1+L\Delta/\epsilon^2)\) calls and wins when \(\log(1/\delta)\gg\sqrt{L\Delta}/\epsilon\).

Against the repository's raw EMA, the gain is concrete: fixing \(L\Delta/\epsilon^2\ge1\) and positive \(\sigma/\epsilon\), confidence cost falls from quadratic to linear in \(\log(1/\delta)\). The lower rules out every constant memory/step tuning in its stated regime, with full matching only when \(\log(1/\delta)\ge\sqrt{L\Delta}/\epsilon\). This potentially meaningful method characterization addresses the persistent-memory obstacle identified in Hübler–Fatkhullin–He's Appendix D.3; it does not establish universal minimax optimality.

Literature priority remains unresolved: the inaccessible convex-momentum manuscript could overlap the scalar characterization. Its missing hypotheses, outputs, and version history prevent treating an unsuccessful competitor search as proof of novelty. The supplied ICLR paper has now been checked and requires stronger tails; its squared-gradient metric converts to our target, so it is not excluded on that basis. The defensible contribution is a sharper raw-momentum guarantee and a restricted matching confidence obstruction, with no established improvement over batching.

**Verdict: INCONCLUSIVE. Confidence: medium.**
