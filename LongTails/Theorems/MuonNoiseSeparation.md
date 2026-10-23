# Momentum-free Muon versus SGD and normalized SGD under spectral smoothness and row-profile noise

The [main theorem](MuonNoiseSeparation.lean) proves an oracle-complexity upper bound for momentum-free batched Muon on the whole class of spectrally smooth matrix objectives with a nuclear-norm noise profile. The [lower-bound module](../Proofs/SeparationLower.lean) proves, inside the same Lean [setup](../Setups/BatchedSpectralSmooth.lean), that every SGD and every Frobenius-normalized SGD run in the same constant-hyperparameter family needs a factor \(r-1\) more oracle calls on explicit hard instances of the class, where \(r=\min(m,n)\) (up to a logarithm for normalized SGD).

**What is new.**
- The Muon upper bound is **not** new. It is Tao, Yu and Zhang's Thm 4 for the same momentum-free batched algorithm (their Alg. 2), restated under the slightly weaker row-profile noise condition and with explicit constants.
- The main new result is the lower bound for Frobenius-normalized SGD. To our knowledge, it is the first lower bound for Euclidean-normalized SGD under nuclear-norm (ℓ1-type) stationarity.
- The SGD lower bound is a self-contained, formally verified matrix and batch version of known results (Jiang–Maladkar–Mokhtari Thm 4.1; Tao–Yu–Zhang Thm 3). It is not claimed as a new mathematical result.

## Problem class, oracle, and accuracy

Matrices \(X\in\mathbb R^{m\times n}\) are stored as `Space m n`, with spectral norm \(\|\cdot\|_{op}\) and nuclear norm \(\|\cdot\|_*\). An instance \(f\) with public parameters \(L,\Delta,s,\varepsilon,X_0\) is admissible when:
- \(f\) is differentiable and \(\|\nabla f(X)-\nabla f(Y)\|_*\le L\|X-Y\|_{op}\) for all \(X,Y\). This is the spectral smoothness of Shen et al. (arXiv 2505.23737), Pethick et al. (ICML 2025) and Tao–Yu–Zhang (arXiv 2605.06615, Assumption 2).
- Some \(f_{\min}\le f\) satisfies \(f(X_0)-f_{\min}\le\Delta\).
- The oracle \(G(X,\omega)\) is jointly measurable, integrable and unbiased. It has a **row noise profile**: there are an orthonormal basis \((b_i)\) of \(\mathbb R^m\) and \(\sigma_i\ge0\) with \(\sum_i\sigma_i\le s\) and \(\mathbb E\|(G-\nabla f)^\top b_i\|^2\le\sigma_i^2\). This is the existing `FiniteVarianceSpectralSmooth.GradientModel`. It is implied by the one-sided condition \(\mathbb E[NN^\top]\preceq\Sigma^2\), \(s=\|\Sigma\|_*\), of ASGO (NeurIPS 2025) and Tao–Yu–Zhang, so the class is at least as large as theirs.
- Samples are IID under an abstract probability measure.

The accuracy criterion is \(\mathbb E\|\nabla f(\hat X)\|_*\le\varepsilon\) under the product of the algorithm seed and the oracle law, with measurability and integrability of the output gradient norm.

## The common algorithm family

`allowedAlgorithm` (via `FollowsBatched`) fixes a step size \(\eta>0\), a batch size \(B\ge1\) and a horizon \(T\), all constant, and the update
\[
X_{t+1}=X_t-\eta\,\mathrm{dir}(\bar G_t),\qquad \bar G_t=\tfrac1B\textstyle\sum_{j<B}G(X_t,\omega_{Bt+j}).
\]
The output is the pre-update iterate \(X_\tau\), with \(\tau\) uniform on \(\{0,\dots,T\}\) and drawn from the algorithm seed. The output is pinned for every budget at least \(B(T+1)\), so extra calls cannot be used for selection. Every oracle call is counted: the cost is \(B(T+1)\). Three directions share this exact family ([algorithms](../Algorithms/BatchedDirection.lean)):

| Method | Direction |
|---|---|
| Muon, momentum \(\beta=0\) | \(\mathrm{dir}=\mathrm{polar}\), with \(\mathrm{polar}(0)=0\) |
| SGD | \(\mathrm{dir}=\mathrm{id}\) |
| NSGD (Hazan–Levy–Shalev-Shwartz 2015) | \(\mathrm{dir}(G)=G/\|G\|_F\), with \(0\mapsto0\) |

Tuning is unrestricted within the family: every \(\eta>0\), \(B\ge1\) and \(T\) is allowed, and the parameters may depend on \(L,\Delta,s,\varepsilon\).

## Results

**Muon upper bound (the Lean `result`).** With \(\eta=\varepsilon/(2L)\), \(B=\lceil64s^2/\varepsilon^2\rceil+1\) and \(T=\lceil8L\Delta/\varepsilon^2\rceil\),
\[
\mathbb E\|\nabla f(X_\tau)\|_*\le\varepsilon\quad\text{using}\quad
\Big(\big\lceil\tfrac{64s^2}{\varepsilon^2}\big\rceil+1\Big)\Big(\big\lceil\tfrac{8L\Delta}{\varepsilon^2}\big\rceil+1\Big)
=O\!\Big(\tfrac{L\Delta}{\varepsilon^2}\big(1+\tfrac{s^2}{\varepsilon^2}\big)\Big)
\]
calls, for every admissible instance, every \(m,n\) and every \(X_0\).

The proof uses three facts:
- the spectral descent inequality \(f(X-\eta P)\le f(X)-\eta\langle\nabla f,P\rangle+L\eta^2/2\) for \(\|P\|_{op}\le1\);
- \(\langle\nabla f,\mathrm{polar}(\bar G)\rangle\ge\|\nabla f\|_*-2\|\bar G-\nabla f\|_*\);
- \(\mathbb E\|\bar G-\nabla f\|_*\le s/\sqrt B\) from the row profile.

**Lower bounds (supporting lemmas `sgd_lower_bound` and `nsgd_lower_bound`).** Let \(r=\min(m,n)\ge2\) and \(L\Delta\ge128\varepsilon^2\). For **every** \(\eta>0\), \(B\ge1\), \(T\), and every algorithm \(A\) in the family with the given direction, there is an instance satisfying exactly the setup's `admissible` predicate such that success with budget \(B(T+1)\) forces:
\[
\text{SGD:}\quad B(T+1)\ \ge\ \frac{(r-1)\,L\Delta s^2}{1728\,\varepsilon^4},
\]
\[
\text{NSGD:}\quad B(T+1)\ \ge\ \frac{(r-1)\,L\Delta s^2}{2.1\cdot10^{7}\,\varepsilon^4\,\Lambda},\qquad
\Lambda=2+\log\!\big(1+s\sqrt r/\varepsilon\big),
\]
where the NSGD bound additionally assumes \(\Lambda\le(r-1)L\Delta/(256\varepsilon^2)\), a mild condition that excludes only astronomically large noise.

**Separation.** In the noise-dominated regime \(s\ge\varepsilon\), Muon's cost is \(O(L\Delta s^2/\varepsilon^4)\) on the whole class. SGD needs \(\Omega(rL\Delta s^2/\varepsilon^4)\) and NSGD needs \(\Omega(rL\Delta s^2/(\varepsilon^4\log(e+s\sqrt r/\varepsilon)))\) on instances of the same class, with the same output rule, sample accounting and hyperparameter freedom. The ratio grows linearly in \(r=\min(m,n)\), up to a logarithm for NSGD.

## Hard instances and mechanism

Write \(d_i(X)=X_{ii}-(X_0)_{ii}\) for \(i<r\). The instances are diagonal but nonlinear, and they couple coordinates through the methods' normalization:
\[
f(X)=\tfrac{\ell}{2}d_0^2+c\sum_{i=1}^{r-1}\psi(d_i),\qquad \ell=\tfrac L2,\quad (r-1)c=4\varepsilon,
\]
where \(\psi\) is a pseudo-Huber valley \(\sqrt{w^2+(u-D)^2}\) with \(w=8\varepsilon/L\) and \(D=\Delta/(4\varepsilon)\). The noise is Gaussian on the stiff entry only: \(G=\nabla f+s\,\omega E_{00}\). Membership in the class is checked in Lean ([instance](../Proofs/SeparationInstance.lean), [model](../Proofs/SeparationModel.lean)): \(\|\nabla f(X)-\nabla f(Y)\|_*\le(\ell+(r-1)c/w)\|X-Y\|_{op}=L\|X-Y\|_{op}\), the gap is at most \(\Delta\), and the row profile is \((s,0,\dots,0)\).

The mechanism is **noise throttling**:
- Any small nuclear gradient requires both a stiff coordinate within \(O(\varepsilon/\ell)\) of its minimizer and the \(r-1\) flat coordinates to travel a distance \(\approx\Delta/\varepsilon\).
- **SGD.** Each flat coordinate moves only \(\eta c=4\eta\varepsilon/(r-1)\) per step, while the stiff noise forces \(\eta\lesssim\varepsilon^2B/(\ell s^2)\). The proof uses the exact Gaussian law of the stiff iterate and covers every \((\eta,B)\) ([SGD proof](../Proofs/SgdSeparation.lean)).
- **NSGD.** The stiff noise dominates the Frobenius normalizer, so each flat coordinate moves only about \(\eta c/\sigma'\) per step, with \(\sigma'=s/\sqrt B\). The stiff coordinate makes \(\pm\eta\)-scale kicks.
- **Muon.** The polar factor handles every diagonal direction separately, so noise on one direction does not slow the others.

The NSGD proof ([process](../Proofs/NsgdProcess.lean), [bounds](../Proofs/NsgdBounds.lean), [window](../Proofs/NsgdWindow.lean), [regime](../Proofs/NsgdRegime.lean)) combines:
- **Travel.** The expected flat travel is at most \(\eta c\,\mathbb E[1/\max(|a|,b_0)]\le\eta c(2+\log(\sigma'/b_0))/\sigma'\) per step, by a Gaussian small-ball bound. Success forces the flat block to cross its valley within half the horizon with probability at least \(1/2\).
- **Kick pairing.** \(|x_t|+|x_{t+1}|\ge\eta|h_t|\) gives \(\mathbb E|x|\gtrsim\eta\), so \(\eta\lesssim\varepsilon/\ell\).
- **Window pairing.** Over windows of length \(k\approx\sigma'/(\eta\ell)\), the stiff displacement is a martingale with \(\mathbb E M^2\gtrsim k\) and \(\mathbb E M^4\le112k^2\), plus a drift controlled by \(\ell\,\mathbb E|x|/\sigma'\). The pointwise inequality \(|M|\ge M^2/a-M^4/(4a^3)\) gives \(\mathbb E|x|\gtrsim\min(\sqrt{\eta\sigma'/\ell},\eta\sqrt T)\), so \(\eta\lesssim\varepsilon^2/(\ell\sigma')\).

Combining these bounds gives \(T\gtrsim D\ell\sigma'^2/(\varepsilon^2c\Lambda)\), and hence \(N=TB\gtrsim D\ell s^2/(\varepsilon^2c\Lambda)\).

When \(B\) is so large that \(\sigma'<4\sqrt{r-1}\,c\), noise no longer throttles. Here the proof uses noise-free instances with \(\ell=0\) ([lattice argument](../Proofs/NsgdLattice.lean)). NSGD then moves the flat block on the lattice \(h\mathbb Z\), with \(h=\eta/\sqrt{r-1}\).
- If \(h<2w\), a single valley forces \(T\gtrsim L\Delta/\varepsilon^2\), and \(B\gtrsim(r-1)s^2/\varepsilon^2\) gives the same total bound.
- If \(h\ge2w\), a two-wall valley instance with objective gap \(f(X_0)-\inf f\le32\varepsilon^2/L\le\Delta\) traps NSGD in an exact 2-cycle with \(\|\nabla f\|_*\ge2\varepsilon\) at every iterate.

## Closest prior work

| Work | What it proves | Relation to this result |
|---|---|---|
| Tao, Yu, Zhang, *When and why SignSGD outperforms SGD* ([arXiv 2605.06615](https://arxiv.org/abs/2605.06615), NeurIPS 2026 poster) | Muon upper bound (their Thm 4, for the momentum-free batched msign method, their Alg. 2) under the one-sided noise class; SGD lower bound for constant step size, \(B=1\), and \(\mathbb E\min_t\) (Thm 3, via Jiang et al.); a lower bound for Muon itself (Thm 5, under \(\mathbb E\min_t\)) | Our upper bound is their Thm 4 for the same algorithm, under the slightly weaker row-profile noise and with explicit constants. They give no lower bound for normalized SGD |
| Jiang, Maladkar, Mokhtari ([arXiv 2406.04592](https://arxiv.org/abs/2406.04592), COLT 2025), Thm 4.1 | Vector SGD lower bound in ℓ1 geometry, constant step size | A best-iterate lower bound already implies the uniform-output one, and batching reduces to variance \(\sigma^2/B\) (up to their range condition on \(T\)). Our SGD bound is a self-contained formal matrix and batch version, not a new mathematical result |
| Xie, Wang, Wu, Li, *A tale of two geometries* ([arXiv 2511.20584](https://arxiv.org/abs/2511.20584), Thm 4.9) | Lower bound for ℓ∞-normalized steepest descent with momentum (signSGD-M) at fixed hyperparameters | Prior art for fixed-hyperparameter lower bounds of a normalized method in ℓ∞ geometry. It does not cover Euclidean-normalized SGD |
| Yadav, Xie, Wang, Li ([arXiv 2512.00763](https://arxiv.org/abs/2512.00763) v2) | GD lower bounds in a softmax unigram model | Their conclusion lists a lower bound for normalized GD as open in their model; our NSGD bound is in a different (stochastic, spectral-smooth) model |
| Hübler, Pethick, Sra ([arXiv 2606.14560](https://arxiv.org/abs/2606.14560)), Thms 3.7–3.8 | Class lower bounds that Muon matches; Euclidean methods compared by converting upper bounds | They give no algorithm-specific SGD or NSGD lower bound |
| Hazan, Levy, Shalev-Shwartz (NeurIPS 2015) | NSGD | The algorithm we lower-bound |
| Ghadimi, Lan (SIOPT 2013) | Randomized output rule | The output rule shared by all three methods |

Literature checks were made with search-engine coverage of arXiv up to 2026-10-22 and of the public NeurIPS 2026 listings. The full NeurIPS 2026 accepted list and OpenReview could not be browsed exhaustively.

## Limitations

- **Constants and crossover dimension.** The constants are very small (\(1/1728\) for SGD and about \(1/(2.1\cdot10^{7})\) for NSGD). With \(s\ge\varepsilon\) and \(L\Delta\ge128\varepsilon^2\), Muon's budget is at most about \(529\,L\Delta s^2/\varepsilon^4\). The proved lower bounds exceed it only when \(r-1\gtrsim9\cdot10^{5}\) for SGD and \(r-1\gtrsim1.1\cdot10^{10}\,\Lambda\) for NSGD. The result therefore establishes the order of the separation (linear in \(r\) versus independent of \(r\)), not a speedup at practical matrix sizes. Simulations at \(r=8\) and \(r=32\) showed the effect, but they are not part of the result.
- **Accuracy criterion.** The separation is specific to nuclear-norm stationarity, the established criterion for Muon (Shen et al.; Tao–Yu–Zhang; Hübler–Pethick–Sra). Under Frobenius stationarity no class-wise separation is possible: the Frobenius smoothness constant is at most \(L\), \(\mathbb E\|N\|_F^2\le s^2\), and SGD is minimax optimal there (Arjevani et al.).
- **Methods not compared.** Shampoo, AdaGrad, ASGO, momentum methods and accelerated methods are not compared.
- **Budget.** The lower bounds are stated at budget exactly \(B(T+1)\), the cost of a full run. Truncated runs are outside the family's specification.
- **Tightness.** Converting Euclidean upper bounds gives SGD and NSGD costs within a factor \(r^2\) of Muon's on this class. We prove a factor \(r\) (\(r/\log\) for NSGD), not a tight characterization.
- **Hyperparameter family.** The lower bounds cover constant \(\eta\) and \(B\) with no momentum (\(\beta=0\)) and the uniform pre-update output. They do not cover step-size schedules, momentum variants, best-iterate (\(\mathbb E\min_t\)) or last-iterate outputs. For last-iterate NSGD, a parity effect lets even iterates return the stiff coordinate near \(0\) when \(\eta\ell\gg\sigma'\); the uniform rule removes this. The regime-\(H\) instances fail every output rule.
- **Instances.** The hard instances are diagonal and coordinate-separable in \(f\); the coupling comes from the algorithms' normalization. The row-profile class is not transpose-symmetric, although the hard instances are.
- **Upper bound.** The Muon upper bound is Tao–Yu–Zhang's Thm 4 for the same algorithm, restated under row-profile noise with explicit constants, and is not claimed as new. Their Muon lower bound (Thm 5, under \(\mathbb E\min_t\)) applies to Muon itself.

## How the requested scope is met

The research direction asked whether Muon is provably better than SGD and NSGD in a practical setup that has not yet been investigated, in the spirit of the existing Adam result.
- All three methods are run in one Lean-specified family: the same oracle, sample accounting, output rule and constant hyperparameters.
- Muon's upper bound holds on the whole standard spectral-smooth class.
- Both competitors provably need a factor \(\min(m,n)-1\) more calls, up to a log for NSGD, on members of that same class.
- The setting is minibatch training of a matrix parameter with noise concentrated in few directions, compared at matched hyperparameter freedom. Low-rank or low-stable-rank gradient noise is the motivation for one-sided noise models in ASGO and Tao–Yu–Zhang and for the low-stable-rank analysis of Davis–Drusvyatskiy ([arXiv 2512.04299](https://arxiv.org/abs/2512.04299)). The single-direction Gaussian noise of the hard instances is a stylized extreme of that model. We found no prior lower bound for normalized SGD in this setting.
