# Stochastic proximal EF21 with biased compression and homotopy

**Public theorem:** `LongTails/Theorems/ProximalEf21Homotopy.lean`,
`LongTails.Theorems.ProximalEf21Homotopy.result : OracleTemplate.Convergence LongTails.Setups.StochasticProximalEf21.spec budget`.

**Setup:** `LongTails/Setups/StochasticProximalEf21.lean`.

**Algorithm:** `LongTails/Algorithms/ProximalEf21Homotopy.lean`.

**Proofs:** `LongTails/Proofs/ProximalEf21{Step,Bound,Run,Moments,Main,Tuning}.lean`.

## Setup

The intended statement concerns the composite convex objective
`Phi(x) = (1/n) sum_i f_i(x) + psi(x)` on a finite-dimensional real Euclidean
space. The local objectives are convex and differentiable with Lipschitz
gradients. The parameter `L > 0` is the root-mean-square local smoothness.
The extended-valued regularizer is proper, lower-semicontinuous, and convex;
exact proximal access retains projection as a special case. An attained
minimizer `xstar` and a feasible deterministic initial point `x0` satisfy
`norm (x0 - xstar) <= R`, with `R > 0`.

The original setup is unchanged. It assumes conditional unbiasedness and
variance bounds for stochastic gradients, together with conditional
contractiveness for compression. Compression need not be unbiased.
The initialization distribution and conditional oracle laws are specified
explicitly. No finite-sample-space restriction is introduced.

The initial compression and momentum errors are finite. The supplied parameter
`H` bounds `8192 * (Delta0 + L * R^2 + (V0 + W0) / L)`. The target range is
`0 < epsilon <= L * R^2`.

## Algorithm and claimed guarantee

The method runs the existing stage schedule with
`gamma = delta / (1572864 * L)`, `mu_s = 2 * L / 2^s`, and
`alpha_s = mu_s * gamma`. Each iteration performs one exact proximal step,
then a fresh mini-batch of gradients at the new point, a momentum update,
and one compressed correction per worker. Complete state is transferred
between stages without resetting the memories. The output is the terminal
iterate, not an average or a randomly selected iterate.

The claimed criterion is
`integral (Phi(output) - Phi(xstar)) <= epsilon`.
The implementation of `output` uses the supplied `OracleTemplate.execute`.
The executable method definition remains in the setup because its
`allowedAlgorithm` field restricts admissible algorithms to that method;
the algorithm module exposes the algorithm and its executed outputs. This
preserves the no-back-import rule for setups.

For `T = sum_s K_s` and `Nworker = sum_s B_s * K_s`, the intended rates are

```
T = O(L R^2 / (delta epsilon)
      + log(2 + H / (L R^2)) / delta),

Nworker = O(L R^2 / (delta epsilon)
            + sigma^2 R^2 / epsilon^2
            + (1 / delta + sigma^2 / (L^2 R^2))
              * log(2 + H / (L R^2))).
```

The public budget retains the explicit universal constant
`1152921504606846976` from the previous package. Channel 0 counts parallel
raw-gradient calls, hence samples per worker; channels 1 and 2 count
compression rounds and proximal evaluations; channel 3 has zero budget and
is used only to stop the evaluator. The corresponding all-worker gradient
and compression counts are `n * Nworker` and `n * T`. Constructing the supplied
initial memories is outside these counts. The additional proximal model used
in the analysis is not an extra algorithmic oracle call.

## Six proof modules

| Module | Responsibility |
| --- | --- |
| `ProximalEf21Step` | Inner-product identities, weighted averaging and interpolation, proximal-model and functional-change algebra, regularized geometry, and conversion of the public problem assumptions to that geometry. |
| `ProximalEf21Bound` | Upper energy comparison, initialization, expected progress and tracking recurrences, inner Lyapunov contraction and unrolling, and the definitions of the stage-trajectory interface. |
| `ProximalEf21Moments` | Conditional-expectation identities, worker and mini-batch moments, measurability, and integrability propagation tools. |
| `ProximalEf21Run` | Construction of the actual stochastic trajectory from the oracle, state-machine simulation, per-channel budget availability, and equality of the replay with `execute`. No convergence statement is an input to this construction. |
| `ProximalEf21Main` | Stage transfer, homotopy induction, terminal accuracy, and transfer of the guarantee from the constructed trajectory to the actual executed output. |
| `ProximalEf21Tuning` | Scalar Lyapunov coefficient calculations, geometric and logarithmic estimates, stage and batch choices, and explicit sample and round budgets. |

The stage-trajectory definitions precede their construction. The final
homotopy and success lemmas are assembled only in `Main`, preventing an
import cycle between the execution argument and the convergence proof.

The physical proof modules contain the original proof bodies rather than
wrappers importing the old fine-grained files. Helper namespaces and all
existing declaration names are retained. Named local sections keep the
original file-local variables and `open` commands from leaking into the
next group of declarations.

This layout contains nine Lean files and this contribution note. It does not
ship compatibility stubs for the 28 superseded proof modules; those old
source files must not remain alongside the compact ones.

## Contribution and limitations

The intended contribution is a homotopy analysis separating the
compression-dependent iteration term from the stochastic sample term,
while retaining general proximal access, biased compression, and unchanged
state transfer. This reorganization does not add a literature comparison,
a new optimality claim, or new mathematical assumptions.

The bound is in expectation and concerns the terminal iterate. The tuning
uses known numerical bounds, the proximal oracle is exact, a minimizer is
assumed to exist, and initialization costs outside the supplied initial
state remain additional. The explicit universal constant is conservative.
There is no measured verification-time improvement for this restructuring.

## Verification status

This is an **uncompiled structural refactoring of the existing proof
attempt**, not a kernel-checked theorem or an approved contribution.

Static source comparisons performed for this package establish:

- Exactly nine Lean files: one setup, one algorithm, six proof modules, and
  one public theorem file.
- All 449 named declaration texts are unchanged, including all 326 lemma
  and theorem declarations with their proof bodies.
- The setup and algorithm files are byte-for-byte unchanged. In the public
  theorem file only the proof-module import changes to `ProximalEf21Main`.
- Declaration-local `open`, `variable`, `universe`, and noncomputable contexts
  are preserved by named sections.
- The new internal import graph is acyclic and has no imports of deleted
  EF21 modules. There are no direct `import Mathlib` or `import Mathlib.Tactic`
  umbrella imports in the delivered Lean files.
- A static scan found no admitted-proof declarations or added axioms. This
  is not an axiom audit of elaborated proof terms.

These checks do not establish successful Lean elaboration or kernel acceptance.
Build, lint, comparator, and timing results are all **pending**. No verification
claim from the structural example in PR #146 is being transferred to this
package.

The target commands, after migrating the old files, are:

```bash
python3 -u run_comparator.py ProximalEf21Homotopy.lean
```

For the repository-wide submission checks prescribed by `AGENTS.md`:

```bash
./build.sh
./lint.sh
python3 -u run_comparator.py ProximalEf21Homotopy.lean
```

Retain the checkout's existing `Template.lean`, `lean-toolchain`, and
`lake-manifest.json`. A successful validation record should state the exact
repository revision, command exit statuses, and resulting axiom audit;
none is claimed here.
