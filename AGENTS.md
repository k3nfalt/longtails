# longtails

Read these instructions before working in this repository. They record the user's
project preferences; newer explicit user requests take precedence.

## File layout and style

- Use UpperCamelCase for Lean module filenames and new module directories
  (for example, `GdConvex.lean`). Reuse existing directory paths in the current
  layout.
- Put algorithm definitions in `LongTails/Algorithms/` and proof derivations in
  `LongTails/Proofs/`. Do not create separate method folders with different casing.
- Reuse shared assumptions in `LongTails/Setups/` and existing lemmas instead of
  duplicating them.
- Match each setup namespace to its module path, for example
  `LongTails.Setups.GeneralizedSmoothAndConvex`. Public convergence statements
  must name that setup's `spec` explicitly and import its module directly.
- Group related supporting lemmas into cohesive proof modules instead of creating
  a separate Lean file for each helper or small proof step.
- Put public theorem exports in `LongTails/Theorems/` so the audit discovers them.
- Keep public declaration names distinct across modules so `LongTails.lean` can
  import the whole library. Regenerate the root using
  `lake exe mk_all --lib LongTails`; `./lint.sh` checks that it is current.
- Each file in `LongTails/Theorems/` must contain exactly one main convergence
  theorem, `result : Convergence spec budget`. Put distinct mathematical cases in
  separate files. Proof modules use lemmas for supporting results; do not add redundant public convergence/rate
  wrappers or drop a mathematical case merely to reduce the theorem count.
- Do not add explanatory comments or docstrings to Lean files unless requested.
- Do not add README files or extra documentation unless requested. This
  `AGENTS.md` is explicitly requested repository guidance.

## Mathematical correctness and verification

- State the algorithm variant, hypotheses, accuracy criterion, and iteration
  budget precisely. Clarify an ambiguous algorithm variant before implementing it.
- Preserve the requested algorithm family when improving a rate. Use the strongest
  applicable published analysis as the starting point, and distinguish limitations
  of the current proof from lower bounds on the algorithm or problem class.
  Exploration may discover a different proof or algorithm; keep any new algorithm
  within the requested scope.
- Put oracle assumptions in `LongTails/Setups/`. State the exact error or moment
  conditions of the model, with the necessary measurability and integrability
  conditions. For unbiased stochastic gradients with bounded variance, state
  `∫ ω, oracle x ω ∂p = gradient f x` and
  `∫ ω, ‖oracle x ω - gradient f x‖^2 ∂p ≤ σ^2`, using mathlib's
  `IsProbabilityMeasure p`. Do not impose unbiasedness or bounded variance on
  models that do not assume them. Require stochastic oracles to be jointly
  measurable in their point and random-sample arguments.
- Make public theorem statements readable and explicit: give concrete parameter
  formulas once, using local names such as `η` for the step size, `Δ` for the
  initial objective gap, and `K` for the iteration count. Reuse those names
  instead of repeating long expressions. Do not leave tuning choices unspecified.
- Derive explicit formulas for all tuning parameters and budgets from the proved
  convergence bound. Write each `let` budget declaration on one line, with an
  explicit formula rather than an opaque helper or an unspecified constant.
  Prefer one readable budget formula to a collection of tuning cases when it
  preserves the rate. Keep supporting algebra in proof modules.
- In `LongTails/Theorems/`, write each public `budget` definition as one explicit,
  human-readable line in the setup parameters, without local tuning variables.
  Simplify nested fractions, products, and rounding where possible; a universal
  constant-factor increase is acceptable when it preserves the parameter rates.
  Prove that the simplified budget suffices for the actual execution, retaining
  all oracle calls and required terms. Keep the supporting algebra in proof modules.
- Seek the strongest rate justified by the exact setup, and check the primary
  literature before choosing a target rate. Compare assumptions, algorithm
  variants, accuracy criteria, and oracle costs; do not transfer a rate that
  requires stronger assumptions. Distinguish a proved upper bound from a known
  optimal rate, and state any unresolved optimality gap honestly.
- Count every oracle call used by the algorithm, including batching and skipped
  Markov transitions. Connect the stated budget to the actual execution, and
  retain all necessary noise, initialization, and mixing terms.
- Define algorithm outputs in `LongTails/Algorithms/` and name the output in the
  theorem statement so the accuracy claim is directly readable.
- Make the probability measure and stochastic accuracy criterion explicit.
  State expected accuracy using integrals, for example
  `(∫ ω, f (output ω) - f xstar ∂P) ≤ ε`; use explicit probability bounds or
  almost-sure statements for high-probability or almost-sure guarantees.
  Do not use `letI : MeasureSpace ...` to select a hidden distribution for `𝔼`,
  or introduce custom expectation helpers such as `expected` or `sampleMean`.
- State the sampling dependence assumed by the model. For IID sampling, take
  an abstract probability measure `P` and sample variables `ξ`, with
  `h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P`. Reuse the IID
  structure in `LongTails/Setups/StochasticGeneralizedSmoothAndConvex.lean` to bundle
  measurability, `ProbabilityTheory.iIndepFun ξ P`, and marginal laws
  `P.map (ξ k) = p`. Derive any product-measure representation internally from
  independence; do not prescribe `P` as a product measure. For Markov or other
  dependent sampling, state the appropriate dependence assumptions instead of IID.
- Use `execute` from `LongTails/Template.lean` to run oracle algorithms.
- Express minimizer-based accuracy relative to `xstar`, using the setup's
  minimizer assumption. State clearly whether the result
  concerns a last iterate, an average across iterations, or some iterate.
- Keep any finite-sample-space restriction explicit; do not imply that a proof
  covers general probability spaces merely because the oracle assumption does.
- Derive descent, estimator-error, and convergence bounds from the algorithm and
  mathematical assumptions; do not assume the result being proved.
- No `sorry`, `admit`, or added axioms. Keep noise and initialization terms when
  the proof requires them; do not claim a stronger complexity bound than proved.
- Use the pinned `lean-toolchain` and `lake-manifest.json`.
- After changing Lean declarations or imports, run `./build.sh`
  to build the project and `python3 run_comparator.py` to audit public
  convergence results and budgets, allowing only `propext`, `Classical.choice`,
  and `Quot.sound`. The default command only builds; it does not run the audit.
- For comment-only or documentation changes, inspect the diff and run
  `git diff --check`; do not repeat unrelated proof builds.
