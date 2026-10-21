# LongTailsOnline

Read the repository root `AGENTS.md` as well. This library contains online learning
and bandit problems; oracle optimization remains in `LongTails/`.

## Layout and protocol

- Use UpperCamelCase module names. Match setup namespaces to their module paths;
  related proof modules may share a namespace.
- Put problem assumptions and `spec` in `Setups/`, algorithms in `Algorithms/`,
  supporting proofs in `Proofs/`, public results in `Theorems/`, and protocol and
  audit examples in `Tests/`. Reuse common probability lemmas.
- Import and use `LongTailsOnline.Template`. Protocol lemmas belong next to its
  definitions; application proofs belong in `Proofs/`.
- Execute algorithms through `OnlineTemplate.execute`. The algorithm receives
  only its public parameters, observations, and feedback. Unknown means, future
  rewards, the instance, and hidden outcomes must not enter the algorithm input.
- State the exact order of observation, action, feedback, and update. Specify
  whether the environment is stationary, oblivious, or adaptive, and the precise
  stochastic independence or conditional distribution assumptions.
- Define the regret from the actions in the actual execution trace. Distinguish
  realized regret, pseudo-regret, expectations, averages per round, and
  high-probability statements. Give the measure explicitly in each expectation.
- State the algorithm variant, initialization, tie rule, reward assumptions,
  horizon, and every tuning parameter explicitly. Preserve the requested family.
- Derive concentration, counting, and regret bounds from the sampling model and
  the algorithm; never assume confidence events, concentration bounds, or the
  desired regret guarantee in the setup.
- Keep the setup independent of the candidate algorithm. Never restrict admissible
  environments using properties proved only for that candidate.

## Public results and verification

- Each theorem module exports exactly one `result`, with no additional hypotheses,
  of the form `OnlineTemplate.Guarantee SetupModule.spec method bound` for a named
  algorithm family, or `OnlineTemplate.Achievable SetupModule.spec bound` for an
  existence result. Import the setup module directly.
- Define `method` and an explicit readable `bound` in the result namespace.
  Comparator compares declaration types structurally. Use the exact signatures
  `method : (p : spec.Public) → OnlineTemplate.Algorithm (spec.Observation p)
  (spec.Action p) (spec.Feedback p)` and `bound : (p : spec.Params) → spec.Bound p`;
  keep the binder name `p` in those signatures.
  Include all initialization, noise, confidence, and horizon terms. Model
  instance-dependent gaps as private parameters, not algorithm inputs.
- Do not claim optimality from an upper bound alone. Compare the exact assumptions
  and regret criterion with primary literature before choosing a target.
- No `sorry`, `admit`, or new axioms in library sources. The permitted foundational
  axioms for audited solutions are `propext`, `Classical.choice`, and `Quot.sound`.
- `LongTailsOnline.lean` is a generated import index; do not commit it.
- Run commands from the repository root:
  - `lake exe mk_all --lib LongTailsOnline` regenerates the online import index;
    it may return nonzero when the generated file changes.
  - `lake build LongTailsOnline` checks the online library.
  - `./build.sh` and `./lint.sh` check both libraries after Lean changes.
  - `python3 run_online_comparator.py Ucb.lean` audits a selected online result;
    omit the filename to audit all online results.
  - `python3 -m unittest discover -s tests -p 'test_online_comparator.py'` checks audit rejection
    cases after changes to online audit tooling.
- The Comparator checks the theorem against a challenge imported from the setup,
  and separately audits the algorithm and bound definitions. Keep the agreed setup
  fixed during algorithm research; a locally generated challenge does not attest
  that the setup matches an earlier revision.
- For documentation-only changes, inspect the diff and run `git diff --check`.
