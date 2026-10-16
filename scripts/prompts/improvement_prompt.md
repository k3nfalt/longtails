Investigate the following proposed improvement to an existing optimization result:

Read `scripts/negative_examples.md` and apply its contribution-assessment lessons before selecting or approving a result. Its user-reviewed corrections take precedence over the older positive reviews of those examples.

Read `scripts/positive_examples.md` for user-selected successful attempts and their concrete gains and limitations. Use these alongside the negative examples; preserve the stated regimes and distinguish complexity, scope, oracle, and adaptivity improvements without automatically assigning a verdict or star rating.

Prioritize new oracle-complexity guarantees and independently meaningful problem setups over analyses of artificially fixed methods. Do not restrict the algorithm family merely to make a weaker result appear competitive or manufacture novelty. A method-specific contribution is an occasional exception requiring independent significance; for example, proving that GD can be almost as fast as accelerated gradient descent (AGD) under comparable assumptions, oracle access, and accuracy can be important even without improving the best known problem-class complexity. Quantify the remaining gap, parameter regimes, and tradeoffs, and verify that the result is new relative to the strongest applicable analyses. Popularity alone does not justify choosing a fixed-method analysis, and using `allowedAlgorithm` does not give it priority.

Example: `LongTails/Setups/KnownValueSmoothConvexLocalLinear.lean` previously enforced the exact SplitBrox implementation through `allowedAlgorithm`. We removed this artificial restriction: the setup now specifies the problem and oracle access, while its theorem still constructs SplitBrox and proves the same budget.

Using `allowedAlgorithm` is optional by default. Require it only when the contribution is specifically about a very popular algorithm family, such as gradient descent (GD), stochastic gradient descent (SGD), or Adam. In that case, enforce the claimed update family and output-selection rule, prove compliance, and leave tuning choices to the algorithm and proof. Agents should occasionally use `allowedAlgorithm` for other families when it adds useful precision, but do not require it for every method-specific analysis or introduce a restriction merely to claim novelty.

**Existing setup or theorem:** "Near-Optimal Convergence of Accelerated Gradient Methods under Generalized and $(L_0, L_1)$-Smoothness" and "OPTIMIZING (L0, L1)-SMOOTH FUNCTIONS BY GRADIENT METHODS"

**Proposed improvement:** These two paper provide the current SOTA in different regimes in the accelerated convex optimization. The goal is develop or use the current method and prove a new oracle complexity that at least is not worst than the results of these papers.

Use exactly two agents: a Researcher and an independent Reviewer. Determine whether the proposed improvement is achievable, mathematically correct, and substantively new. Treat my suggestion as a research hypothesis, not as a claim you must confirm.

1. Scope and deliverables

Inspect the repository, its instructions, the existing result, and its proof dependencies before starting. Understand the current assumptions, algorithm, guarantee, and oracle-cost accounting.

All research changes must be inside `LongTails/`, except necessary dependency additions in `lakefile.toml` and `lake-manifest.json`. `LongTails.lean` is generated automatically by build and lint; do not commit it. Never modify `LongTails/Template.lean`. Treat existing core definitions, oracle interfaces, assumptions, verification infrastructure, and existing theorem statements as frozen. Preserve the original result.

Deliver only:
- New setup definitions, if the improvement requires them.
- New algorithm definitions, if needed.
- Supporting proofs and lemmas.
- Exactly one NEW main proved improved theorem under `LongTails/Theorems`, following repository conventions.
- A companion Markdown contribution note beside the new theorem, with the same basename, explaining its improvement, literature comparisons, and limitations.
- Necessary Lean dependency additions.

Reuse existing definitions when appropriate. Do not duplicate a setup or algorithm merely to rename it.

No paper draft or additional standalone research note is required. Keep research notes and review exchanges outside the repository. Summarize the outcome in the final response.

2. Agents and independence

Use separate agents, contexts, Git worktrees, and working branches for the Researcher and Reviewer. Do not spawn additional agents.

The Researcher develops the improvement. The Reviewer independently checks correctness, the comparison with the existing result, novelty, and significance.

The Researcher must not write the Reviewer’s assessment or approve its own work. Only the Reviewer may create the final commit and push to the task's unique `agent/<unique-task-name>` branch.

3. Git workflow

Read and follow section 3 (Git workflow and authentication) of `scripts/prompts/research_prompt.md`. Use separate worktrees based on freshly fetched `origin/main` and deliver the approved improvement on a unique `agent/<unique-task-name>` branch with exactly one research commit. Keep the recorded starting base even if `origin/main` advances; being behind alone does not require rebasing or repeating validation. Never push or merge into `main`.

4. Researcher

First restate the existing guarantee and the requested improvement precisely. Compare:
- Assumptions and admissible problem instances.
- Information available to the algorithm.
- Accuracy criteria.
- Oracle operations and their costs.
- Parameter dependence and applicable parameter regimes.

Identify where the existing proof loses the factor or requires the assumption we want to improve. Investigate whether the obstacle is in the analysis, the algorithm, or the problem itself.

Search current literature and read relevant primary papers. Check whether the proposed improvement is already known or ruled out by a lower bound or counterexample. Do not claim novelty from a routine application of an existing result.

Present a concrete proof strategy and its main unresolved obstacles to the Reviewer before extensive formalization.

If feasible, develop the mathematical proof and formalize it. Handle parameter ranges, randomness, expectations, stopping rules, and oracle-call accounting explicitly.

Do not hide a worse dependence elsewhere, strengthen assumptions silently, change the accuracy criterion, or introduce a stronger oracle while presenting the result as an unconditional improvement.

If the exact target is unattainable, explain why. A partial improvement may be pursued only if it remains directly relevant to my suggestion and has a meaningful, clearly stated advantage. Do not substitute an unrelated easy result.

5. Reviewer

Independently inspect the existing theorem, candidate theorem, proof, and closest literature.

Check:
- Is the new guarantee genuinely stronger in a clearly identified regime?
- Are the assumptions, oracle model, and accuracy criterion compared fairly?
- Are any additional assumptions necessary, explicit, and meaningful?
- Does the algorithm use only permitted information?
- Is the improvement already known or a routine corollary?
- Does the formal statement faithfully encode the claimed improvement?
- Are all proof steps and complexity calculations correct?

Use the repository’s existing verification tools. Check compilation and the main theorem’s assumptions and axiom dependencies. Reject `sorry`, `admit`, unproved custom axioms, altered core definitions, and vacuous guarantees.

Separate mathematical correctness from novelty and significance. Formalizing an existing result is not, by itself, a new optimization result.

For each round, issue REJECT, REVISE, or APPROVE with concrete evidence. Identify blocking issues, cite relevant primary sources, and state uncertainty honestly.

Approval requires a correct, faithfully formalized, substantively novel improvement with a credible research contribution. Explain whether it could support a standalone conference paper or is better viewed as part of a larger contribution.

6. Revision and stopping

The Researcher must address every blocking issue; the Reviewer must reassess independently.

After five full review rounds without approval, stop and report the best result, unresolved obstacles, and recommended next steps. Do not weaken the acceptance criteria to force success.

If the proposed improvement is false, already known, or unsupported, report that outcome. Do not commit or push unapproved work.

7. Acceptance and push

Before committing, the Reviewer must:
- Approve the exact integrated candidate contents.
- Inspect the full diff against the recorded starting base.
- Confirm that all changed paths match the permitted research deliverables above.
- Independently check the companion contribution note against the improved theorem and literature.
- Confirm that `LongTails/Template.lean`, frozen core files, and existing theorem statements are unchanged.
- Verify the improved theorem and its comparison with the original.
- Run the required build, proof, and axiom checks. Audit the new theorem with `python3 run_comparator.py <TheoremName>.lean`; a full-library comparator run is not required for adding a new result.
- Confirm that only the requested deliverables are staged.

Any substantive change after approval requires renewed review and validation.

After acceptance, follow the submission instructions at the end of section 7 of `scripts/prompts/research_prompt.md`. Push the single approved research commit and open one draft PR targeting `main`. Verify that the PR contains the approved commit, report its URL, and stop. Verification and novelty reviews start automatically. Do not dispatch or monitor workflows, append commits, force-push, merge, or automatically retry, repair, replace, or close the PR.

Finish with:
- The original guarantee and the improved guarantee side by side.
- Any differences in assumptions or oracle models.
- The parameter regimes where the improvement matters.
- The central proof idea and comparison with prior work.
- The Reviewer’s verdict and remaining limitations.
- Verification results, changed file paths, and the pushed research commit ID, PR URL, or why submission was blocked or no commit was justified.
