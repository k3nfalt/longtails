Run this task as a persistent Codex goal.

Read `scripts/negative_examples.md` and apply its contribution-assessment lessons before selecting or approving a result. Its user-reviewed corrections take precedence over the older positive reviews of those examples.

Read `scripts/positive_examples.md` for user-selected successful attempts and their concrete gains and limitations. Use these alongside the negative examples; preserve the stated regimes and distinguish complexity, scope, oracle, and adaptivity improvements without automatically assigning a verdict or star rating.

Prioritize new oracle-complexity guarantees and independently meaningful problem setups over analyses of artificially fixed methods. Do not restrict the algorithm family merely to make a weaker result appear competitive or manufacture novelty. A method-specific contribution is an occasional exception requiring independent significance; for example, proving that GD can be almost as fast as accelerated gradient descent (AGD) under comparable assumptions, oracle access, and accuracy can be important even without improving the best known problem-class complexity. Quantify the remaining gap, parameter regimes, and tradeoffs, and verify that the result is new relative to the strongest applicable analyses. Popularity alone does not justify choosing a fixed-method analysis, and using `allowedAlgorithm` does not give it priority.

Example: `LongTails/Setups/KnownValueSmoothConvexLocalLinear.lean` previously enforced the exact SplitBrox implementation through `allowedAlgorithm`. We removed this artificial restriction: the setup now specifies the problem and oracle access, while its theorem still constructs SplitBrox and proves the same budget.

Using `allowedAlgorithm` is optional by default. Require it only when the contribution is specifically about a very popular algorithm family, such as gradient descent (GD), stochastic gradient descent (SGD), or Adam. In that case, enforce the claimed update family and output-selection rule, prove compliance, and leave tuning choices to the algorithm and proof. Agents should occasionally use `allowedAlgorithm` for other families when it adds useful precision, but do not require it for every method-specific analysis or introduce a restriction merely to claim novelty.

Produce a genuinely new optimization result whose novelty, significance, and technical depth justify acceptance as a theory paper at ICML, ICLR, or NeurIPS. Use exactly two agents: a Researcher and an independent Reviewer. Both agents MUST work toward producing such a result; a plausible research direction, a routine extension, or a formalization of a known theorem does not satisfy the task.

The required outcome is a naturally motivated problem setup, an algorithm, and a rigorously proved convergence or oracle-complexity guarantee, formalized using this repository’s existing framework. The mathematical contribution MUST be substantively novel relative to the literature, not merely new to this repository. A new setup is not itself a contribution unless it captures a meaningful problem and leads to a substantive new result. A recognized existing problem with a genuinely new guarantee is preferable to an artificial new problem designed to make a theorem easy.

Strongly prioritize common, established assumptions already used in primary research papers. Prefer a new result under a standard setup over a result requiring a newly invented restriction. Among candidates with comparable significance, prefer fewer and weaker assumptions and broader applicability. Assess the actual mathematical restrictions, not the number of named assumptions; bundling restrictions does not make a setup more general. Removing or weakening an established assumption can itself be a substantive contribution.

Start from unresolved extensions of known methods and theorems. Prefer results for general nonlinear objectives in arbitrary finite dimension within a recognized convex, nonconvex, composite, constrained, or minimax class. Scalar and quadratic calculations are diagnostics, not substitutes for the intended general theorem. A specialized target needs independent significance and explicit review; inability to finish a general proof does not justify silently narrowing the problem.

Both agents must independently investigate current optimization results from ICML, ICLR, NeurIPS, and arXiv before choosing a candidate. Use the current UTC date, initially survey the two most recent publicly available editions of each conference and roughly the last two years of arXiv submissions and revisions, and follow citations to foundational or stronger older results. Read primary theorem statements, assumptions, relevant proof steps, and limitations. Verify conference status through official proceedings or OpenReview; distinguish submissions and unreviewed preprints from accepted papers. Check the latest arXiv versions, follow-up work, corrections, and counterexamples. Record search coverage, key paper versions, and inaccessible sources. Choose the strongest applicable baseline regardless of publication date.

The files in `scripts/proposals` are previous artifacts, not the research agenda or evidence that a question is open. Consult relevant files only as optional historical context after the literature survey. A proposal explicitly supplied by the user may guide the topic, but both agents must reassess it against current primary sources. Neither matching nor differing from an old proposal is a selection criterion by itself.

Treat acceptance-quality research as a completion requirement, not an aspiration. Actual conference acceptance cannot be guaranteed by either agent. The Reviewer must independently support an acceptance recommendation with evidence; the requirement to produce a result never authorizes invented novelty, concealed limitations, or forced approval.

Two research routes are explicitly allowed:
- Remove, relax, or replace an established assumption, or add a naturally motivated structural assumption, and establish a substantive new guarantee. Anchor the change in a known theorem and explain which instances become covered or excluded, why that matters, and where its proof stops applying. A stronger assumption must yield a new result relative to existing work under that stronger assumption. A naturally motivated new setup is also allowed when its connection to an established optimization question is explicit.
- Take an established setup from the literature and obtain a NEW STATE-OF-THE-ART convergence or oracle-complexity guarantee. The setup need not be novel; the result MUST be. Demonstrate a meaningful improvement over the strongest applicable known guarantees under comparable assumptions, oracle access, accuracy criteria, and cost accounting. State the precise parameter regimes of improvement and any tradeoffs; do not claim universal superiority from a restricted-regime improvement.

Both routes require repository deliverables. In particular, choosing a setup from the literature does not excuse leaving it outside the repository: add its faithful Lean specification, the new theorem, and the complete supporting proofs.

1. Scope and deliverables

Inspect the repository, its instructions, existing setups, proofs, and verification tools before starting.

All committed changes must be inside `LongTails/`, except necessary dependency additions in `lakefile.toml` and `lake-manifest.json`. `LongTails.lean` is generated automatically by build and lint; do not commit it. Never modify `LongTails/Template.lean`. Treat existing core definitions, oracle interfaces, assumptions, and verification infrastructure as frozen. Do not weaken existing statements or modify the framework to make a proof pass.

You may install reasonable Python libraries, system packages, and Lean libraries when needed for research, experiments, or formalization. Reuse existing libraries and tools when they suffice. Prefer a virtual environment for Python libraries and the system package manager for system packages. Keep temporary tooling outside the repository; for Lean dependencies needed by the deliverables, update `lakefile.toml` and regenerate `lake-manifest.json` with Lake, preserving existing pinned versions and the Lean toolchain. The Reviewer must review dependency additions and verify the final result with them.

Deliver only:
- The chosen setup as a Lean specification under `LongTails/Setups`, including when it is an established setup from the literature. If an exactly equivalent specification already exists in the repository, reuse it explicitly rather than adding a duplicate; otherwise, adding the setup is mandatory.
- Algorithm definitions.
- Complete supporting Lean proofs and lemmas for the new result, following the existing proof-module layout.
- Exactly one NEW main proved convergence or oracle-complexity theorem under `LongTails/Theorems`, connected to the chosen setup and actual algorithm execution. Preserve existing theorems; do not replace a prior result with the new one.
- A companion Markdown contribution note beside that theorem, with the same basename: `LongTails/Theorems/<TheoremName>.md` for `<TheoremName>.lean`. Include it in the same reviewed final commit and push to the task's `agent/<unique-task-name>` branch as the Lean deliverables.
- Necessary Lean dependency additions in `lakefile.toml` and `lake-manifest.json`.

Prefer new files. Supporting lemmas are allowed; “one theorem” means one main research result.

The companion contribution note is required; no LaTeX draft, additional standalone research note, or committed review report is required. Keep working research notes and review exchanges outside the repository and summarize the findings in the final response.

2. Agents and independence

Keep the Researcher and Reviewer as separate agents with separate contexts and worktrees. Do not spawn additional agents.

The root agent is the Researcher and owns the goal; spawn exactly one independent Reviewer. Reuse that Reviewer across revisions and pivots. A Reviewer verdict completes a review round, not the root research task.

The Researcher proposes and develops the result. The Reviewer independently assesses correctness, novelty, significance, and faithful formalization. Start the Reviewer in a fresh context with the full task and any user or proposal guidance, without inheriting the Researcher's candidate rankings or conclusions. Before reading the Researcher's preferred candidate and ranking, the Reviewer independently surveys current ICML, ICLR, NeurIPS, and arXiv results for meaningful assumption gaps. Keep this independent search distinct from reviewing the eventual candidate; reuse the same Reviewer.

The Researcher must not write the Reviewer’s assessment or approve its own work. Only the Reviewer may create the final commit and push to the task's `agent/<unique-task-name>` branch.

3. Git workflow and authentication

Inspect `./infra/generate_token.py` and authenticate every GitHub operation, including fetches, with `python3 infra/generate_token.py <command> [arguments...]`. Do not use personal credentials or alter repository protections.

Fetch the latest remote state before starting. Base both agents’ working branches on the freshly fetched `origin/main`. Deliver each task on a unique `agent/<unique-task-name>` branch; do not combine tasks on a shared integration branch.

Create a separate Git worktree and unique working branch for each agent. Use unique paths and branch names so other Codex sessions can work concurrently. Do not overwrite existing work, reuse another session’s worktree, or change its branches.

All research edits and reviewer validation must happen in these worktrees. Never modify or push the `main` branch.

Reuse existing Lean build artifacts when initializing each worktree to avoid rebuilding unchanged dependencies and modules. Run the required verification on the final integrated result.

Do not create intermediate commits. Transfer proposed changes between worktrees using patches or explicit file copies that include new files. Record the base revision and identify the exact candidate contents being reviewed.

In the Reviewer’s worktree, apply the proposed changes to the recorded starting base. Inspect and validate the complete resulting diff. A PR may use this base even if `origin/main` has advanced.

Create exactly one final commit containing the approved deliverables. Push only to the task's unique `agent/<unique-task-name>` branch, without force-pushing.

Do not rebase, merge newer `main` commits, or restart validation merely because `origin/main` advances. Keep the recorded starting base through submission and postprocessing. Never rewrite the submitted branch or replace a submitted PR automatically. Preserve other sessions’ changes.

4. Researcher

Before extensive proof work, propose three candidate extensions of specific primary results identified by the current literature survey. Compare their motivation, closest prior work, potential novelty, generality, and feasibility. For each candidate, give a baseline-versus-target comparison: the exact theorem and paper version; every removed, relaxed, added, or replaced assumption; the relation between the instance classes; algorithm, oracle, output, and cost changes; the proof step affected; and the proposed technical idea. Prefer one primary assumption change with a substantive consequence over an arbitrary conjunction of restrictions. Explain how current literature supports the question and what remains uncertain; use earlier local proposals only for relevant historical context. Select the strongest candidate after the Reviewer's initial critique. If none clears the novelty and naturalness requirements, propose new candidates rather than implementing the easiest rejected one.

Complete the obvious standard-reduction check before selecting a candidate. Derive what batching, clipping, regularization, or composition with existing results already achieves under the target assumptions and count its actual cost. Record the remaining gap or the exact condition blocking that reduction. An unchecked possibility that the target is a standard corollary is an unresolved novelty issue, not a positive research assessment. Give a meaningful nonlinear family with interacting coordinates satisfying the assumptions, make dimension dependence explicit, and identify the technical obstruction not visible in scalar or quadratic examples. If the candidate comes from a supplied proposal, recheck these points even if its recorded verdict is PROMISING.

Convert each surviving candidate into a concrete proof task. State the critical lemma with explicit hypotheses, derive it, and test its boundary cases before expanding the argument. Where relevant, check one-dimensional and quadratic instances, zero-noise limits, initialization, and adversarial oracle sequences. Numerical experiments may disprove a conjecture or guide a proof, but never replace one. If the lemma fails, reproduce the counterexample and either change the mechanism for a mathematically justified reason or reject the candidate. Do not repeatedly retain the same failed mechanism under renamed assumptions.

Search current literature and read the relevant primary papers. Compare against the strongest applicable results, including reductions to known settings. Do not manufacture novelty through renamed parameters, artificial assumptions, or cosmetic variants.

The setup MUST have motivation independent of the proposed proof. Explain what real optimization setting or established theoretical question it captures, give a concrete nontrivial family of instances, and justify every unusual assumption. Reject assumptions tailored to the desired conclusion, hidden convergence hypotheses, contrived parameter regimes, or arbitrary combinations of restrictions introduced only to evade prior results. A special case is acceptable only when it is independently important and the new guarantee is substantial.

For each candidate, identify the provenance of every substantive assumption: cite the primary paper and exact definition or theorem using it, or explicitly mark it as new. Check the precise quantifiers, parameter dependencies, and oracle model; a similar name or citation does not justify a stronger restriction. Prefer assumptions widely used in the relevant literature over isolated specialized assumptions. Prior publication is evidence of motivation, not automatic justification for combining restrictions from unrelated settings.

Minimize assumptions before committing to a candidate and again after completing its proof. Try to remove or weaken each added restriction, and distinguish what the proof currently needs from what the problem intrinsically requires. A new or unusually strong assumption needs a concrete, independently motivated problem or oracle mechanism that implies it, with explicit parameter dependence. A hand-crafted example only proves nonemptiness; it does not establish usefulness. For example, bounded cumulative oracle errors must be derived from a meaningful mechanism rather than justified solely by an alternating-error example. If an assumption is introduced to repair a failed proof, repeat the naturalness and literature comparison before proceeding. Do not present a faster rate obtained by imposing stronger assumptions as an improvement for the original broader class.

Write a precise novelty comparison against the closest primary results: their hypotheses, oracle access, accuracy criterion, rate, and applicable parameter regimes versus yours. Check whether your claim follows by substitution, rescaling, a standard reduction, or composition of known theorems. Identify the new mathematical mechanism and the proof step that requires it. A missing search result, a new name, a constant-factor change without independent significance, or the Lean formalization alone is not sufficient evidence of a new optimization contribution.

For the chosen direction, specify:
- The objective class and assumptions.
- The oracle model and information available to the algorithm.
- The algorithm and its permitted parameter dependencies.
- The exact accuracy criterion and convergence or oracle-complexity bound.
- Parameter regimes where the result meaningfully improves on or extends prior work.
- Nontrivial examples satisfying the assumptions.

Develop a complete mathematical proof and formalize it in the repository. Explicitly handle randomness, expectations, stopping rules, parameter ranges, and oracle-call accounting where relevant.

Simplify the public oracle-call budget before final review. In `LongTails/Theorems/`, write each public `budget` definition as one explicit, human-readable line in the setup parameters, without local tuning variables or opaque helpers. Simplify nested fractions, products, repeated expressions, and rounding where possible. Prefer one readable formula over multiple tuning cases when it preserves the rate. A universal constant-factor increase is acceptable only when it preserves the parameter rates and the claimed improvement over prior work. Prove that the simplified budget suffices for the actual algorithm execution, counting every oracle call and retaining necessary noise, initialization, and other required terms. Keep supporting algebra in proof modules. Simplify the Lean definition itself, not merely its website or LaTeX presentation.

After the initial novelty and naturalness screening, formalize established supporting lemmas incrementally in the Researcher’s worktree and compile the affected modules. Do not postpone all Lean work until the final review, and do not create empty scaffolding merely to show changed files. Keep speculative calculations and rejected candidate notes outside the repository. Progress must consist of a proved lemma, a checked counterexample, a concrete literature comparison, a compiled proof step, or a resolved review issue—not repeated statements that a difficult argument remains to be found.

Ensure that the formal statement matches the intended claim and that the algorithm does not use unavailable information.

Make the Lean setup consistent with the claimed contribution. Formally capture every condition essential to its meaning or novelty, including the problem class, assumptions, admissible algorithms, available information, output, accuracy criterion, and cost model. Connect the algorithm and main theorem to that specification and prove the required compliance; neither prose nor implementation details alone establish that the setup expresses the claimed result. For example, a contribution about GD step sizes requires the setup to capture the GD update and permitted step-size choices. Check this alignment before proof development and again against the final contribution note.

Write the companion contribution note for a reader who has not seen the research conversation. Explain the setup and assumptions, algorithm and returned output, proved guarantee and oracle cost, precise new contribution and technical mechanism, and what is already known. Compare with the closest primary papers using links and specific theorem or section references; state the improvement regimes, assumption differences, limitations, and unresolved literature comparisons honestly. Link to the local Lean theorem, setup, and algorithm. Incorporate the final clarifications about the contribution from the review and any user feedback, keeping the note consistent with the final integrated theorem. Do not substitute a conversation transcript or an unsupported novelty claim for this explanation.

Respond to every blocking review issue with a concrete correction or evidence-based rebuttal.

5. Reviewer

Act as a demanding conference reviewer, not as a collaborator whose objective is eventual approval.

Independently search the literature and examine the closest results. Check whether the proposed result follows from an existing theorem, standard reduction, or routine argument. Explain the substantive contribution and any remaining uncertainty about novelty.

Independently audit the assumptions at candidate selection and final review; do not merely accept the Researcher's justification. Strongly favor common assumptions from prior papers and fewer, weaker restrictions. Verify the cited formulations yourself, identify every added restriction relative to the closest established setup, and challenge whether it can be removed or weakened. For each unusual assumption, require an independently meaningful application or oracle mechanism and check that it actually implies the assumption. Include an explicit assessment of assumption reasonableness and necessity in every review verdict. Unjustified restrictions are blocking issues even when the proof is correct; request a revision or reject the candidate rather than approving a contrived setup.

Independently check the baseline-versus-target assumption comparison, the claimed general nonlinear scope, and the completed reduction calculation before endorsing a candidate. For assumption removal, test a meaningful family excluded by the baseline; for a natural addition, check that it does not reduce the question to an existing structured theorem. Distinguish an explicitly published open question, a gap inferred from theorem scopes, and an incomplete literature search, and check subsequent work before treating any of them as unresolved. Reassess any historical proposal verdict against current primary sources; prior inclusion in the folder is neither approval nor a reason to reject the question. A proof only for quadratics, separable objectives, fixed dimension, or a special spectral model cannot approve a promised general optimization result.

Actively try to invalidate the novelty claim before approving it. Independently reconstruct the strongest applicable prior guarantee and test the claimed improvement on equivalent assumptions and oracle costs. Reject an artificial setup even if its theorem is correct. Reject a technically correct but routine or insignificant result. Assess the mathematical contribution as if its Lean formalization were absent; formal verification supports correctness but does not replace research significance.

Check:
- Mathematical correctness and completeness.
- Whether the setup is motivated, nonempty, and nontrivial.
- Whether common literature assumptions were prioritized, their cited formulations faithfully matched, and every new or stronger restriction independently justified. Challenge removable assumptions and reject proof-driven restrictions supported only by contrived examples.
- Whether assumptions hide the solution or grant unavailable information.
- Whether comparisons use equivalent assumptions, accuracy criteria, and cost models.
- For an established literature setup, whether the claimed new state of the art survives comparison with the strongest applicable known results, and whether the repository specification faithfully matches that setup.
- Whether the contribution has sufficient significance and depth for the target venues.
- Whether the Lean theorem faithfully represents the stated mathematical guarantee.
- Whether the formal setup and claimed contribution agree on every essential condition and whether the algorithm and main theorem establish the result under that specification. Independently trace the problem class, assumptions, admissible algorithms, available information, output, accuracy criterion, and cost model across the setup, algorithm, theorem, and contribution note. Treat missing restrictions, hidden strengthenings, or other mismatches as blocking even when the proof compiles; prose or suggestive definition names are insufficient.
- Whether proofs compile and use only permitted axioms, with no `sorry`, `admit`, unproved custom axioms, or weakened core definitions.

Inspect the assumptions and dependencies of the main theorem, not just its proof body. Use the repository’s existing independent verification tools where available. A successful Lean build alone establishes neither novelty nor faithful formalization.

For each round, produce an independent verdict: REJECT, REVISE, or APPROVE. Distinguish blocking issues from optional suggestions. Cite relevant primary sources and identify the exact disputed claims.

An APPROVE verdict must explain why you would recommend acceptance at a named target venue based on the theoretical contribution, identify the strongest likely rejection argument, and explain why the evidence overcomes it. State the precise new result and technical insight. Do not approve merely because the Researcher has spent substantial effort, the proof compiles, or the task requires a successful outcome.

If literature access is unavailable or critical prior work cannot be checked, explicitly report that limitation. Do not claim verified novelty without adequate evidence.

6. Revision and stopping

The Researcher revises; the Reviewer reassesses independently.

REJECT applies to the current candidate. It is an instruction to repair the specific defect or select another candidate, not permission to terminate the research goal. A clean worktree, several failed candidates, an unproved nonlinear stability argument, a rate already implied by prior work, or the absence of a theorem so far are not external blockers. A report listing these facts belongs in a progress update, followed by further work.

Maintain a concise research checkpoint outside the repository containing the goal objective, agent and worktree identifiers, base revision, candidate history, exact rejection reasons and evidence, proved lemmas, current proof obligation, and next concrete action. Update it after each review or pivot. After context compaction or continuation, read the checkpoint; resume from the unresolved step rather than repeating rejected proposals or issuing an incomplete final report. Revisit a rejected candidate only with new evidence or a substantive new mechanism addressing its recorded defect.

Do not weaken acceptance criteria to obtain approval. Continue revising, searching, and pivoting until an acceptance-quality result is independently approved and verified. After five full review rounds on a candidate without approval, abandon that candidate and start a fresh candidate-selection round; this is a pivot threshold, not successful completion or a reason to stop the entire task. Pivot sooner when a fundamental novelty or naturalness objection cannot be resolved. Do not commit or push unapproved work.

Respect explicit user stop or pause instructions and actual runtime limits. Do not invent an execution limit from elapsed effort, a review-round count, or mathematical difficulty. For a genuine external blocker, identify the failed operation and evidence, try permitted alternatives, and continue unaffected work. If work must stop, preserve the checkpoint and report the precise stopping condition honestly. Never claim success or manufacture approval to avoid reporting an incomplete task.

Do not declare completion after literature screening, candidate selection, a Reviewer response, or an ordinary end-of-turn summary. Keep pursuing it across turns. Completion requires every acceptance condition below, including the actual Lean deliverables, independent approval of the final integrated contents, successful local verification, and creation of the research PR.

7. Acceptance and final commit

Approve only when correctness, faithful formalization, substantive novelty, natural motivation, and an evidence-based acceptance recommendation are all supported. Each is a separate mandatory condition.

Before committing, the Reviewer must:
- Approve the exact candidate contents.
- Confirm that the final theorem preserves the independently reviewed novelty claim and meaningful improvement over the closest prior work.
- Confirm that the setup remains naturally motivated and that no artificial assumptions were introduced during proof completion.
- Confirm that the final assumptions were checked for unnecessary restrictions, that their literature provenance or independent justification is explicit, and that the claimed improvement accounts for every strengthening relative to prior work.
- Confirm that the final theorem preserves the reviewed objective class and assumption change, includes the intended nonlinear instances, and resolves the identified gap beyond the checked standard reduction. Reassess significance if proof development narrowed the scope.
- Inspect the full diff against the recorded starting base.
- Confirm that every changed path is inside `LongTails/`, except reviewed, necessary dependency additions in `lakefile.toml` and `lake-manifest.json`.
- Confirm that `LongTails/Template.lean` and all other frozen core files are unchanged.
- Confirm that the deliverables contain exactly one main research theorem under `LongTails/Theorems`.
- Confirm that the chosen setup is present under `LongTails/Setups` and that the new theorem and complete supporting proofs are included, regardless of which research route was selected.
- Independently review the companion `<TheoremName>.md` for accuracy of its contribution claims, literature comparisons, and limitations; confirm it reflects the final clarifications and integrated Lean result and is included in the same commit to be pushed to the task branch.
- Check that the public budget satisfies the simplification requirement and that its proof preserves all required terms, actual oracle-call accounting, parameter rates, and the claimed improvement over prior work.
- Run `./build.sh`, `./lint.sh`, and `python3 run_comparator.py <TheoremName>.lean` on the final integrated result. All three must pass before committing and submitting the PR; a full-library comparator run is not required for adding a new result.
- Confirm that only the requested deliverables are staged.

Any substantive change after approval, including conflict resolution, requires renewed review and validation.

The Reviewer then creates the single final research commit, verifies that it matches the approved contents, and pushes it to the task's unique `agent/<unique-task-name>` branch. This task explicitly authorizes that push and opening one ready-for-review PR targeting `main` once all acceptance criteria pass. It never authorizes pushing or merging into `main`.

Before submission, confirm `git rev-list --count origin/main..HEAD` is exactly 1. Use `python3 infra/generate_token.py` for each GitHub operation. Create one ready-for-review PR with `gh pr create --base main --head <task-branch> --title <title> --body-file <file>`. Include the theorem, setup, contribution note, and verification evidence in the PR body. Write multiline PR text to a temporary file. Verify that the PR exists, is not a draft, and contains the approved research commit, clean up the task worktrees as described below, report its URL, and stop. Do not dispatch or monitor workflows, append commits, force-push, or automatically retry, repair, replace, or close the PR.

PR creation automatically starts verification and novelty reviews. Postprocessing adds a second commit containing only `scripts/reviews/<TheoremName>.md` for each new theorem. Negative novelty reviews do not block this stage. Tables, references, metadata, and website generation remain separate manual steps. Failed PRs remain open for the user to inspect.

After verifying the submitted PR, stop all processes using the task worktrees and remove both agents’ worktrees with `git worktree remove`, running from outside those directories. The Researcher coordinates cleanup before the final response. Remove only worktrees created for this task; keep branches and the submitted PR. Use `--force` only after confirming that remaining files are already preserved in the pushed commit or are disposable task-generated artifacts. If any work is unpreserved, submission failed, or the task is paused, keep the affected worktree and report its path and reason.

Finish with:
- The setup, main theorem, and convergence or complexity rate.
- The closest prior results and the specific novelty claim.
- The Reviewer’s verdict and remaining limitations.
- Verification results and changed file paths.
- The pushed research commit ID and PR URL, or an explicit explanation of why submission was blocked.
