Produce a list of exactly five distinct optimization research directions by finding unresolved questions within established optimization methods and problem classes. Prioritize meaningful changes to known assumptions and guarantees for general optimization problems. Novelty must come from the mathematical question and its consequences, not from inventing an unusual setup. This is a proposal task only: stop after writing the independently reviewed proposals and pushing their single commit to `main-bot`. Do not implement algorithms, prove complete results, formalize Lean theorems, or run the full research workflow.

Read `scripts/negative_examples.md` and apply its contribution-assessment lessons before selecting or approving a result. Its user-reviewed corrections take precedence over the older positive reviews of those examples.

Read `scripts/positive_examples.md` for user-selected successful attempts and their concrete gains and limitations. Use these alongside the negative examples; preserve the stated regimes and distinguish complexity, scope, oracle, and adaptivity improvements without automatically assigning a verdict or star rating.

Prioritize new oracle-complexity guarantees and independently meaningful problem setups over analyses of artificially fixed methods. Do not restrict the algorithm family merely to make a weaker result appear competitive or manufacture novelty. A method-specific contribution is an occasional exception requiring independent significance; for example, proving that GD can be almost as fast as accelerated gradient descent (AGD) under comparable assumptions, oracle access, and accuracy can be important even without improving the best known problem-class complexity. Quantify the remaining gap, parameter regimes, and tradeoffs, and verify that the result is new relative to the strongest applicable analyses. Popularity alone does not justify choosing a fixed-method analysis, and using `allowedAlgorithm` does not give it priority.

Example: `LongTails/Setups/KnownValueSmoothConvexLocalLinear.lean` previously enforced the exact SplitBrox implementation through `allowedAlgorithm`. We removed this artificial restriction: the setup now specifies the problem and oracle access, while its theorem still constructs SplitBrox and proves the same budget.

Using `allowedAlgorithm` is optional by default. Require it only when the proposed contribution is specifically about a very popular algorithm family, such as gradient descent (GD), stochastic gradient descent (SGD), or Adam. In that case, specify how it will enforce the claimed update family and output-selection rule, with compliance to be proved during implementation and tuning choices left to the algorithm and proof. Occasionally propose using it for other families when it adds useful precision, but do not require it for every method-specific proposal or introduce a restriction merely to claim novelty.

Use exactly two agents: the root agent is the Researcher and spawns one independent Reviewer. Reuse that Reviewer throughout; do not spawn additional agents. The Researcher develops the proposals; the Reviewer independently checks their motivation, assumptions, literature comparisons, and feasibility. The Researcher must not invent the Reviewer’s assessment.

Read the repository instructions first. Develop candidates from the current primary literature as described below, then inspect existing setups, theorems, and companion contribution notes for implementation context and overlap. The five directions must address materially different research questions, not cosmetic variants or parameter regimes of the same proposed theorem.

Files in `scripts/proposals` are historical artifacts. Consult relevant ones only after forming candidates from the literature; there is no requirement to investigate the entire folder, extend its topics, or find directions absent from it. Prior claims and Reviewer verdicts are unverified research notes. Recheck any relevant objection against primary sources, and briefly acknowledge a related earlier proposal when useful. Overlap with an old proposal neither establishes nor defeats the value of a currently supported research question.

Current literature discovery

Both agents must independently investigate current optimization results from ICML, ICLR, NeurIPS, and arXiv. Use the current UTC date, the latest publicly available conference editions, and recent arXiv submissions and revisions. Start with the two most recent available editions of each conference and roughly the last two years of arXiv work, then follow citations back to foundational or stronger older results. Broaden this window when needed; recency alone is not evidence of strength or relevance.

Use official proceedings, accepted-paper pages, and OpenReview records to establish conference status, and arXiv records to identify preprint dates and versions. Read the actual theorem statements, assumptions, proofs of the relevant steps, limitations, and open-question sections of the closest papers; abstracts and search snippets are only discovery aids. Check the latest version, subsequent papers, corrections, and counterexamples before treating a gap as open. Distinguish accepted conference papers from submissions and unreviewed preprints. Record the search date, conference editions covered, and arXiv versions of the key baselines; disclose inaccessible or unsearched sources rather than claiming comprehensive coverage.

Build a working map of what these papers establish, which assumptions their analyses need, and what remains unresolved. Select directions from this map. A recent result may motivate a question while an older theorem remains its strongest baseline. Every final proposal must cite its primary anchor theorem and explain what the current literature check establishes about the proposed gap.

Researcher: search from known results

Before choosing the final five, build a short working comparison of candidate extensions anchored in specific primary theorems. Start from the problem and method people already study, list the theorem's substantive assumptions, and locate where its proof uses them. For each candidate, investigate one primary change:

- Remove or relax a restriction, such as quadratic structure, interpolation, samplewise regularity, bounded gradients, uniform noise bounds, independence, interior solutions, or knowledge of a tuning parameter.
- Add a natural, independently motivated structural assumption to a general objective class and ask what stronger guarantee it enables. Compare against the strongest results already exploiting that structure; disclose the smaller instance class and any cost of obtaining its parameters.
- Replace an assumption with a different meaningful condition, or determine a quantitative threshold between regimes. State whether the old and new instance classes are nested or incomparable.

These are search axes, not assertions that any listed extension is open. For each candidate, record the baseline theorem, the exact old and new hypotheses, the proof step affected, the target consequence, and evidence that existing results leave it unresolved. Do not combine several noise, geometry, communication, or oracle restrictions merely to create an uncovered intersection. Multiple changes need a single motivating problem and an explanation of why they belong together.

General optimization scope

- At least four of the five directions must target general nonlinear objectives in arbitrary finite dimension within a recognized class: for example convex, strongly convex, nonconvex, composite or constrained minimization, or minimax/monotone problems. “General” means a guarantee uniform over the stated class, not a single chosen loss or every conceivable objective without assumptions. Make dimension dependence explicit.
- Scalar problems, quadratics, commuting Hessians, separable objectives, or prescribed spectra can be diagnostic examples. They do not establish that a target covers general nonlinear optimization. A specialized final direction is acceptable only with independent significance and an explicit account of what prevents the general extension; do not fill the list with easier special cases.
- Give a meaningful nonlinear instance family with interacting coordinates and explain why it satisfies the proposed assumptions. Identify the obstruction absent from scalar or quadratic models, such as changing curvature or coupling between coordinates. Do not promise a general extension after proposing only a special-case theorem.
- Unless user guidance narrows the scope, consider several established problem and algorithm families. Prefer substantial extensions of familiar methods over a portfolio consisting entirely of the same noise-model substitution. Preserve the named algorithm family whenever the contribution concerns that family.

Research standards

- Strongly prioritize established problems and common assumptions already used in primary papers. Prefer fewer and weaker restrictions and broader applicability. Removing an established assumption can be a valuable contribution.
- Search current literature and read the closest primary papers. Cite exact theorem or section references and links. Distinguish novelty relative to the literature from novelty relative to this repository.
- Seek substantive improvements with potential significance for ICML, ICLR, or NeurIPS. Do not promise conference acceptance or describe a conjectured result as proved or verified SOTA.
- Give every direction motivation independent of a convenient proof. New or unusually strong assumptions require a meaningful application or oracle mechanism; hand-crafted examples alone do not justify them. Identify the literature provenance of assumptions and explicitly mark new restrictions.
- Compare the strongest applicable known guarantee with the proposed target under precise assumptions, oracle access, output criteria, and oracle-call accounting. Include relevant simple baselines and standard reductions. Do not claim improvement merely by strengthening assumptions, renaming parameters, or hiding costs.
- Perform the obvious standard-reduction check before selection: work out whether batching, clipping, regularization, a change of variables, or composition with an existing convergence theorem already gives the target, counting all costs. Record the resulting bound or the exact hypothesis/lemma that prevents the reduction. Merely listing this check as future work is insufficient for a PROMISING verdict.
- Describe a plausible technical idea and the specific obstacle it must overcome. No complete proof is required. State uncertainty and missing evidence honestly, including inaccessible literature.
- Distinguish an explicitly stated open question in a primary paper from a gap inferred by comparing theorem scopes and from an unresolved literature search. Search for follow-up work and negative results. Neither an old open-problem statement nor failure to find a paper establishes that the question remains open.

Independent review

Start the Reviewer in a fresh context with the full task, user guidance, and repository path, without inheriting the Researcher's candidate rankings or conclusions. Before seeing the Researcher's ranking, the Reviewer independently surveys current ICML, ICLR, NeurIPS, and arXiv results and identifies promising assumption gaps. Then the Reviewer examines every shortlisted direction and its closest results, verifies assumption provenance and the baseline-to-target change, and tries to invalidate novelty through a standard reduction or counterexample. The Reviewer must not merely repeat the Researcher's search or reserve all substantive checks for future work.

For each direction, provide a verdict of PROMISING, NEEDS REFINEMENT, or NOT RECOMMENDED, with reasons, the strongest objection, and the first remaining check. Explicitly assess: whether the changed assumption matters; whether the target covers the stated general problem class; whether a natural addition really buys a new guarantee; and whether the reduction check leaves a specific unresolved obstacle. Use NEEDS REFINEMENT when a decisive novelty or generality check remains undone. These verdicts assess research potential, not theorem correctness or conference acceptance.

Revise or replace clearly duplicated, artificial, or already settled proposals in response to review. Preserve unresolved objections and uncertainty in the final document; do not force positive verdicts to fill the list. Have the Reviewer assess the final five proposals before saving the result.

The Reviewer must check that the new five questions are distinct and that their claimed gaps survive the current literature search. Relevant historical proposals may provide leads or objections to recheck, but their topics and verdicts must not control selection. A copied proposal without renewed primary-source investigation is insufficient; a question independently justified by current literature may be retained even if it appeared in the folder before.

Required output

Create exactly one new Markdown file at `scripts/proposals/YYYY-MM-DD-HHMMSS.md`, using the current UTC timestamp. Create the directory if needed and choose a unique suffix if the filename already exists. Do not overwrite earlier proposals. This file is the only repository deliverable; do not modify other files.

Write a self-contained document with a short ranked overview followed by exactly five numbered directions. For each direction include:

1. Research question and independent motivation, with a concrete meaningful instance family.
2. Precise setup, assumptions and their provenance, oracle model, and algorithm family if applicable. Include a compact baseline-versus-proposal comparison identifying every removed, weakened, added, replaced, or unchanged substantive assumption, the relation between the instance classes, and any changed information or costs.
3. Primary anchor and closest results with exact theorem references, publication status and versions, their guarantees, and evidence and uncertainty about the unresolved gap after checking current work. State overlap with existing repository results; mention related historical proposals only when relevant.
4. Proposed new result or conjectured rate, accuracy/output criterion, improvement regimes, and tradeoffs. State what is gained and what is lost if assumptions change; identify the nonlinear, arbitrary-dimensional scope or justify the specialized exception.
5. Candidate technical mechanism, the specific baseline proof step that breaks, the completed reduction check and its outcome, and the first remaining concrete proof task or falsification check. That task must address the new obstacle, not just reproduce a known proof on a scalar example.
6. Independent Reviewer verdict, assumption and generality assessment, objections, and remaining uncertainty.

Clearly separate established facts from conjectures. Rank directions by significance of the assumption change, breadth of the objective class, evidence for an unresolved gap and technical mechanism, and feasibility. Topic distance from the archive and ease of Lean formalization are not ranking advantages. Include a short literature-search coverage note with the date, conference editions, and arXiv search window, plus primary-source links and relevant local file links. Keep the document focused on the five directions rather than the agents' conversation or rejected candidate history.

Git workflow and completion

Inspect `scripts/generate_token.py` and use its supported authentication wrapper for every GitHub operation, including fetches and verification. Fetch before starting and work in a new, uniquely named worktree and branch based on the latest `origin/main-bot`. If it does not exist, use the latest `origin/main` as the base and create remote `main-bot` when pushing. Preserve other sessions’ work; do not modify the user's checkout or update `main`.

After writing the file, check that it contains exactly five distinct reviewed directions, each anchored in a primary result with a current literature check, an explicit change, and a reduction check, and that at least four satisfy the general nonlinear scope requirement. Fetch again and integrate with the latest `origin/main-bot`, preserving concurrent changes. Preserve any newly added proposal artifacts; their presence alone does not require replacing a literature-supported direction. The Reviewer must approve the exact final document as an accurate proposal report, including any negative verdicts and unresolved concerns; approval does not require all directions to be rated PROMISING. Inspect the final diff and run `git diff --check`. Stage only the new proposal file.

Only the Reviewer creates exactly one final commit and pushes it to `main-bot`, without force-pushing. This task explicitly authorizes that push after review. Do not create intermediate commits. If the remote advances, fetch, integrate, review again, and recreate the unpublished commit on the new base so the task contributes exactly one commit containing only its proposal file.

The Researcher verifies that the approved commit is present on remote `main-bot`. Report the proposal file path, a brief list of the five titles, and the pushed commit ID, then stop. If a genuine blocker prevents the push, report it honestly rather than claiming completion.
