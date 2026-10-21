PR delivery

These additional instructions select PR delivery instead of the default local delivery. Give them to the Reviewer unchanged. All shared research, review, and verification requirements remain mandatory. Completion additionally requires the approved commit, its ready-for-review PR, and the cleanup below.

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

Only the Reviewer may create the final commit and push to the task branch. Include the companion contribution note in the same reviewed final commit as the Lean deliverables.

7. Acceptance and submission

Complete every check in section 7 of the shared research prompt before committing or submitting. Confirm that only the requested deliverables are staged.

The Reviewer then creates the single final research commit, verifies that it matches the approved contents, and pushes it to the task's unique `agent/<unique-task-name>` branch. This task explicitly authorizes that push and opening one ready-for-review PR targeting `main` once all acceptance criteria pass. It never authorizes pushing or merging into `main`.

Before submission, confirm `git rev-list --count origin/main..HEAD` is exactly 1. Use `python3 infra/generate_token.py` for each GitHub operation. Create one ready-for-review PR with `gh pr create --base main --head <task-branch> --title <title> --body-file <file>`. Include the theorem, setup, contribution note, and verification evidence in the PR body. Write multiline PR text to a temporary file. Verify that the PR exists, is not a draft, and contains the approved research commit, clean up the task worktrees as described below, report its URL, and stop. Do not dispatch or monitor workflows, append commits, force-push, or automatically retry, repair, replace, or close the PR.

PR creation automatically starts verification and novelty reviews. Postprocessing adds a second commit containing only `scripts/reviews/<TheoremName>.md` for each new theorem. Negative novelty reviews do not block this stage. Tables, references, metadata, and website generation remain separate manual steps. Failed PRs remain open for the user to inspect.

After verifying the submitted PR, stop all processes using the task worktrees and remove both agents’ worktrees with `git worktree remove`, running from outside those directories. The Researcher coordinates cleanup before the final response. Remove only worktrees created for this task; keep branches and the submitted PR. Use `--force` only after confirming that remaining files are already preserved in the pushed commit or are disposable task-generated artifacts. If any work is unpreserved, submission failed, or the task is paused, keep the affected worktree and report its path and reason.

In the final report, also include the pushed research commit ID and PR URL, or an explicit explanation of why submission was blocked.
