# Research automation

This directory contains agent runners, prompt templates, and research artifacts.
Run commands from the repository root; each runner supports `--help`.

- `run_research_prompt.py`: investigate a research direction, optionally from a proposal.
- `run_proposals_prompt.py`: generate research proposals, optionally guided by keywords.
- `run_novelty_prompt.py`: review one theorem or all unreviewed theorems.
- `run_results_table_prompt.py`: turn reviews into comparison tables.
- `run_prompt_tmux.py`: launch research or proposal runners in a tmux window.
- `prompts/`: task instructions used by the runners.
- `reviews/` and `tables/`: saved reviews and comparison artifacts.
- `positive_examples.md`, `negative_examples.md`, and `negative_examples/`: guidance for assessing contributions.
- `requirements.txt`: Python dependencies; see [project requirements](../REQUIREMENTS.md).

Proposal runs save files under `scripts/proposals/`. The table runner and website
both use `scripts/tables/` by default.

`nolints-style.txt` is an empty exceptions file at the path hardcoded by mathlib's
style linter. It prevents a missing-file warning and suppresses no checks.

GitHub authentication and PR postprocessing live in `infra/`.
