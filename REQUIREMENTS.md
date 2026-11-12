# Requirements

## LongTails project

- Elan, with Lean and Lake using the version in `lean-toolchain`.
- Python 3.

Lean libraries and verification tools are declared in `lakefile.toml` and pinned
in `lake-manifest.json`: mathlib, LeanTeX, ProofWidgets, Batteries, Comparator,
and lean4export. Lake manages their dependencies; do not update the pinned
revisions during setup.

Run the following command from the repository root to fetch the Mathlib build
cache and build the project:

```sh
./build.sh
```

## Contribution (optional)

Install Ruff for Python linting and formatting in your active environment:

```sh
python3 -m pip install ruff==0.17.0
```

If you add, remove, or rename Lean modules, update the import index:

```sh
lake exe mk_all --lib LongTails
```

Then run linters:

```sh
./lint.sh
```

To independently audit a public theorem and its budget, run:

```sh
python3 run_comparator.py YourTheorem.lean
```

To audit all theorems with four parallel workers, run `python3 run_comparator.py -j 4`.
The script builds the selected modules first, then runs the audits in parallel.

## Server (optional)

See [server/README.md](server/README.md) for website generation and serving requirements.

## Agent scripts (optional)

Install the Python dependencies for the automation scripts:

```sh
python3 -m pip install -r scripts/requirements.txt
```

This installs `tomlkit` for reading and updating TOML files. Additional tools depend on the workflow you choose:

- Research and proposal runners require the selected agent CLI (`codex`, `omp`, or `claude`) and its authentication.
- `scripts/run_results_table_prompt.py` requires `latexmk` and a TeX distribution with `pdflatex`, BibTeX, and the `amsmath`, `amssymb`, `array`, `booktabs`, `tabularx`, `threeparttable`, `textcomp`, `natbib`, `hyperref`, and `changepage` packages (for example, TeX Live or MacTeX).
- `scripts/run_prompt_tmux.py` also requires a running tmux server and zsh. Its `--openrouter` mode requires `OPENROUTER_API_KEY`.
- `infra/generate_token.py` requires OpenSSL, curl, a configured GitHub App private key, and `AUTO_MATH_BOT_INSTALLATION_ID` set to the installation ID for `k3nfalt` with access to `longtails`.
