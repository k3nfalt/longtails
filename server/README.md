# Server requirements

- Python 3.
- Pandoc for generating HTML with [build.py](build.py).
- The [Lean project requirements](../REQUIREMENTS.md#lean-project) when extracting theorem descriptions from Lean sources.

Serving the generated page with [serve.py](serve.py) requires only Python.

## Build the website

From the repository root, run:

```sh
python3 -m server.build
```

This extracts Lean theorem metadata and renders the website without running Codex.
Existing setup descriptions and reference reports are reused. Missing setup
descriptions are shown as “Description not generated.”; missing reference reports
are left unassessed.

To use Codex to generate only missing descriptions and reference reports:

```sh
python3 -m server.build --generate-descriptions --model gpt-6.1-sol -j 10
```

To regenerate all descriptions, theorem metadata, and reference reports, including
existing files:

```sh
python3 -m server.build --regenerate-all --model gpt-6.1-sol -j 10
```

Both generation options require an authenticated Codex CLI and can incur costs.
`--model` and `-j` configure these runs; they do not enable generation themselves.
Review the generated text and citations before publishing.

To serve the generated page locally:

```sh
python3 server/serve.py
```
