# reachmap

Which modules and functions of a project are called, and which are not? reachmap maps entry points (routes, pages,
`main`, schedulers, listeners), what is reachable from them, what only tests call, and what has no caller. For every
function it shows the call chain from the entry point.

One Python file, no dependencies, no model, no network. WebGoat (829 files) takes about 3 seconds.

## Usage

```bash
python3 reachmap.py ./project                                    # HTML + JSON report, summary in the terminal
python3 reachmap.py ./project --config reachmap.cfg              # custom entry points, framework code, exceptions
python3 reachmap.py ./project --coderaster run/coderaster.json   # show CodeRaster findings on the map
python3 reachmap.py ./project --trace NAME                       # callers and callees of one function
python3 reachmap.py ./project --formats json,sarif,openapi --fail-on unprotected-sink,new-unprotected   # CI
```

Reports go to `reachmap-data/runs/<timestamp>/`, one level above the program folder (`--out`, `--data-dir` or
`REACHMAP_DATA_DIR` change that). Other switches: `--exclude GLOB`, `--include-dir NAME`, `--baseline FILE|auto|none`,
`--source production|all|none`, `--no-git`, `--quiet`. Exit codes: `0` ok, `1` `--fail-on` hit, `2` usage error.

## What you get

- **Status per function:** entry point, called from an entry point, maybe called (name match only), run by the
  framework, only called by tests, no caller found, and more. Dead subtrees are reported with their top function.
- **Report (single HTML file, works offline):** module filter, function list with call chains, source viewer,
  and three graph views: *Map*, *Layers* and *Around a function* (columns or free force layout).
- **Trace:** follow any function up to its entry points and down to what it calls.
- **Attack surface:** every endpoint with method, path, parameters, access check (annotations, middleware, central
  Spring Security rules) and the dangerous calls it reaches (SQL, OS command, file access, deserialisation, XML,
  SSRF, redirect, code evaluation). Export as CSV, OpenAPI or SARIF.
- **Hotspots, deletion candidates and a comparison with the last run.**

A hit means "look here", not "vulnerable": the report reads the code, it does not test it. reachmap does not
generate requests, payloads or exploit code.

## Configuration

What the tool cannot see goes into a text file (see `examples/reachmap.example`):

```
entry jobs/nightly.py:cleanup        # started from outside
framework app/plugins/*.py           # loaded by the framework via names
ignore src/legacy/*                  # known, do not report
```

A `.reachmap` inside the scanned project only takes effect with `--trust-project-config`.

## Limits

- Except for Python it is text search, not a type-aware parser. Calls via interfaces, reflection, dependency
  injection and generated code are only seen if the name appears somewhere.
- "No caller found" is a hint to check, not proof of dead code. Same-named methods of different classes are not
  reliably told apart ("maybe called").
- Central access rules are only read from Spring `authorizeHttpRequests` chains; path prefixes one level deep.
- More precise per language: Go `deadcode`, knip (JS/TS), vulture (Python), ShipMonk dead-code-detector (PHP).

## Development

```bash
python3 -m pytest tests
```

Changes per version: `releases/`.

## License

MIT, see [LICENSE](LICENSE).
