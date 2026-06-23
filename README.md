**English** | [Español](README.es.md)

# clingo-magic-sets

**Dynamic Magic Sets (DMS)** transformer for [Clingo](https://potassco.org/clingo/).

`dms.py` rewrites an ASP program annotated with `#magic pred/n` directives into an
equivalent program that restricts the *grounding* (variable elimination) of the
selected hidden predicates to the atoms relevant to the implicit query. Clingo
does not support Magic Sets natively; this tool provides them as an external
preprocessor, operating on Clingo's AST (Abstract Syntax Tree) through its Python
API.

This is an implementation of the Dynamic Magic Sets algorithm by Alviano, Faber,
Greco and Leone (see [References](#references)), developed as part of a *Traballo
Fin de Grao* (Grao en Intelixencia Artificial, Universidade da Coruña).

## Requirements

- Python ≥ 3.9
- [clingo](https://pypi.org/project/clingo/) (the Clingo Python API package)

```bash
pip install -r requirements.txt
```

## Usage

```bash
python dms.py input.lp [output.lp]
```

If no output file is given, the transformed program is written to `stdout`. The
result is a standard ASP program that can be passed directly to Clingo:

```bash
python dms.py examples/reach.lp reach_dms.lp
clingo reach_dms.lp
```

### Shortcut: `dms-solve.sh`

The `dms-solve.sh` script chains both steps (transform + solve) into a single
command. Any argument after the input file is forwarded as-is to `clingo`:

```bash
./dms-solve.sh examples/reach.lp              # transform and solve
./dms-solve.sh examples/reach.lp 0 --stats    # all answer sets + statistics
./dms-solve.sh -o reach_dms.lp examples/reach.lp   # keep the transformed program
./dms-solve.sh -h                             # help
```

Options: `-o FILE` saves the transformed program (a temporary file by default),
`-k` keeps the temporary file, `-q` quiet mode. The `PYTHON` environment variable
selects the interpreter.

## Input format

The program is annotated with one or more `#magic` directives, which declare the
predicates (MDB) to transform:

```prolog
#magic reach/2.            % transform reach/2

reach(X, Y) :- edge(X, Y).
reach(X, Z) :- reach(X, Y), edge(Y, Z).

query(X) :- source(X), reach(X, Y).
```

Only predicates declared with `#magic` are rewritten; the rest of the program is
copied unchanged (except for the seeds that depend on it).

## Examples

The [`examples/`](examples/) directory contains sample programs:

| File | What it illustrates |
|---|---|
| `reach.lp` | Graph reachability (running example, `bf` adornment). |
| `sameGen.lp` | Same generation (disconnected EDB, Sippu's analysis). |
| `factorial.lp`, `fibonacci.lp` | Arithmetic recursion with no explicit domain. |
| `area.lp` | Arithmetic with no domain (DMS as a *safety* provider). |
| `sat.lp` | Formulas as compound terms (function symbols, anonymous vars). |
| `member.lp` | Lists with Prolog syntax (`cons`). |

## Documentation

[`docs/DMS_ALGORITHM.md`](docs/DMS_ALGORITHM.md) describes the correspondence
between the original algorithm and the implementation, and the design decisions
(EDB-first SIPS, safe arithmetic, anonymous-variable freshening, stratification
check).

## References

- M. Alviano, W. Faber, G. Greco, N. Leone. *Magic Sets for Disjunctive Datalog
  Programs*. Artificial Intelligence 187–188 (2012) 156–192.
- F. Bancilhon, D. Maier, Y. Sagiv, J. D. Ullman. *Magic Sets and Other Strange
  Ways to Implement Logic Programs*. PODS 1986.

## License

[MIT](LICENSE) © 2026 Marcelo Ferreiro Sánchez.
