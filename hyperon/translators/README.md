# HE <-> PeTTa MeTTa Translator

Bidirectional translator between Hyperon Experimental (HE) and PeTTa MeTTa
dialects.  The command-line translator is implemented in Prolog; the
shared-core translation rules are accompanied by a Lean formalization and
runtime regression tests.

## Prerequisites

- [SWI-Prolog](https://www.swi-prolog.org/) (tested with v10.0+)

## Quick Start

```bash
# HE -> PeTTa
./translate.sh he2petta program.metta program_petta.metta

# PeTTa -> HE
./translate.sh petta2he program.metta program_he.metta

# PeTTa -> PeTTa --he profile, preserving PeTTa goal-control surfaces
./translate.sh petta2he --petta-he program.metta program_petta_he.metta

# PeTTa -> PeTTa --he profile, preserving hyperpose too
./translate.sh petta2he --petta-he --preserve-hyperpose program.metta program_he_hyperpose.metta

# Run test suite
./translate.sh --test
```

## Examples

### HE → PeTTa: sequential side effects

```metta
; Input (HE dialect):
(= (foo $x) (chain (bar $x) $y (baz $y)))
(= (run) (chain (do-stuff) $_ (chain (do-more) $_ done)))
(nop (println! "side effect"))
(collapse-bind (match &self ($x $y) ($y $x)))
```

```metta
; Output (PeTTa dialect):
(= (foo $x) (let $y (bar $x) (baz $y)))
(= (run) (let $_ (do-stuff) (let $_ (do-more) done)))
(let $__tr_discard_1 (println! "side effect") ())
(collapse (match &self ($x $y) ($y $x)))
```

### PeTTa → HE: procedural patterns

```metta
; Input (PeTTa dialect):
(= (run) (progn (println! "hello") (println! "world") done))
(= (first $x) (prog1 $x (println! "done")))
(= (count-matches $pat) (foldall (+ $acc 1) $pat 0))
```

```metta
; Output (HE dialect):
(= (run) (chain (println! "hello") $__tr_discard_1
           (chain (println! "world") $__tr_discard_2 done)))
(= (first $x) (let $__tr_result_3 $x
                 (chain (println! "done") $__tr_discard_4 $__tr_result_3)))
(= (count-matches $pat) (let $__tr_collapsed_5 (collapse $pat)
                           (foldl-atom $__tr_collapsed_5 0 $__tr_acc_6 $__tr_item_7
                             (eval ((+ $acc 1) $__tr_acc_6 $__tr_item_7)))))
```

### Real-world: backward chainer (51 atoms)

```bash
$ ./translate.sh he2petta tests/bench_backchain_he.metta build/bc_petta.metta
$ head -5 build/bc_petta.metta
; Translated from HE to PeTTa (51 atoms)
; Source: tests/bench_backchain_he.metta

(Evaluation (philosopher p1))
(Evaluation (philosopher p2))
```

The translated file runs on PeTTa and produces identical results.

## Translation Modes

### Single File

```bash
./translate.sh he2petta input.metta output.metta
./translate.sh petta2he input.metta output.metta
```

### Recursive (with imports)

Translates a file and all its local `.metta` imports in place,
writing translated siblings with renamed filenames:

```bash
./translate.sh he2petta --recursive program.metta
# Creates: program.he2petta.metta, support/module.he2petta.metta, etc.
```

### Bundle

Translates a file and all local imports into a self-contained directory:

```bash
./translate.sh petta2he --bundle program.metta translated_dir/
# Creates: translated_dir/program.metta, translated_dir/support/module.metta, etc.
```

### Extended Mode (PeTTa -> HE only)

Emits `collect` instead of `collapse` for `foldall` lowering
and uses HE-extended committed-choice surfaces such as `select`.
This is appropriate for CeTTa `--profile he-extended` and PeTTa `--he`,
but it is not an upstream-HE-core claim:

```bash
./translate.sh petta2he --extended input.metta output.metta
```

### PeTTa HE Profile Mode (PeTTa -> HE only)

Preserves PeTTa `--he` profile goal-control surfaces such as `once` and `cut`.
Use this for artifacts intended to run specifically with `./run.sh --he`, not
for backend-agnostic upstream HE examples:

```bash
./translate.sh petta2he --petta-he input.metta output.metta
```

### Hyperpose-Preserving Mode (PeTTa -> HE only)

Preserves `hyperpose` instead of lowering it to `superpose`. Use this only for
HE runtimes that provide `hyperpose` semantics, such as `petta --he`:

```bash
./translate.sh petta2he --preserve-hyperpose input.metta output.metta
```

In the PeTTa HE profile repository's `examples/he_translated/` directory, the
portable/default outputs use the `_he.metta` suffix. For sources whose
portability story specifically depends on deparallelizing `hyperpose`, the
portable sequentialized artifact may instead use `_he_sequential.metta`, while
preserve-hyperpose artifacts conventionally use `_he_parallel.metta`. That
naming keeps ordinary portable HE output separate from the rare cases where we
make the sequentialized hyperpose lowering explicit, and from runtime-specific
hyperpose support.

## What Gets Translated

| HE Construct | PeTTa Equivalent |
|-------------|-----------------|
| `chain expr var body` | `let var expr body` |
| `collapse-bind expr` | `collapse expr` |
| `superpose-bind list` | `superpose list` |
| `nop expr` | `let $_ expr ()` |
| `switch val branches` | `case val branches` |
| `function (return x)` | `x` |
| `unique expr` | `let $xs (collapse expr') (let $u (unique-atom $xs) (superpose $u))` |

| PeTTa Construct | HE Equivalent |
|----------------|--------------|
| `progn a b c` | `let $_ a (let $_ b c)` |
| `prog1 a b c` | `let $r a (let $_ b (let $_ c $r))` |
| `foldall agg goal init` | `let $list (collapse goal) (foldl-atom ...)` |
| `foldl-atom list init agg` | `foldl-atom list' init' $acc $item (eval (agg' $acc $item))` |
| `quote expr` | `quote expr'` in the pure lane; PeTTa-profile artifacts may use a helper representation |
| `call/eval/reduce expr` | `unquote (quote expr')` for syntactic expressions; `unquote $code` for quoted-code variables |
| `length (collapse expr)` | `let $tuple (collapse expr') (size-atom $tuple)` |
| `test actual expected` | Self-contained observable test via a file-local `test` helper |
| `once expr` | Pure lane: first result via `collapse` + `case` + `decons-atom`; extended lane: `select 1 expr'`; PeTTa-profile lane: `once expr'` |
| `unique-atom (collapse expr)` | `collapse (unique expr')` |
| `hyperpose exprs` | `superpose exprs'` by default, or `hyperpose exprs'` with `--preserve-hyperpose` |
| `@<` | `<s` (string comparison) |

## What's NOT Translated

- Python FFI (`py-atom`, `py-call`, `py-dot`) — passed through unchanged
- Git module imports — passed through unchanged
- PeTTa `cut` search control — passed through only for PeTTa-profile targets;
  the default pure PeTTa-to-HE translator rejects it because there is no
  current clean upstream-HE-core lowering
- PeTTa-native `msort` over arbitrary atoms — passed through only for
  PeTTa-profile targets or when the source defines `msort` itself; the default
  pure translator rejects unprovided `msort` because HE core has no specified
  total order over arbitrary atoms
- PeTTa-specific Prolog builtins (e.g., `fail`) — require manual adaptation

Note: `hyperpose` is lowered to sequential nondeterministic choice by default,
including computed-list cases such as `let $xs ... (hyperpose $xs)`. Use
`--preserve-hyperpose` when targeting an HE runtime that genuinely supports a
`hyperpose` surface; the default portability contract remains sequential.
Likewise, default `once` is lowered through pure HE building blocks
(`collapse`, `case`, and `decons-atom`), so it does not depend on `select`. Use
`--extended` when deliberately targeting CeTTa-style `select`, and use
`--petta-he` when targeting PeTTa `--he` performance/behavior specifically;
that mode preserves `once`.

Cross-engine validation has two distinct lanes:

```bash
# PeTTa --he profile artifacts in examples/he_translated/
cd ../petta-he-profile
HE_METTA_BIN=/path/to/metta tests/tools/check_generated_he_portability.sh

# Fresh default pure-HE translator outputs under .he-logs/
HE_METTA_BIN=/path/to/metta tests/tools/run_pure_he_engine_bench.sh
```

The second command is the stricter check for backend-neutral translation,
because it regenerates default pure outputs instead of using PeTTa-profile
artifacts.

## Verified Properties

The shared-core translation rules are accompanied by a sorry-free Lean 4
development and by command-line regression tests.  The Lean development covers:

- **Pattern matching equivalence** between HE and PeTTa matching
- **Equation dispatch correspondence** for the pure fragment
- **`progn` -> `let*`** and **`foldall` -> `collapse+foldl-atom`** lowering
- **State-operation boundary** — PeTTa named state is lowered through explicit
  helpers; HE native state is not treated as stable-common identity syntax
- **Helper-name hygiene** — generated helper names avoid source-symbol
  collisions instead of shadowing user code
- **Space operations** (`match`, `add-atom`, `remove-atom`, `new-space`) formalized
- **Import commutativity** — translating a stable-common module then importing
  produces the same space as importing then translating (kernel-checked)
- **`change-state!` return value** — trusted mode wraps HE's `(State val)` return
  for PeTTa compatibility without modifying PeTTa's runtime

### Running the Lean Translator

The Lean translator is an executable function (`translateHE`, `translatePeTTa`)
that can be invoked via `lake env lean --run`:

```bash
cd /path/to/mettapedia
lake env lean --run your_script.lean
```

Where `your_script.lean` imports
`Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslate` and calls
`translatePeTTa` or `translateHE` on Atom values.  The Lean translator mirrors
the core rewrite rules and is kernel-checked.  The Prolog CLI additionally does
file/program-level helper-name selection to avoid source-symbol collisions
before emitting concrete helper definitions.

Lean proofs: `lean-projects/mettapedia/Mettapedia/Languages/MeTTa/Translation/`

## File Structure

```
translators/
  translate.sh          # CLI wrapper (this tool)
  metta_parser.pl       # S-expression parser (DCG-based)
  he_to_petta.pl        # HE -> PeTTa translation rules
  petta_to_he.pl        # PeTTa -> HE translation + optimizer
  he_petta_relational.pl # Relational core (proof-friendly)
  test_on_real_files.pl  # File-level driver + recursive/bundle
  test_translators.pl    # Unit test suite
```
