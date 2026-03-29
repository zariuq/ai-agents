# HE <-> PeTTa MeTTa Translator

Bidirectional translator between Hyperon Experimental (HE) and PeTTa MeTTa dialects, backed by a sorry-free Lean proof of semantic correspondence.

## Prerequisites

- [SWI-Prolog](https://www.swi-prolog.org/) (tested with v10.0+)

## Quick Start

```bash
# HE -> PeTTa
./translate.sh he2petta program.metta program_petta.metta

# PeTTa -> HE
./translate.sh petta2he program.metta program_he.metta

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
$ ./translate.sh he2petta tests/bench_backchain_he.metta /tmp/bc_petta.metta
$ head -5 /tmp/bc_petta.metta
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
(CeTTa-compatible, not standard HE):

```bash
./translate.sh petta2he --extended input.metta output.metta
```

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
| `unique-atom (collapse expr)` | `collapse (unique expr')` |
| `@<` | `<s` (string comparison) |

## What's NOT Translated

- Python FFI (`py-atom`, `py-call`, `py-dot`) — passed through unchanged
- Git module imports — passed through unchanged
- PeTTa-specific Prolog builtins (e.g., `fail`) — require manual adaptation

## Verified Properties (Lean)

The translation is backed by a sorry-free Lean 4 proof (5,400+ lines, 0 sorries):

- **Pattern matching equivalence** between HE and PeTTa matching
- **Equation dispatch correspondence** for the pure fragment
- **`progn` -> `let*`** and **`foldall` -> `collapse+foldl-atom`** lowering
- **State operations** (`new-state`, `get-state`, `change-state!`) operational bridge
- **Space operations** (`match`, `add-atom`, `remove-atom`, `new-space`) formalized
- **Import commutativity** — translating a stable-common module then importing
  produces the same space as importing then translating (kernel-checked)
- **`change-state!` return value** — trusted mode wraps HE's `(State val)` return
  for PeTTa compatibility without modifying PeTTa's runtime

### Running the Lean Translator

The Lean translator is an executable function (`translateHE`, `translatePeTTa`)
that can be invoked via `lake env lean --run`:

```bash
cd ~/claude/lean-projects/mettapedia
lake env lean --run your_script.lean
```

Where `your_script.lean` imports `Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslate`
and calls `translatePeTTa` or `translateHE` on Atom values. The Lean translator
produces the same translations as the Prolog CLI but is kernel-checked.

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
