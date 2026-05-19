# HE <-> PeTTa Translation Semantics

Status: draft engineering specification.

This document is the code-near semantic contract for the HE <-> PeTTa
translator in this directory.  It explains which language surfaces are shared,
which are implementation/profile-specific, and how the translator classifies
generated files that require helper or profile support.

The command-line entry point is:

```bash
./translate.sh he2petta input.metta output.metta
./translate.sh petta2he input.metta output.metta
```

The implementation is in:

```text
he_to_petta.pl
petta_to_he.pl
he_petta_relational.pl
metta_parser.pl
test_translators.pl
test_on_real_files.pl
```

The PeTTa HE runtime profile is specified separately in:

```text
../petta-he-profile/specs/petta-he-compatibility-profile.md
../petta-he-profile/src/he/DIVERGENCES.md
```

## 1. Purpose

The translator has two related but distinct jobs.

1. Translate programs in the common HE/PeTTa fragment with preserved observable
   behavior.
2. Make non-common surfaces explicit, either by lowering them to a portable
   target form or by marking them as helper/profile-specific.

The translator keeps these categories explicit.  In particular, a file that
requires PeTTa HE compatibility helpers is not a pure-HE conformance artifact
merely because it has `.metta` syntax.

Positive example:

```metta
!(test (length (collapse (demo-peano 300))) 301)
```

can be translated to:

```metta
!(test (let $__tr_tuple_1 (collapse (demo-peano 300))
         (size-atom $__tr_tuple_1))
       301)
```

This is ordinary lowering: the PeTTa convenience surface is replaced by an
explicit HE-facing computation.

Negative example:

```metta
!(test (quote (+ 1 2)) (+ 1 2))
```

cannot be presented as a pure-HE claim unless the target semantics for
PeTTa-style quote-as-syntax are supplied or lowered away.  The translator uses a
helper surface for this PeTTa compatibility lane.

## 2. Semantic Lanes

Generated artifacts and audit reports should distinguish these lanes.

| Lane | Meaning | Example |
| --- | --- | --- |
| Shared core | Runs by the same visible rules in the target engines considered. | `if`, `case`, many `let`, `match`, arithmetic examples. |
| Portable lowering | Source surface is rewritten to target forms without PeTTa-only assumptions. | `length (collapse e)` -> `let tuple (collapse e) (size-atom tuple)`. |
| Translator helper | Generated artifact needs a small helper definition to preserve source behavior. | `test`, `assertEqualToEval`, `quoted-syntax`. |
| PeTTa HE compatibility | Intended for `./run.sh --he`; may use PeTTa profile behavior outside HE core. | Callable-return application, selected quote/eval/reduce compatibility. |
| PeTTa extension | Useful PeTTa surface outside the strict HE portability claim. | Python FFI, selected host/runtime support surfaces. |

The default `petta2he` mode should prefer shared core or portable lowering.  If
a helper is emitted, the artifact should be classified as using a helper
surface.  If `--preserve-hyperpose` is used, the artifact is intentionally not
the default pure-portable hyperpose lowering.

Generated helper names are context-sensitive.  The translator first scans the
source program and chooses helper symbols that do not collide with source
symbols.  For example, if a source program already defines `quoted-syntax`, the
generated quote helper will use a fresh `__tr-quoted-syntax-N` name instead of
capturing or shadowing the source definition.

## 3. HE Core Surface Used By The Translator

The translator targets the operational HE surface centered on evaluated top
level atoms, expressions as data unless reduced, and the minimal MeTTa
instructions used by HE implementations.

Important target constructs include:

| HE-facing construct | Role |
| --- | --- |
| `chain` | Sequenced evaluation with result binding. |
| `collapse` / `collapse-bind` | Collect nondeterministic results into a tuple-like value. |
| `superpose` / `superpose-bind` | Re-enter nondeterministic results as alternatives. |
| `eval` / `evalc` / `unquote` | Explicit evaluation of syntax/data under the runtime profile. |
| `case` / `switch` | Pattern-directed branching. |
| `size-atom` | Explicit tuple length/count surface. |
| `function` / `return` | Minimal function-return surface. |
| `metta` | Interpreter call with expected type and space. |

The translator should not invent HE-core claims for surfaces that are only
present in a particular implementation.  Such surfaces belong in a profile or
extension lane.

## 4. PeTTa Source Surface

PeTTa source programs use ordinary MeTTa syntax plus Prolog-backed runtime
conveniences.  Some are shared with HE.  Some are PeTTa-specific conveniences.
Some are observed behavior rather than written HE-core spec.

Important PeTTa-facing surfaces include:

| PeTTa surface | Translation status |
| --- | --- |
| `let`, `let*`, `if`, `case`, `match`, `collapse`, `superpose` | Usually shared or nearly identity. |
| `progn`, `prog1` | Lowered to sequenced `chain`/`let` forms. |
| `foldall`, PeTTa-style `foldl-atom` | Lowered to `collapse` plus explicit `foldl-atom` accumulator/item variables. |
| `length (collapse e)` | Lowered to `let tuple (collapse e) (size-atom tuple)`. |
| `test` | Preserved as an observable source-test helper, not silently replaced by a quiet assertion. |
| `bind! name (new-state value)`, `get-state name`, `change-state! name value` | Lowered to PeTTa named-state helpers; not HE native state. |
| `quote`, `eval`, `reduce` | PeTTa compatibility lane; see Section 7. |
| `hyperpose` | Lowered to `superpose` by default, preserved only with explicit target intent. |
| Python/Git/host FFI | Passed through or classified as extension; not pure HE. |

## 5. HE -> PeTTa Rules

The HE-to-PeTTa direction adapts explicit HE sequencing and binding forms to
PeTTa source forms.

| HE input | PeTTa output | Notes |
| --- | --- | --- |
| `(chain e $x b)` | `(let $x e b)` | Preserves sequencing and result binding. |
| `(collapse-bind e)` | `(collapse e')` | Preserves collected nondeterministic results. |
| `(superpose-bind xs)` | `(superpose xs')` | Re-enters collected results as alternatives. |
| `(nop e)` | `(let $__tr_discard_n e' ())` | Keeps effects, discards result. |
| `(switch x branches)` | `(case x' branches')` | Branches translated recursively. |
| `(function (return x))` | `x'` | Removes minimal function wrapper where safe. |
| `(unique e)` | `let/collapse/unique-atom/superpose` | Uses PeTTa's available uniqueness surface. |

Fresh names use the `$__tr_...` namespace.  Translation must avoid capturing
source variables.  The relational core threads freshness explicitly so the
capture-avoidance contract is visible to proof-oriented tooling.

## 6. PeTTa -> HE Rules

The PeTTa-to-HE direction lowers PeTTa conveniences to explicit HE-facing
forms.

| PeTTa input | HE-facing output | Notes |
| --- | --- | --- |
| `(progn a b c)` | nested sequencing | Effects and final result preserved. |
| `(prog1 a b c)` | result capture plus sequencing | First result preserved after later effects. |
| `(foldall agg goal init)` | `let list (collapse goal') (foldl-atom ...)` | Makes collection and fold explicit. |
| `(foldl-atom list init agg)` | explicit `foldl-atom list init $acc $item (eval (...))` | Introduces accumulator/item variables. |
| `(length (collapse e))` | `let tuple (collapse e') (size-atom tuple)` | Portable visible lowering. |
| `(test actual expected)` | `(test actual' expected')` | Preserves observable test reporting. |
| `(unique-atom (collapse e))` | `(collapse (unique e'))` | Uses HE uniqueness surface where available. |
| `(hyperpose xs)` | `(superpose xs')` by default | Preserves nondeterministic values, not parallel scheduling. |
| `(bind! name (new-state value))` | `(__tr-petta-state-set! name' value')` | PeTTa named-state initialization, not HE native state allocation. |
| `(get-state name)` | `(__tr-petta-state-get name')` | PeTTa named-state read. |
| `(change-state! name value)` | `(__tr-petta-state-set! name' value')` | PeTTa named-state update. |
| `(new-state value)` outside `bind!` | `(quoted-syntax (quote (new-state value')))` | Preserves PeTTa data syntax; does not allocate an HE state handle. |
| `(@< a b)` | `(<s a' b')` | String comparison naming bridge. |

Positive example:

```metta
!(test (length (collapse (demo-peano 300))) 301)
```

becomes:

```metta
!(test (let $__tr_tuple_1 (collapse (demo-peano 300))
         (size-atom $__tr_tuple_1))
       301)
```

Negative example:

```metta
(= (bad $x) (let $__tr_tuple_1 something $x))
```

Source programs may already use `$__tr_...` names.  A production translator
must still generate fresh names that do not capture or shadow source variables.

## 7. Quote, Eval, Reduce, And `quoted-syntax`

This is a compatibility boundary where runtimes commonly differ.

PeTTa default mode exposes:

```metta
!(quote (+ 1 2))
```

as the syntax value:

```text
(+ 1 2)
```

Some HE implementations expose `quote` as a visible wrapper:

```text
(quote (+ 1 2))
```

The translator preserves PeTTa-visible behavior by emitting a file-local helper
when needed:

```metta
(= (quoted-syntax (quote $expr)) $expr)
```

and lowering PeTTa quote:

```metta
(quote e)
```

to:

```metta
(quoted-syntax (quote e'))
```

PeTTa `eval` and `reduce` are lowered through an explicit HE-facing evaluation
of translated syntax:

```metta
(eval e)    -> (unquote (quote e'))
(reduce e)  -> (unquote (quote e'))
```

This is a PeTTa-compatibility translation, not a claim that `quoted-syntax` is
HE core.  A backend-agnostic artifact must either avoid this surface, provide
the helper, or use a target-specific quote/eval representation with an
explicit conformance claim.

Positive example:

```metta
(= (before-quote) (quote-before (quote (fib 5))))
```

can become, for the PeTTa HE compatibility target:

```metta
(= (before-quote)
   (quote-before (quoted-syntax (quote (fib 5)))))
```

Negative example:

```metta
; Do not claim this helper is HE core.
(= (quoted-syntax (quote $expr)) $expr)
```

## 8. State

PeTTa and HE both use the spellings `new-state`, `get-state`, and
`change-state!`, but they do not denote the same portable contract.

PeTTa named state:

```metta
!(bind! counter (new-state 0))
!(change-state! counter 1)
!(get-state counter)
```

uses the symbol `counter` as a mutable cell name.  In PeTTa's implementation,
`bind! name (new-state value)` delegates to `change-state! name value`, and the
state is stored by name.

HE native state:

```metta
!(let $s (new-state 0)
   (change-state! $s 1))
```

allocates and updates an explicit state handle.  Treating PeTTa named-state
syntax as HE native state changes the meaning of later `get-state` and
`change-state!` calls, so it is not a valid stable-common identity translation.

The PeTTa-to-HE direction therefore lowers the whole PeTTa named-state family
to file-local helpers:

| PeTTa source | HE-facing generated form |
| --- | --- |
| `(bind! name (new-state value))` | `(__tr-petta-state-set! name' value')` |
| `(change-state! name value)` | `(__tr-petta-state-set! name' value')` |
| `(get-state name)` | `(__tr-petta-state-get name')` |
| standalone `(new-state value)` | `(quoted-syntax (quote (new-state value')))` |

The helper definitions use an atomspace-backed cell relation:

```metta
(__tr-petta-state-cell name value)
```

and are generated only when the translated program uses the helper surface.
This is a translator-helper lane, not an HE-core claim.  The concrete helper
symbols are chosen to avoid source-program collisions; the names shown above
are the default names when they are unused by the source.

The HE-to-PeTTa direction may pass HE native state spellings through as HE
source syntax.  That passthrough is not evidence that PeTTa named state and HE
native state are stable-common syntax; it only preserves an HE-facing source
surface for a PeTTa target profile that already provides compatible runtime
support.

Positive example:

```metta
(progn
  (bind! counter (new-state 0))
  (change-state! counter 1)
  (get-state counter))
```

becomes:

```metta
(let $__tr_discard_1 (__tr-petta-state-set! counter 0)
  (let $__tr_discard_2 (__tr-petta-state-set! counter 1)
    (__tr-petta-state-get counter)))
```

Negative example:

```metta
(bind! counter (new-state 0))
```

must not be translated by simply passing `(new-state 0)` through as an HE state
handle constructor.  That would silently switch from PeTTa's named-cell
semantics to HE's handle semantics.

## 9. Tests And Assertion Surfaces

PeTTa `test` has observable output:

```text
is actual, should expected. ...
```

Therefore translating `test` to a quiet assertion is not semantically faithful
for source examples whose observable output matters.  Current generated PeTTa
source translations preserve `test`.

`assertEqualToEval`, `assertEqualToResult`, `assertAlphaEqualToResult`, and
related assertion helpers are allowed for HE-facing profile tests.  They are
translator/helper surfaces unless a target runtime natively provides them.

Positive example:

```metta
!(test (+ 1 2) 3)
```

stays:

```metta
!(test (+ 1 2) 3)
```

Negative example:

```metta
!(assertEqualToEval (+ 1 2) 3)
```

should not be used as the automatic lowering of a source `test` if the source
program expected PeTTa's printed `test` report.

## 10. Hyperpose

`hyperpose` is PeTTa's parallel nondeterministic surface.  Portable HE does not
require this exact scheduling/parallelism surface.

Default behavior:

```metta
(hyperpose xs)
```

is lowered to:

```metta
(superpose xs')
```

This preserves nondeterministic values, but not parallel execution strategy.
Programs should not rely on result order unless the target profile declares an
ordering contract.

Explicit preserve mode:

```bash
./translate.sh petta2he --preserve-hyperpose input.metta output.metta
```

keeps:

```metta
(hyperpose xs')
```

and the artifact must be classified as requiring a runtime with `hyperpose`
support.

## 11. Type And Unknown Behavior

Unknown type behavior must be explicit because it affects translation
soundness.

Current intended behavior:

```metta
!(get-type $x)
```

returns:

```metta
%Undefined%
```

while:

```metta
!(get-metatype $x)
```

returns:

```metta
Variable
```

Returning a fresh type variable for `(get-type $x)` is unsound for translation
because that variable can escape into stored type facts and later unify with
concrete types, creating branch-order-dependent behavior.  Unknown types should
remain unknown; metatypes distinguish variables.

## 12. Imports, Spaces, And Host Resources

Translation over imports has two forms:

| Mode | Behavior |
| --- | --- |
| `--recursive` | Translate a file and local imports beside their sources. |
| `--bundle` | Translate a file and local imports into a self-contained output tree. |

Space operations, state operations, and host resources are part of the
validation boundary.  The translator may preserve source operations when the
target runtime supports the same contract, but must not claim pure HE
portability for host-specific spaces, MORK/PathMap handles, Python handles, Git
imports, HE native state, PeTTa named state, or other implementation resources
unless the target profile declares the contract explicitly.  PeTTa named state
is handled by the helper lowering in Section 8.

## 13. Proof And Validation Status

There are three different evidence layers.

| Evidence | What it supports |
| --- | --- |
| Unit tests in `test_translators.pl` | Individual syntactic rewrite rules and helper insertion behavior. |
| Real-file translator tests in `test_on_real_files.pl` | Parser, serializer, recursive/bundle workflows, and corpus translation shape. |
| Lean translator/proof development | Pure/common-fragment correspondence claims and explicit freshness discipline. |
| PeTTa HE profile suite/survey | Runtime correctness and performance for generated artifacts under `./run.sh --he`. |
| Cross-engine portability checker | Classification of behavior across PeTTa `--he`, CeTTa, and upstream HE when available. |

The tests and survey should be run before claiming a production-relevant change:

```bash
./translate.sh --test
cd ../petta-he-profile
./tests/run_he_profile_suite.sh
HE_SURVEY_OVERWRITE=1 ./tests/tools/run_translator_survey.sh
```

The cross-engine checker needs explicit target engine paths:

```bash
HE_METTA_BIN=/path/to/metta \
TIMEOUT_SECONDS=30 \
./tests/tools/check_generated_he_portability.sh
```

## 14. Production Readiness Criteria

A translation rule is production-ready only when all applicable items are true.

1. The source and target semantic lanes are named.
2. The rule has positive and negative examples.
3. Fresh variables are capture-avoiding.
4. Generated helper names avoid collisions with source symbols.
5. Observable output is preserved or the deviation is explicitly classified.
6. Helper surfaces are named as helpers, not HE core.
7. `translate.sh --test` passes.
8. A representative generated artifact runs under its intended target.
9. Cross-engine differences are classified when the artifact is described as
   portable.

For performance work, correctness gates come first.  A faster generated program
that changes source behavior is a regression, not an optimization.

## 15. Current Open Edges

The following areas remain intentionally visible rather than hidden.

| Edge | Current handling |
| --- | --- |
| `quote` / `eval` / `reduce` | PeTTa HE compatibility via `quoted-syntax` and `unquote`; not pure HE core. |
| PeTTa named state | Lowered via `__tr-petta-state-*` helpers; not HE native state identity. |
| `test` | Preserved for source examples; helper/assertion surfaces classified separately. |
| `hyperpose` | Lowered to `superpose` by default; preserved only under explicit mode. |
| Host resources | Passed through or extension-classified; not pure HE. |
| Implementation output shape | Survey/oracle tooling normalizes where justified and records divergences. |

This document should be updated whenever a translation rule changes, a helper
is added or removed, or a cross-engine classifier label changes.
