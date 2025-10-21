# Mizar Error Zoo (4CP)

A compact A/B compendium of minimal examples that trigger and fix the error codes seen in this project’s curriculum. Keep `text/` and `dict/` as siblings; compile from module root with `mizf text/…`.

Legend: A = triggers; B = fixed. Snippets are intentionally tiny and self-contained.

## Paths / Environ

- 801 — Cannot find vocabulary file
  - **Root Cause**: Mizar cannot locate the `.voc` file referenced in `vocabularies` directive
  - **A (wrong working directory)**: `cd text && mizf lesson1`
    - Running from inside `text/` means `dict/` is not a sibling
  - **B (correct - module root)**: `cd .. && mizf text/lesson1.miz`
    - Module root is where `text/` and `dict/` are siblings

  - **A (vocabulary file name mismatch)**:
    - Article: `fparity.miz`
    - Vocabulary file: `FINITE_P.voc` (UPPERCASE, different name)
    - Directive: `vocabularies FINITE_P;`
    - **Result**: Error 801 even from correct directory!

  - **B (correct - lowercase matching article base)**:
    - Article: `fparity.miz`
    - Vocabulary file: `fparity.voc` (lowercase, matches article)
    - Directive: `vocabularies FPARITY;` (uppercase in directive)
    - **Result**: Compiles successfully!

  - **Critical Rule**:
    - Vocabulary **file name** must be **lowercase** and **match the article base name**
    - Vocabulary **directive** uses **UPPERCASE** version of the file name
    - Example: `fparity.miz` → `dict/fparity.voc` → `vocabularies FPARITY;`

  - **Why**: Mizar's vocabulary attachment mechanism requires the file name to match the article base for local vocabularies. System vocabularies (in MML) use different rules.

  - Curriculum refs:
    - Negative: `theories/00_curriculum/text/lesson21_op_props.miz` (local vocab LESSON21 without dict → 801 inside text/)
    - Positive: `theories/00_curriculum/text/lesson21_op_props_ok.miz` (MML‑only env; compiles)
    - **Working example**: `theories/02_parity/` - `fparity.miz` with `dict/fparity.voc` and `vocabularies FPARITY;`

- 830 — Nothing imported from notations
  - **Nature**: Non-fatal warning from Accommodator
  - **Root Cause**: An article listed in `notations` exports no symbols actually used in your article
  - **A (unused import)**:
    ```mizar
    notations XBOOLE_0, SUBSET_1, NAT_1, XCMPLX_0, XXREAL_0, ORDINAL1, INT_1, ...;
    ```
    where XCMPLX_0, XXREAL_0, ORDINAL1 symbols aren't referenced in definitions
  - **B (cleaned using irrvoc)**:
    ```bash
    # From module root with mizenv sourced:
    irrvoc build/finite_parity     # generates finite_parity.irv
    cat build/finite_parity.irv    # shows actual imports with usage counts
    # Remove entries with 0 usage from notations directive
    # Recompile → pristine green!
    ```

  - **CORRECTED UNDERSTANDING** (verified 2025-10-21):
    - **Myth**: "Error 830 blocks export file generation" ❌
    - **Reality**: Error 830 is just a warning; export files ARE created ✅
    - **Exit code 0** with Error 830 means: "Processing completed, exports generated, but you have unused imports"
    - Export files `.dct`, `.frm`, `.xml`, `.aco`, `.atr`, `.eno`, `.eth`, etc. ARE generated despite 830
    - Other articles CAN successfully import despite 830 warnings

  - **The .irv file format**:
    ```
    XBOOLE_0
    O1 2 O2 2 O3 1 O4 2 O5 5 R1 3 ;
    SUBSET_1
    M1 2 ;
    NUMBERS
    O2 1 ;
    ```
    - Shows each imported article with usage counts for each symbol type
    - Missing articles = 0 usage = candidates for removal
    - Example: `build/finite_parity.irv` showed XCMPLX_0, XXREAL_0, ORDINAL1 missing → safe to remove

  - **When to use irrvoc**:
    - After successful compilation with Error 830
    - To achieve "pristine green" (zero warnings)
    - For hygiene before finalizing a module
    - **Working example**: `build/finite_parity.miz` - went from Error 830 → pristine green via irrvoc cleanup

- 203 — Unknown token / Environ/vocabulary mismatch
  - A: `environ vocabularies XBOOLE_0, SUBSET_1; notations XBOOLE_0;` (uses SUBSET_1 symbols later)
  - B: Add matching `notations SUBSET_1; constructors SUBSET_1; registrations SUBSET_1;`
  - **Environment limitation (bracket notation):**
    - A: `F.[a,b]` bracket notation even with `definitions MARGREL1;`
      - See `theories/00_curriculum/text/lesson30_rel_symm_bracket_A.miz` (NEGATIVE)
    - B: Use simpler notation like `[a,b] in R` instead of function application
      - See `theories/00_curriculum/text/lesson30_rel_univ_sym_ok.miz` (POSITIVE)

- 210/223 — Unknown or unsupported environ directive
  - A: `articles XBOOLE_0;` in `environ` (not a standard directive)
    - See `error_tests/text/e223_unknown_directive_A.miz`
  - B: Use standard directives e.g. `theorems XBOOLE_0;`
    - See `error_tests/text/e223_unknown_directive_B.miz`

## Vocabulary / Category

- 140, 142, 148, 152 — Unknown symbol/category (attr/mode/functor/selector)
  - A: Use `X is trivial` without declaring `Vtrivial` in `.voc`
  - B: In `dict/file.voc`: `Vtrivial`; in article define `attr X is trivial means X = {};`

- 892 — MML identifier should be at most eight characters long
  - A: `vocabularies THIS_IS_TOO_LONG, XBOOLE_0;`
    - See `error_tests/text/e892_vocab_length_A.miz`
  - B: Avoid local vocab names or keep ≤ 8 chars (and ensure the `.voc` exists if used)
    - See `error_tests/text/e892_vocab_length_B.miz`

## Correctness

- 73 — Correctness condition missing (functor)
  - A:
    ```mizar
    definition let X be set; func double X -> set equals X \/ X; end;
    ```
  - B: Add `coherence;` for `equals` definitions
    ```mizar
    definition let X be set; func double X -> set equals X \/ X; coherence; end;
    ```
  - **B (for conditional Boolean functions with `if...otherwise`)**: Use `correctness;` NOT `coherence;`
    ```mizar
    definition
      let x, y be object;
      func IsEqual(x, y) -> Element of BOOLEAN equals
      TRUE if x = y otherwise FALSE;
      correctness;  :: NOT coherence!
    end;
    ```
  - **Critical Rule**:
    - `coherence;` for `equals` with explicit values
    - `correctness;` for `if...otherwise` conditionals
    - `correctness;` for `means` definitions
  - Curriculum refs:
    - Positive: `theories/00_curriculum/text/lesson2b_coherence.miz` (equals → coherence)
    - Positive: `theories/00_curriculum/text/lesson18.miz` (if...otherwise → correctness)
    - **Working example**: `build/chain_lesson18.miz` (verified 0 errors)

- 72 — Correctness cannot be established (too implicit)
  - A: Overly implicit constructor typing; missing visible target type
  - B: State the result type explicitly and/or add `coherence proof ... end;`
  - Curriculum refs:
    - See also `theories/00_curriculum/text/lesson20_functor_props.miz` for theorem‑based equalities that avoid fragile indices

## Kind Expected (Parser/Analyzer)

- 301/302/303/304/306/321 — Predicate/Functor/Mode/Structure/Attribute expected
  - A: Wrong kind in header, e.g.,
    ```mizar
    definition let X be set; pred Double X means X = X \/ X; end;  :: 301/302/306/321
    ```
  - B: Use correct kind and placement:
    ```mizar
    definition let X be set; func double X -> set equals X \/ X; coherence; end;
    ```
  - **Environment limitation (complex function types):**
    - A: `Function of [:X,X:], BOOLEAN` type fails to parse even with full imports
      - See `theories/00_curriculum/text/lesson30_tuples_symmetric_A.miz` (NEGATIVE)
      - Tried: definitions FUNCT_2/MARGREL1, registrations SUBSET_1/FUNCT_2, using object instead of Element
      - All attempts failed with Error 306 "Attribute symbol expected"
    - B: Use simpler types like `set`, `object`, or `Relation of X`
      - See `theories/00_curriculum/text/lesson30_rel_univ_sym_ok.miz` (POSITIVE)
      - Lesson: Not all type constructors work in all environments; when 306 persists, simplify types
  - Curriculum refs:
    - Positive: `theories/00_curriculum/text/lesson21_op_props_ok.miz` (equals + label + coherence)

## Dots, Functions, Schemes

- 103 — Unknown functor (dot usage without visible types)
  - A:
    ```mizar
    definition let X be set, f be Function of X, BOOLEAN;
      func Flip(f) -> Function of X, BOOLEAN means for x holds it.x = 'not'(f.x);
    end;  :: 103 (x not typed)
    ```
  - B:
    ```mizar
    definition let X be non empty set, f be Function of X, BOOLEAN;
      func Flip(f) -> Function of X, BOOLEAN means
      for x being Element of X holds it.x = 'not'(f.x);
      existence
      proof deffunc F(Element of X) = 'not'(f.$1);
        consider h being Function of X, BOOLEAN such that
        A1: for x being Element of X holds h.x = F(x) from FUNCT_2:sch 4;
        take h; thus thesis by A1; end;
      uniqueness by FUNCT_2:def 8;

- 103 — Unknown functor (arithmetic operations: mod, div, +, -, *, /)
  - **Root Cause**: Using arithmetic operators like `mod`, `div` without **requirements ARITHM** and **REAL**
  - **Symptom**: `n mod 2` or `k div 3` causes Error 103 even with INT_1/NAT_D in environment
  - **A (missing ARITHM requirement)**:
    ```mizar
    environ
    vocabularies YOURMOD, NUMBERS, NAT_1, INT_1, ORDINAL1;
    notations ORDINAL1, INT_1, NAT_1;
    constructors INT_1, NAT_D;
    registrations INT_1, NAT_1;
    requirements SUBSET, BOOLE, NUMERALS;  :: Missing ARITHM!
    theorems INT_1, NAT_D;

    begin
    reserve n for Nat;
    definition
      attr n is even means n mod 2 = 0;  :: Error 103!
    end;
    ```
  - **B (complete arithmetic setup)**:
    ```mizar
    environ
    vocabularies YOURMOD, NUMBERS, NAT_1, INT_1, XXREAL_0, ORDINAL1;
    notations NUMBERS, INT_1, NAT_1;
    constructors XXREAL_0, INT_1, NAT_1, NAT_D;
    registrations INT_1, NAT_1;
    requirements REAL, NUMERALS, SUBSET, BOOLE, ARITHM;  :: ARITHM + REAL!
    theorems INT_1, NAT_D;

    begin
    reserve n for Nat;
    definition
      let n be Nat;
      func parity(n) -> Element of BOOLEAN equals
        TRUE if n mod 2 = 1 otherwise FALSE;  :: Works perfectly!
      coherence;
    end;
    ```

  - **Key Fix Components** (verified 2025-10-21):
    1. `requirements ARITHM, REAL;` — **THE CRITICAL FIX** for activating arithmetic operators
    2. `INT_1` in vocabularies, notations, constructors, registrations, theorems
    3. `NAT_1` in vocabularies, notations, constructors, registrations
    4. `NAT_D` in constructors, theorems (for Nat-specific div/mod)
    5. `XXREAL_0` in vocabularies, constructors (for numeric types)

  - **CORRECTED: XCMPLX_0 is NOT needed!**:
    - **Old myth**: "XCMPLX_0 in notations required for mod (triggers Error 830 but necessary)"
    - **Reality**: XCMPLX_0 is **NOT** needed for `mod` operator! It was cargo-culted from examples
    - **Proof**: `build/finite_parity.miz` compiles pristine green WITHOUT XCMPLX_0/XXREAL_0/ORDINAL1 in notations
    - Use `irrvoc` to identify and remove such unused imports

  - **Why ARITHM is mandatory**:
    - Without ARITHM, operators like `mod` exist in vocabulary but aren't properly typed/constructed
    - Parser recognizes the symbol but Analyzer can't type-check arithmetic terms
    - REAL requirement works with ARITHM to enable numeric literal evaluation

  - **Error 830 is acceptable here**:
    - XCMPLX_0 triggers "Nothing imported from notations" warning
    - But XCMPLX_0 is required for `mod` typing to work
    - Export files ARE generated despite the warning
    - This is a known pattern in MML articles using mod (e.g., fib_fusc.miz, abian.miz)

  - **Reference**: See HOWTO_Mizar.md section 5a for complete arithmetic setup pattern
  - **Working example**: `theories/02_parity/text/fparity.miz` — defines parity with `n mod 2`

- 103 — Unknown functor (function application - typed dot pattern)
  - **A (incomplete environment - Error 103 on `f.x`)**:
    ```mizar
    environ
    vocabularies FUNCT_1, FUNCT_2, ...;
    notations FUNCT_2;           :: MISSING FUNCT_1!
    constructors FUNCT_2;        :: MISSING FUNCT_1!
    registrations FUNCT_2;       :: MISSING FUNCT_1!
    theorems FUNCT_2;            :: MISSING FUNCT_1!
    begin
    let f be Function of X, Y;
    let x be Element of X;
    ... f.x ...  :: Error 103: Unknown functor
    ```
  - **B (complete environment - WORKS)**:
    ```mizar
    environ
    vocabularies FUNCT_1, FUNCT_2, ...;
    notations FUNCT_1, FUNCT_2;       :: FUNCT_1 added!
    constructors FUNCT_1, FUNCT_2;    :: FUNCT_1 added!
    registrations FUNCT_1, FUNCT_2;   :: FUNCT_1 added!
    theorems FUNCT_1, FUNCT_2;        :: FUNCT_1 added!
    begin
    let f be Function of X, Y;
    let x be Element of X;
    ... f.x ...  :: Works!
    ```
  - **Key insight**: FUNCT_1 must be in **ALL** environment sections (notations, constructors, registrations, theorems), not just vocabularies, for dot notation to work
  - **Discovered**: 2025-10-21 during M3 Step 1 (chain_dot_m3_s1s2s3.miz)
  - **Positive example**: `theories/03_chain_dot/text/chain_dot_m3_s1s2s3.miz` (lines 8-20)
  - Curriculum refs:
    - See How‑To "Function application and pairs" (typed dot + FUNCT_2:sch 4) and reuse that pattern

- 191 — Scheme/constructor dependencies
  - A: Use `from FUNCT_2:sch 4` without `FUNCT_2` present in env
  - B: Add `notations/constructors/registrations FUNCT_2;`

## Labels / Proof Flow

- 4 — This inference is not accepted
  - A:
    ```mizar
    assume X is empty; hence X = {};
    ```
  - B:
    ```mizar
    assume X is empty; then X = {} by XBOOLE_0:def 1; hence thesis;
    ```
  - Curriculum refs:
    - Positive: `theories/00_curriculum/text/lesson20_functor_props.miz` (explicit elementwise steps + TARSKI:2)

- 55 — Invalid generalization; 100 — Unused locus; 144 — Unknown label
  - A: Refer to nonexistent label or generalize bound variables
  - B: Introduce with `let/assume`, label as `A1: ...`, and reuse `by A1`
  - Curriculum refs:
    - 100 Negative: `theories/00_curriculum/text/lesson24_reserve_vs_let_A.miz`
    - 100 Positive: `theories/00_curriculum/text/lesson24_reserve_vs_let_ok.miz`
    - 144 See error_tests `e144_unknown_label_{A,B}.miz`

## Attributes / Structures

- 106/115 — Unknown attribute (or not imported)
  - A: `cluster non void for MultiGraphStruct;` without GRAPH_1/STRUCT_0
  - B: Add `STRUCT_0, GRAPH_1` to env or use known attrs like `non empty`.
  - **Environment limitation (library attributes not accessible):**
    - A: Using `R is symmetric` with full RELAT_2 imports still fails with Error 106
      - See `theories/00_curriculum/text/lesson30_rel_symm_bracket_A.miz` (NEGATIVE)
      - Even with `definitions RELAT_2; theorems RELAT_2;` the attribute is not accessible
    - B: Define your own attribute or use simpler predicates
      - Lesson: Even standard MML attributes may not be accessible in minimal environments
  - Curriculum refs:
    - See How‑To "GRAPH_1: tiny integration example" for a minimal attribute demo

- Aggregate literal issues (302/304; sometimes 330 in complex cases)
  - A: Misuse `(# ... #)` outside proper struct context; see `error_tests/text/e330_bad_aggregate_A.miz`
  - B: Define structures normally, or construct values only where well-typed; see `error_tests/text/e330_bad_aggregate_B.miz`
  - Curriculum refs:
    - See How‑To “Structures & selectors” for a minimal, well‑typed struct pattern

- 183 — Relation constructor typing
  - A: `set R = {} the Relation of E, V;` without `RELAT_1, ZFMISC_1`
  - B: Add `RELAT_1, ZFMISC_1` in env and ensure `E, V` are sets.
  - Curriculum refs:
    - See How‑To set‑builder and tuple examples for required imports

- 175 — Unknown attribute format
  - A: Using predicate syntax with an attribute cue, e.g., `pred F is_symmetric_on X means ...` (mixes `pred` with `is`)
  - B: Either use a true attribute: `attr F is symmetric means ...` or a predicate without `is`: `pred Symmetric(F, X) means ...`
  - Curriculum refs:
    - See `theories_second_draft/00_curriculum_proposals/text/lesson30_tuples_symmetric.miz` (predicate form works)

- 830 — Nothing imported from notations
  - A: `notations SUBSET_1;` present but no visible use on the page
  - B: Remove the `notations` line, or actually use it (e.g., `Element of X`) and add `constructors SUBSET_1;` if needed
  - Curriculum refs:
    - See `theories_second_draft/00_curriculum_proposals/text/lesson32_reconsider_coercion.miz` (fix by making `Element of` visible)

## Misc (seen in curriculum)

- 51 — Redundant steps; too implicit equality usage
  - A: Abbreviated steps in complex proofs
  - B: Expand intermediate equalities with `then/hence`.

- 136/165/174/175/190/214/215/223/253/396 — Advanced analyzer/normalizer notes
  - Typical causes: hidden types, unused or misordered quantifiers, missing `requirements SUBSET, BOOLE`, case splits without premises, or proof fragments left unused.
  - Fix: Make types visible (`Element of ...`), add `requirements` only as needed, use `per cases`, remove unused quantifiers, and split proofs into labeled steps.
  - Curriculum refs:
    - 223: see error_tests `e223_unknown_directive_{A,B}.miz`
    - 136: `theories/00_curriculum/text/lesson30_tuples_symmetric.miz` (proposal) shows missing registrations when SUBSET/registrations are absent

## Environment Limitations (Lesson 30 discoveries)

Sometimes code that "should work" according to canonical Mizar docs doesn't compile in minimal environments. These are fundamental parser/environment limitations, not user errors:

- **Complex function types** (`Function of [:X,X:], BOOLEAN`):
  - Error 306 persists even with correct imports (FUNCT_2, MARGREL1, SUBSET_1, ZFMISC_1)
  - Tried: definitions, registrations, theorems — all failed
  - Solution: Use simpler types (`set`, `object`, `Relation of X`)
  - Example: `theories/00_curriculum/text/lesson30_tuples_symmetric_A.miz` (negative)

- **Bracket notation** (`F.[a,b]`):
  - Error 203 "Unknown token" even with definitions MARGREL1
  - This notation is standard in MML but environment-dependent
  - Solution: Use simpler notation like `[a,b] in R` for relations
  - Example: `theories/00_curriculum/text/lesson30_rel_symm_bracket_A.miz` (negative)

- **Library attributes not accessible** (e.g., `symmetric` from RELAT_2):
  - Error 106 even with full imports (definitions/theorems RELAT_2)
  - Standard MML attributes may not be accessible in minimal setups
  - Solution: Define custom attributes or use predicates instead
  - Example: See negative examples above

- **Source pollution** (`::>` error annotations):
  - Mizar writes error annotations back into `.miz` files
  - These annotations can cause cascading parse errors
  - Solution: Strip with `sed -i '/^::>/d' file.miz` before re-compiling
  - Prevention: Keep clean backup copies of source files

**Key lesson**: When canonical patterns fail despite correct syntax, the environment may have fundamental limitations. Simplify types and notation rather than fighting the parser.

## CLI/path gotchas (compact)

- Always compile from module root: `mizf text/your_file.miz` (keeps `dict/` visible).
- `MIZFILES` is set to `/home/zar/claude/mizar/share` here; no need to change it.
- Error lines appear as `::> *code` inside `.miz`; re-run `mizf` after fixes — annotations self-clean (but may pollute source; see "Source pollution" above).

This file covers the codes actually observed under `theories/00_infrastructure/text/*.err`. For anything beyond this list, prefer compile‑driven diagnosis: make types visible, add only the required env, and minimize steps.

---

## Quick fixes table (merged)

Common error codes with causes and fast cures used in this repo.

| Code | Message (short)                           | Why it occurs (here)                                    | Fix (copy‑paste ready) |
|------|-------------------------------------------|---------------------------------------------------------|------------------------|
| 4    | Inference not accepted                    | Step too implicit; automation boundary                  | Add explicit step or intermediate lemma |
| 55   | Invalid generalization                     | Quantifier/type order issue                             | Keep types visible; re‑order `let`/quantifiers |
| 72   | Unexpected correctness condition           | Used `correctness` where `coherence` is expected        | For `equals` functors use `coherence;` |
| 73   | Correctness/coherence missing              | Forgot end‑condition in definition                      | Add `coherence;` (equals) or `correctness` (means/modes) |
| 100  | Unused/ill‑typed locus                     | Wrong/missing type                                      | Add proper `let … be Type;` / adjust type |
| 103  | Unknown functor (often at `f.x`)           | Hidden function type at dot                             | Use typed quantification; make type visible; or `reconsider` |
| 140  | Unknown variable                           | Param not declared                                      | Declare with `let … be …;` |
| 142  | Unknown locus                              | Missing typed binder                                    | Use `for x being Element of X holds …` |
| 191  | Scheme/Theory deps                         | Missing scheme import                                   | Add needed `schemes …;` (e.g., `FUNCT_2`) |
| 203  | Unknown token                              | Bad symbol / missing `.voc` / naming style clash        | Fix symbol; add to `.voc`; follow project naming |
| 216  | Unexpected end                             | Trailing `end.`                                         | Remove `end.`; file ends with last `end;` |
| 301  | Predicate symbol expected                  | `.voc` missing predicate                                | Add `Ryour_symbol` to your vocabulary |
| 302  | Functor symbol expected                    | Bad label placement **or** broken env/vocab             | Put label on its own line; verify `.voc` and `MIZFILES` |
| 303  | Mode symbol expected                       | Bad mode name / missing vocab                           | Add to `.voc` (`M…`) and import vocabulary |
| 306  | Proof step issue                           | Needs more justification                                | Add intermediate steps / cite theorems |
| 321  | Category mismatch                          | Vocab qualifier wrong                                   | Fix `.voc` line (R/O/M/V…) |
| 801  | Vocabulary not found                       | Running from wrong dir; `dict/` not visible             | Run from module root, reference `text/…` path |
| 815  | Vocabulary symbol repeated                 | Duplicates across `environ`                             | Remove duplicate `vocabularies` entries |
| 892  | Identifier too long                        | Over‑long vocabulary name                               | Keep vocab names ≤ 8 chars |
