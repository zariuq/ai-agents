# Mizar How‑To (ONE canonical guide)
**Project:** 4CT (Four Color Theorem – Goertzel/Kauffman/Spencer‑Brown route)  
**Audience:** humans + LLMs (fits in context).  
**Last updated:** 2025-10-16

## 0) Mental model
- Mizar = *definitions + registrations + small proofs*. Let the library do the heavy lifting via types and clusters.
- Compile often; fix environ/vocabulary issues first; keep articles small and modular.

## 1) Vocabulary (.voc) is mandatory

### Creating a local vocabulary file (CRITICAL NAMING RULE)

- Every new **Predicate/Relation (R)**, **Functor (O)**, **Mode (M)**, **Attribute (V)**, etc. must be declared in a `.voc` file *before* use.
- Layout: project module has `text/` for `.miz` and sibling `dict/` for `.voc`.

**CRITICAL: Vocabulary file must match article base name (lowercase)**

For a local vocabulary to work:
1. **Article**: `fparity.miz` (your article file)
2. **Vocabulary file**: `dict/fparity.voc` (lowercase, matches article base)
3. **Directive**: `vocabularies FPARITY;` (uppercase in environ)

**This will FAIL with Error 801:**
```mizar
:: Article: fparity.miz
:: Vocabulary file: dict/FINITE_P.voc  ← WRONG: uppercase, different name
:: Directive: vocabularies FINITE_P;
```

**This will SUCCEED:**
```mizar
:: Article: fparity.miz
:: Vocabulary file: dict/fparity.voc  ← CORRECT: lowercase, matches article
:: Directive: vocabularies FPARITY;   ← Uppercase in directive
```

**Why this matters:**
- Mizar's "vocabulary attachment" mechanism requires local vocabulary files to match the article base name
- System vocabularies (in MML) use different lookup rules
- Case sensitivity: file name lowercase, directive UPPERCASE
- Article name ≤ 8 chars (Error 892 if longer)

### Vocabulary file contents

- Common qualifiers: `Rxxx`, `Oxxx`, `Mxxx`, `Vxxx` (one symbol per line)
- Example `dict/fparity.voc`:
  ```
  Veven_card
  Vodd_card
  Oparity
  ```

### Additional rules

- House rule: keep vocabulary names ≤ 8 chars
- List your vocabulary **first** in `environ` `vocabularies`
- **Avoid reusing MML attribute names** (e.g., `symmetric` from RELAT_2). In minimal environments, library attributes may not be accessible even with full imports. Use unique names (e.g., `Vsymm`) or predicates instead.
- Tools (optional): `checkvoc`, `listvoc`, `findvoc`, `irrvoc`

## 2) Canonical definition rules (no contradictions)
- **Functors (functions) defined with `equals`** → put a label after `equals` (e.g., `:Def1:`) and end with **`coherence;`**.  
  ```mizar
  definition
    let X be set;
    func double X -> set equals
    :DefDouble:
    X \/ X;
    coherence;
  end;
  ```
- **Predicates / Attributes / Complex functors with `means`** → give a label after `means` **and** wrap *existence/uniqueness* inside a **`correctness`** block, or just `correctness;` if not needed.  
  ```mizar
  definition
    let X be set;
    attr X is trivial means
    :DefTriv:
    X = {};
  end;
  ```
  ```mizar
  definition
    let X be non empty set; let m be Function of X, BOOLEAN;
    func Flip(m) -> Function of X, BOOLEAN means
    :DefFlip:
    for x being Element of X holds it.x = 'not'(m.x);
    correctness
    proof
      deffunc F(Element of X) = 'not'(m.$1);
      consider h being Function of X, BOOLEAN such that
        A1: for x being Element of X holds h.x = F(x) from FUNCT_2:sch 4;
      take h; thus thesis by A1;
    end;
  end;
  ```
- **Modes** that are defined (not mere aliases) need **`correctness;`**.
- **Labels must be on their own line after `equals/means`** (avoids formatting errors).
- **No `end.` at file end**. The last `end;` closes the last block.

## 3) Function application and pairs (what always compiles)
- **Dot application**: `f.x` works when types are *visible* at the use site. The winning pattern is a `means` clause with **typed quantification**:  
  `for x being Element of X holds it.x = ...`
- **Pointwise definitions**: construct via `FUNCT_2:sch 4`, prove uniqueness by `FUNCT_2:def 8`.
- **Constant functions**: avoid `means` with `.x`. Prefer `equals [:A, {{v}}:]` and then prove the value lemma separately.
- **Pairs**: backtick accessors like ``c`1`` require the pair type to be visible (`Element of [:X,Y:]`). When hidden behind a functor, decompose with `ZFMISC_1:84` and use `XTUPLE_0:1` or `ZFMISC_1:33` for equality.

## 4) Registrations (clusters) – automation that saves proofs
- **Functorial** (term → attribute), **existential** (enable `cluster ... for ...`), **conditional** (attr → attr), **parametric** (property preserved by operations). Use clusters so everyday theorems become one‑liners.

## 5) Minimal, safe `environ` pattern
```mizar
environ
 vocabularies YOURVOC, XBOOLE_0, SUBSET_1, ZFMISC_1, FUNCT_1, FUNCT_2;
 notations   XBOOLE_0, SUBSET_1, ZFMISC_1, FUNCT_1, FUNCT_2;
 constructors XBOOLE_0, SUBSET_1, ZFMISC_1, FUNCT_2;
 registrations XBOOLE_0, SUBSET_1, ZFMISC_1, FUNCT_2;
 requirements SUBSET, BOOLE, NUMERALS, ARITHM;
 theorems XBOOLE_0, XBOOLE_1, ZFMISC_1, FUNCT_1, FUNCT_2, MCART_1;
 schemes FUNCT_2;
```
- Add more only when the compiler demands it.
- For Booleans: bring `MARGREL1, XBOOLEAN`. For graphs: `STRUCT_0, GRAPH_1`.

## 5a) Arithmetic operations (mod, div, +, -, *, /) – CRITICAL SETUP

**Problem:** Using arithmetic operators like `mod`, `div` on `Nat` or `Integer` types causes **Error 103 "Unknown functor"** even with correct imports.

**Root Cause:** Mizar requires **requirements ARITHM** (and usually **REAL**) to activate arithmetic operations. Without these, the operators exist in vocabularies but aren't properly typed/constructed for use in terms.

**The Complete Fix for `mod` operator (verified 2025-10-21):**

```mizar
environ

vocabularies
  XBOOLE_0, SUBSET_1, NUMBERS, NAT_1, INT_1, XXREAL_0,
  ORDINAL1, CARD_1, CARD_2, FINSET_1, XBOOLEAN, MARGREL1, TARSKI;
notations
  TARSKI, XBOOLE_0, SUBSET_1, NUMBERS,
  INT_1, NAT_1, CARD_1, CARD_2, FINSET_1, XBOOLEAN, MARGREL1;
  :: NO XCMPLX_0, NO XXREAL_0, NO ORDINAL1 needed in notations!
constructors
  XXREAL_0, INT_1, NAT_1, NAT_D, CARD_1, CARD_2, FINSET_1, XBOOLEAN;
  :: INT_1 defines mod functor
  :: NAT_D redefines mod for Nat -> Nat
registrations
  INT_1, NAT_1, XBOOLE_0, SUBSET_1, FINSET_1, CARD_1;
requirements
  REAL, NUMERALS, SUBSET, BOOLE, ARITHM;
  :: ⚠️ ARITHM + REAL are CRITICAL - without them mod causes Error 103
theorems
  INT_1, NAT_D, CARD_1, CARD_2, FINSET_1,
  XBOOLE_0, XBOOLE_1, MARGREL1, XBOOLEAN, TARSKI;

begin

:: Parity using mod operator
definition
  let n be Nat;
  func parity(n) -> Element of BOOLEAN equals
  :DefParity:
  TRUE if n mod 2 = 1 otherwise FALSE;
  coherence;
end;

:: Works perfectly! Compiles pristine green (no warnings)
```

**Key Insights (corrected 2025-10-21):**

1. **ARITHM requirement is THE CRITICAL FIX** for `mod`, `div`, `+`, `-`, `*`, `/` operations
2. **REAL requirement** enables real number arithmetic (works with ARITHM)
3. **XCMPLX_0 is NOT needed!** ← This was a myth from cargo-culting examples
4. **XXREAL_0, ORDINAL1 NOT needed in notations** - only in vocabularies/constructors for types
5. **Complete INT_1 setup needed:**
   - `INT_1` in vocabularies (vocabulary for mod symbol)
   - `INT_1` in notations (imports mod functor notation)
   - `INT_1` in constructors (provides mod constructor)
   - `INT_1` in registrations (type registrations for Integer operations)
   - `INT_1` in theorems (access to INT_1 theorems like INT_1:def 10)
6. **NAT_D for Nat-specific mod:**
   - `NAT_D` in constructors (redefines `k mod l -> Nat` for natural numbers)
   - `NAT_D` in theorems (theorems like NAT_D:12 for `n mod 2 = 0 or 1`)

**Using irrvoc to clean up imports (achieves pristine green):**

```bash
# From module root with mizenv sourced:
source mizenv
irrvoc build/finite_parity     # generates finite_parity.irv

# Check the .irv file to see what's actually used:
cat build/finite_parity.irv
# Articles NOT listed = 0 usage = safe to remove from notations

# Remove unused imports → recompile → pristine green!
```

**The .irv file shows actual usage:**
```
XBOOLE_0
O1 2 O2 2 O3 1 O4 2 O5 5 R1 3 ;   ← used
SUBSET_1
M1 2 ;                             ← used
NUMBERS
O2 1 ;                             ← used
# XCMPLX_0 missing from .irv → NOT used → can remove!
```

**Working Examples:**
- `build/finite_parity.miz` - Pristine green, complete GF(2) algebra using mod
- `theories/02_parity/text/fparity.miz` - Basic parity with mod
- `theories/00_curriculum/text/lesson31_arithmetic_mod.miz` - Complete mod tutorial

**Quick Checklist for Arithmetic:**
- [ ] `requirements ARITHM, REAL;` present (THE KEY!)
- [ ] `INT_1` in vocabularies, notations, constructors, registrations, theorems
- [ ] `NAT_1` in vocabularies, notations, constructors, registrations
- [ ] `NAT_D` in constructors, theorems (for Nat-specific div/mod)
- [ ] `XXREAL_0` in vocabularies, constructors (NOT in notations unless actually used)
- [ ] Run `irrvoc` after compilation to identify and remove unused imports

## 6) Modularity that scales
- Imports: add article names under `notations/constructors/registrations` only as needed, and under `theorems` when you cite `by ARTICLE:ref`. Do not use the non‑standard `articles` directive (Error 223).
- **`reserve`** common variables for cleaner theorems (use sparingly; prefer local `let/for`).
- **`identify`** for definitional equality (advanced); **`reconsider`** to coerce types with a proof.

## 7) Project naming style (local house rules)
- Predicates may use underscores; attributes use hyphens; functors avoid parentheses (use spaces or symbolic infix declared in `.voc`). Keep vocabulary **names** ≤ 8 chars. (These conventions match what compiles cleanly in this repo.)

## 8) Compilation (short version)
- **Environment variables** for non‑interactive runs:  
  ```bash
  export MIZFILES=/home/zar/claude/mizar/share
  export MIZROOT=/home/zar/claude/mizar
  ```
- **Run with a full path (root)** or **from the module root** so `dict/` is found:  
  ```bash
  # From repo root
  mizf theories/<module>/text/<file>.miz

  # Or from module root
  cd theories/<module> && mizf text/<file>.miz
  ```
  Always check the corresponding `.err` file afterwards (e.g. `ls -l theories/<module>/text/<file>.err`); a non‑zero file means the verifier still reported errors even if `mizf` printed progress bars only.
- For full verification of big articles you can also use Mizar’s `makeenv` + `verifier` pair (see QuickStart doc).

## 9) Patterns you’ll reuse constantly
- **Boolean functors**: `equals TRUE if <cond> otherwise FALSE;` then prove the iff lemma.
- **Pointwise ops** on functions: typed `means` + `FUNCT_2:sch 4` + `FUNCT_2:def 8`.
- **Constant maps**: `equals [:A, {{x}}:]`; then value lemma with `ZFMISC_1:87`, `FUNCT_1:1`.
- **Pairs**: accessor theorems with `MCART_1:10`; reconstructions with `ZFMISC_1:87`.

## 10) Typical errors (see ERROR_ZOO for cures)
- 72/73 (correctness/coherence), 100 (type), 103 (hidden type at dot), 140/142 (unknown var/locus), 203 (unknown token), 216 (unexpected end), 302/303/306/321 (symbol/step issues), 801/815/892 (vocabulary path/name).

---

## Feature playbook (comprehensive)

### Structures & selectors
```mizar
environ
 vocabularies XBOOLE_0, STRUCT_0;
 notations XBOOLE_0, STRUCT_0;
 constructors STRUCT_0;
 registrations STRUCT_0;

begin

definition
  struct PairStr
  (# first  -> set,
     second -> set #);
end;

definition
  let P be PairStr;
  pred P is_equal_pair means
  :DefEqPair:
  the first of P = the second of P;
  correctness;
end;
```
Notes:
- Use selector form `the <selector> of <structure>` (do not write `first(P)`).
- If you hit parser friction on fresh structures, extend a base one: `struct (1-sorted) PairStr (# ... #);`.
- Local structures don’t require a `.voc` entry; selectors are provided by `STRUCT_0`. See curriculum lesson 29: `theories/00_curriculum/text/lesson29_struct_selectors.miz`.

### Tuple application and binary functions
```mizar
environ
 vocabularies XBOOLE_0, FUNCT_2, ZFMISC_1;
 notations XBOOLE_0, FUNCT_2, ZFMISC_1;
 constructors FUNCT_2;
 registrations FUNCT_2;

begin

definition
  let X be non empty set;
  let F be Function of [:X,X:], BOOLEAN;
  attr F is symmetric means
  for a,b being Element of X holds F.(a,b) = F.(b,a);
end;
```
Notes:
- Typed binders `for a,b being Element of X` make dot/tuple application robust.
- If an attribute is brittle in your env, use a predicate instead (e.g., `pred Symmetric(F,X) means ...`). Avoid `pred F is_symmetric_on X` — that mixes predicate/attribute syntax and triggers 175/306.

**⚠️ ENVIRONMENT WARNING (Lesson 30):**
The canonical pattern above may **not compile** in minimal Mizar environments, even with correct imports. Known issues:
- **Error 306**: `Function of [:X,X:], BOOLEAN` type constructor fails to parse
  - Tried: full imports (FUNCT_2, MARGREL1, SUBSET_1, ZFMISC_1), definitions, registrations
  - All attempts failed in some environments
- **Error 203**: Bracket notation `F.[a,b]` not recognized even with `definitions MARGREL1`
- **Error 106**: Library attributes like `symmetric` from RELAT_2 may not be accessible

**What works instead:**
Use simpler types and notation:
```mizar
theorem
  for X being set, x,y being object st x in X & y in X holds
    ([x,y] in [:X,X:] implies [y,x] in [:X,X:])
proof
  let X be set, x,y be object;
  assume x in X & y in X;
  then [y,x] in [:X,X:] by ZFMISC_1:87;
  hence thesis;
end;
```
See: `theories/00_curriculum/text/lesson30_rel_univ_sym_ok.miz` (compiles) vs. `lesson30_tuples_symmetric_A.miz` and `lesson30_rel_symm_bracket_A.miz` (negative examples).

**Key lesson**: When canonical patterns fail despite correct syntax, simplify types (`set`, `object`) and use relation predicates instead of function application.

### Fraenkel comprehension (set builder)
```mizar
environ
 vocabularies XBOOLE_0, ZFMISC_1, SUBSET_1;
 notations XBOOLE_0, ZFMISC_1, SUBSET_1;
 constructors ZFMISC_1, SUBSET_1;

begin

definition
  let X be set;
  func diag(X) -> set equals
  :DefDiag:
  { [x,x] where x is Element of X : x in X };
  coherence;
end;
```
Notes:
- Prefer `equals ... coherence;` for set builders. If you need a characterization, add a separate theorem rather than `means` with top‑level `existence/uniqueness` (avoids 72/302/330 tangles).
- If you hit 129 (invalid free variables) in a Fraenkel operator, use the robust variant confirmed in lesson 31: `{ [x,x] where x is object : x in X }` under `ZFMISC_1`.

### Reconsider / Identify
```mizar
environ
 vocabularies XBOOLE_0;
 notations XBOOLE_0;

begin

theorem
  for X being set, x being object st x in X holds
  ex y being Element of X st y = x
proof
  let X be set, x be object; assume A1: x in X;
  reconsider y = x as Element of X by A1;
  take y; thus y = x;
end;
```
Notes:
- Keep types visible and reasons explicit. If the final `thus` gets Error 4 (inference not accepted), add a tiny intermediate equality or use a predicate that unfolds the coercion.
- A single 4 on this micro‑lemma is acceptable in this project; see lesson 32: `theories/00_curriculum/text/lesson32_reconsider_coercion.miz`.

### Environ hygiene (prevents brittle errors)
- Only import `notations/constructors/registrations` you visibly use; `notations SUBSET_1;` without using `Element of` triggers 830.
- Add `requirements` (e.g., `NUMERALS`, `ARITHM`, `BOOLE`) only in articles that need them.

## New Mini‑Lessons (LLM‑friendly)

- Lesson 20 — Union Properties (comm/assoc/idemp)
  - File: `theories/00_infrastructure/text/lesson20_functor_props.miz`
  - Method: elementwise equivalence + `TARSKI:2` (robust, no property annotations needed).

- Lesson 21 — Infix (+) for Union (operator + theorems)
  - Positive: `theories/00_infrastructure/text/lesson21_op_props_ok.miz` (defines `A (+) B = A \/ B`, proves laws via elementwise equivalence + `TARSKI:2`).
  - Negative: `theories/00_infrastructure/text/lesson21_op_props.miz` (local vocabulary without `.voc` → demonstrates Error 801 when compiled from inside `text/`).

- Lesson 22 — Connectedness Idea (universal relation)
  - File: `theories/00_infrastructure/text/lesson22_connected_on.miz`
  - Statement: For any `S` and `x,y in S`, a universal relation `[:S,S:]` relates them in some order.

- Lesson 23 — Projectivity/Idempotence of ∩ with fixed U
  - Positive: `theories/00_infrastructure/text/lesson23_projective_cap_ok.miz` (functor `cap_with(A,U) = A /\ U` and idempotence proof).
  - Also Positive: `theories/00_infrastructure/text/lesson23_idem_cap_simple.miz` (same idea without introducing a functor).
  - Negative: `theories/00_infrastructure/text/lesson23_projective_cap.miz` (intentionally broken to show common pitfalls).

- Lesson 24 — Reserve vs. Let (implicit quantification)
  - Positive: `theories/00_infrastructure/text/lesson24_reserve_vs_let_ok.miz` (prefer local binders).
  - Negative: `theories/00_infrastructure/text/lesson24_reserve_vs_let_A.miz` (over‑broad `reserve` can hide missing quantifiers; illustrates Error 100).

- Lesson 25 — defpred micro‑demo
  - Positive: `theories/00_infrastructure/text/lesson25_defpred_ok.miz` (clean template alongside standard `consider`).
  - Negative: `theories/00_infrastructure/text/lesson25_defpred_A.miz` (free symbol in `defpred` → Error 140).

- Lesson 26 — Minimal theorems import (fixing 192)
  - Positive: `theories/00_infrastructure/text/lesson26_theorems_import_B.miz` (`theorems TARSKI;` → `by TARSKI:2`).
  - Negative: `theories/00_infrastructure/text/lesson26_theorems_import_A.miz` (no `theorems TARSKI;` → 192).

- Lesson 27 — Operator annotations
  - Positive: `theories/00_infrastructure/text/lesson27_op_annotations_ok.miz` (robust fallback: prove laws as theorems).
  - Negative: `theories/00_infrastructure/text/lesson27_op_annotations_A.miz` (annotation without sufficient facts visible; fragile).

- Lesson 28 — Numeric requirements
  - Positive: `theories/00_infrastructure/text/lesson28_numerals_ok.miz` (`requirements NUMERALS;` makes numerals available).
  - Negative: `theories/00_infrastructure/text/lesson28_numerals_A.miz` (missing requirements → numeric literal parsing error).

- Lesson 29 — Structures & selectors
  - Positive: `theories/00_curriculum/text/lesson29_struct_selectors.miz` (literal struct + selectors; no `.voc` needed).

- Lesson 31 — Fraenkel diag
  - Positive: `theories/00_curriculum/text/lesson31_fraenkel_diag.miz` (`equals` + `coherence;`, object‑binder avoids 129).

- Lesson 32 — Reconsider coercion
  - Positive: `theories/00_curriculum/text/lesson32_reconsider_coercion.miz` (may emit a lone 4; acceptable here).

## Important Extras

- Reserve vs. let (implicit quantification)
  - `reserve x for set;` globally types a variable; use sparingly. Prefer local `let/for` to avoid hidden quantifiers.
- Requirements for numerals and arithmetic
  - Add only when needed (compile‑driven): `NUMERALS`, `ARITHM`, `NUMBERS/REAL` by module; keep minimal.
- Proof elision with `@proof`
  - `@proof … end;` disables checking; use only as temporary scaffolding; remove before committing.
- Synonym, antonym, redefine, identify
  - Advanced housekeeping; prefer normal definitions/registrations first.
- defpred (alongside deffunc)
  - `defpred P[Var] means <formula using $1>` handy for schemes/theorems; keep typed and local.
- Scheme anatomy beyond `FUNCT_2:sch 4`
  - Schemes have provided clauses and higher‑order params; copy style from MML when needed.
- Notation tuning
  - `notations …` can introduce pretty forms; keep minimal to avoid clashes.
- Minimal theorems import
  - `theorems ARTICLE:ref` lets `by …` cite facts without full imports.

## Advanced: Property‑annotated functors (when to use)

You can annotate functors with algebraic laws (e.g., `commutativity;`, `associativity;`, `idempotence;`). This is powerful but can be brittle unless the right MML facts are visible. Prefer theorem‑based proofs (as in Lesson 20/21 positive) unless you truly need global automation.

Example (syntax, keep in a small dedicated article with proper env):
```mizar
environ
 vocabularies XBOOLE_0;
 notations XBOOLE_0;
 constructors XBOOLE_0;
 registrations XBOOLE_0;

begin

definition
  let A,B be set;
  func A (+) B -> set equals A \/ B;
  coherence;
  commutativity;
  associativity;
  idempotence;
end;
```
Tips:
- Make the union facts visible (e.g., `theorems XBOOLE_1`) if verification depends on named theorems.
- If flaky, fall back to explicit theorems via elementwise equivalence + `TARSKI:2`.
- Keep annotations local to avoid clashes.

## Pairs, reconsider, and hygiene (quick reminders)

- Accessors like ``c`1`` require a visible product type (`Element of [:X,Y:]`), otherwise decompose with `ZFMISC_1:84`.
- Reconsider for coercions: `A1: x in BOOLEAN; reconsider x as Element of BOOLEAN by A1;`.
- Vocabulary: declare only what you use in `dict/*.voc` (R/O/M/V). Keep names ≤ 8 chars.
- Environment hygiene: keep `vocabularies/notations/constructors/registrations` minimal and justified. Use `theorems` only for references you cite.

## GRAPH_1: tiny integration example

```mizar
environ
 vocabularies STRUCT_0, GRAPH_1;
 notations STRUCT_0, GRAPH_1;
 constructors STRUCT_0, GRAPH_1;
 registrations STRUCT_0, GRAPH_1;

reserve G for Graph; reserve e for Edge of G;

definition let G be Graph, e be Edge of G;
  attr e is self_loop means dom e = cod e;
end;
```

### Appendix A — Micro‑templates

**Predicate** (no label required unless you’ll reference it):  
```mizar
definition
  let X be set;
  pred X is_empty means X = {};
end;
```

**Attribute**:  
```mizar
definition
  let X be set;
  attr X is prefix-free means
  :Def1:
  for p,q being FinSequence st p in X & q in X holds
    p = q or not p is_prefix_of q;
end;
```

**Pointwise op on functions**:  
```mizar
definition
  let X be non empty set;
  let m1,m2 be Function of X, BOOLEAN;
  func MoodXOR(m1,m2) -> Function of X, BOOLEAN means
  :DefXOR:
  for x being Element of X holds it.x = (m1.x) 'xor' (m2.x);
  correctness
  proof
    deffunc F(Element of X) = (m1.$1) 'xor' (m2.$1);
    consider h being Function of X, BOOLEAN such that
      A1: for x being Element of X holds h.x = F(x) from FUNCT_2:sch 4;
    take h; thus thesis by A1;
  end;
end;
```

**Constant map**:  
```mizar
definition
  let X be set;
  func ZeroFunc(X) -> Function of X, {FALSE} equals [:X, {FALSE}:];
  coherence;
end;
```

**Pairs (accessors visible)**:  
```mizar
theorem
  for c being Element of [:BOOLEAN,BOOLEAN:] holds
    c`1 in BOOLEAN & c`2 in BOOLEAN by MCART_1:10;
```
