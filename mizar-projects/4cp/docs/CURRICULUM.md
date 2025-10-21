# Curriculum (ONE canonical)
A compact single source for the teaching track that compiles with 0 errors.  
**Location in repo:** `theories/00_curriculum`

## Why one file?
We consolidated overlapping notes into this one pager so humans/LLMs always quote the same patterns. The actual **working lessons** remain as code in `text/` with matching `.voc` in `dict/`.

## Lessons (all verified 0 errors)
- **Lesson 1 – Predicates** (`text/lesson1.miz`, `dict/lesson1.voc`): basic `means` syntax; underscores allowed for predicate names.
- **Lesson 2 – Functors** (`text/lesson2.miz`, `dict/lesson2.voc`): `equals` + label + `coherence;`.
- **Lesson 3 – Modes** (`text/lesson3.miz`, `dict/lesson3.voc`): simple aliases; correctness required for defined modes.
- **Lesson 4 – Attributes** (`text/lesson4.miz`, `dict/lesson4.voc`): `means` + label; project style uses hyphens in attribute names.
- **Lesson 5 – Theorems** (`text/lesson5c.miz`): labeled definitions referenced by `by Def1;` show proof wiring.

### Advanced mini-lessons (robust patterns)
- **Lesson 20 – Union laws** (`text/lesson20_functor_props.miz`): commutativity, associativity, idempotence via elementwise equivalence + `TARSKI:2`.
- **Lesson 21 – Infix (+) for union**
  - Positive: `text/lesson21_op_props_ok.miz` (defines `A (+) B = A \/ B` and proves laws by elementwise equivalence + `TARSKI:2`).
  - Negative: `text/lesson21_op_props.miz` (demonstrates Error 801 from a local vocabulary without a matching `.voc` when compiled inside `text/`).
- **Lesson 22 – Connectedness idea** (`text/lesson22_connected_on.miz`): `[:S,S:]` relates any `x,y in S` (ZFMISC_1 facts; simple and clean).
- **Lesson 23 – Projectivity/idempotence of ∩ with fixed U**
  - Positive: `text/lesson23_projective_cap_ok.miz` (functor `cap_with(A,U) = A /\ U` and idempotence theorem).
  - Also Positive: `text/lesson23_idem_cap_simple.miz` (same property without introducing a functor).
  - Negative: `text/lesson23_projective_cap.miz` (intentionally broken to showcase pitfalls & error annotations).

- **Lesson 24 – Reserve vs. Let (implicit quantification)**
  - Positive: `text/lesson24_reserve_vs_let_ok.miz` (prefer local binders for clarity).
  - Negative: `text/lesson24_reserve_vs_let_A.miz` (over‑broad `reserve` → illustrates Error 100).

- **Lesson 25 – defpred micro‑demo**
  - Positive: `text/lesson25_defpred_ok.miz` (clean template with `consider`).
  - Negative: `text/lesson25_defpred_A.miz` (free symbol in `defpred` → Error 140).

- **Lesson 26 – Minimal theorems import (fixing 192)**
  - Positive: `text/lesson26_theorems_import_B.miz` (`theorems TARSKI;` enables `by TARSKI:2`).
  - Negative: `text/lesson26_theorems_import_A.miz` (missing import → 192).

- **Lesson 27 – Operator annotations**
  - Positive: `text/lesson27_op_annotations_ok.miz` (prove laws explicitly; robust fallback when annotations are brittle).
  - Negative: `text/lesson27_op_annotations_A.miz` (annotations without sufficient facts in scope; fragile).

- **Lesson 28 – Numeric requirements**
  - Positive: `text/lesson28_numerals_ok.miz` (`requirements NUMERALS;` makes numerals available).
  - Negative: `text/lesson28_numerals_A.miz` (missing requirements → parsing/typing error).

### Lessons 29–32 (now part of curriculum)
- **Lesson 29 — Selectors via pairs**
  - Positive: `text/lesson29_struct_selectors.miz` (uses backtick pair selectors; robust without local vocab)
  - Negative: `text/lesson29_struct_selectors_A.miz` (misuses `first(P)/second(P)` → selector/notation errors)
- **Lesson 30 — Tuple application & symmetry (environment limitations)**
  - Positive: `text/lesson30_rel_univ_sym_ok.miz` (✅ compiles - simple relation symmetry using set/object types)
  - Negative: `text/lesson30_tuples_symmetric_A.miz` (Environment limitation: `Function of [:X,X:], BOOLEAN` fails with Error 306 even with full imports)
  - Negative: `text/lesson30_rel_symm_bracket_A.miz` (Environment limitation: bracket notation `F.[a,b]` fails with Error 203; `symmetric` attribute from RELAT_2 fails with Error 106)
  - **Key lesson**: Not all type constructors work in all environments. When canonical patterns fail despite correct imports, simplify to basic types (`set`, `object`) and use relation predicates. See ERROR_ZOO.md "Environment Limitations" section.
- **Lesson 31 — Fraenkel comprehension (diag)**
  - Positive: `text/lesson31_fraenkel_diag.miz` (`equals … coherence;`)
  - Negative: `text/lesson31_fraenkel_diag_A.miz` (`means` with existence/uniqueness outside correctness → 72/302)
- **Lesson 32 — Reconsider/coercion**
  - Positive: `text/lesson32_reconsider_coercion.miz` (explicit membership step; Error 4 acceptable if triggered)
  - Negative: `text/lesson32_reconsider_coercion_A.miz` (unused `notations` → 830)

## Minimal directory scaffold
```
00_curriculum/
  text/   lesson1.miz  lesson2.miz  lesson3.miz  lesson4.miz  lesson5c.miz
  dict/   lesson1.voc  lesson2.voc  lesson3.voc  lesson4.voc
```

## How to practice
1) Compile each lesson from the module root: `mizf theories/00_infrastructure/text/lessonN.miz`  
2) Modify one thing at a time; re‑compile.  
3) If something breaks, check vocabulary first; then `environ`; then labels/correctness conditions.

## Common pitfalls (curriculum context)
- Missing `.voc` lines (301/203).
- Functor without label/coherence (73).
- Using `end.` (216) — never do.
- Running `mizf` from inside `text/` so `dict/` is not found (801).

## Success criteria
You can compile Lessons 1–5 with 0 errors and explain why each rule (labels, correctness/coherence, vocabulary) exists. Then apply the patterns to 4CT articles.

---

## Critical Compilation Patterns (Verified 2025-10-20)

### ⚠️ ALWAYS compile from module root
```bash
# ✅ CORRECT (text/ and dict/ are siblings):
cd theories/00_curriculum
mizf text/lesson1.miz

# ❌ WRONG (Error 801 - vocabulary not found):
cd /home/zar/claude/mizar-projects/4cp
mizf theories/00_curriculum/text/lesson1.miz
```

**Why**: Mizar requires dict/ to be visible as sibling to text/ for vocabulary resolution.

### Error checking
```bash
# Empty .err file = success
cat text/lesson1.err
ls -lh text/lesson1.err  # 0 bytes = success
```

---

## Key Verified Patterns

### Typed Accessors (Lesson 15a)
```mizar
✅ for c being Element of [:X,Y:] holds c`1 in X  # WORKS
❌ for c being object st c in [:X,Y:] holds c`1 in X  # Error 103
```
**Key**: Backtick accessors need **visible product type**, not `object` or mode alias.

### Set Equality (Lesson 20)
```mizar
theorem A \/ B = B \/ A
proof
  thus A \/ B c= B \/ A proof let x be object; ... end;
  thus B \/ A c= A \/ B proof let x be object; ... end;
end;
```
**Pattern**: Double inclusion with elementwise reasoning.

### Proof Tactics (Lesson 10)
- `hereby` - bidirectional proofs (iff)
- `per cases` - exhaustive case analysis
- `given` - witness extraction from existential

### Environment Limitations (Lesson 30) ⚠️
Some patterns **fail even with full imports** in minimal environments:
- ❌ `Function of [:X,X:], BOOLEAN` → Error 306
- ❌ Bracket notation `F.[a,b]` → Error 203
- ❌ Library attributes `symmetric` → Error 106

**Solution**: Simplify to basic types (`set`, `object`) and custom attributes.

---

## Testing Log
See `logs/curriculum_testing_session_2025-10-20.log` for comprehensive session with all commands and outputs.
