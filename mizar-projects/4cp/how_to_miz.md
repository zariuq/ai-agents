# How to Mizar: Complete Guide for 4CP Formalization

A comprehensive guide combining foundational Mizar knowledge with advanced patterns learned during the Four Color Theorem formalization.

## Table of Contents
1. [The #1 Thing You Must Know](#the-1-thing-you-must-know)
2. [Quick Start](#quick-start)
3. [Vocabulary Files Deep Dive](#vocabulary-files-deep-dive)
4. [Common Constructs](#common-constructs)
5. [Proof Patterns from 4CP](#proof-patterns-from-4cp)
6. [Arithmetic Automation](#arithmetic-automation)
7. [Advanced Patterns: Modularity](#advanced-patterns-modularity)
8. [Error Resolution](#error-resolution)
9. [Best Practices](#best-practices)
10. [Common Pitfalls](#common-pitfalls)
11. [Real-World Examples](#real-world-examples)

---

## The #1 Thing You Must Know

**VOCABULARY FILES ARE MANDATORY FOR ALL NEW SYMBOLS**

This single fact will save you hours of frustration. Before you can use ANY new predicate, functor, mode, or attribute name in a Mizar article, you MUST:

1. Create a `.voc` file declaring the symbol
2. Place it in a `dict/` subdirectory
3. Reference it in your article's `environ` section

Without this, you'll get cryptic errors like:
- Error 301: "Predicate symbol expected"
- Error 203: "Unknown token"
- Error 302: "Functor symbol expected"

**MML articles work because they import pre-existing vocabularies that already have symbols registered.**

**Key Lesson from 4CP**: Always create the vocabulary file (.voc) and registrations BEFORE writing complex proofs. Vocabulary registration errors (140, 142, 203, 302, 306, 321) obscure real proof issues. Setting up vocabulary first makes debugging much cleaner.

---

## Quick Start

### Minimal Working Example

**Step 1**: Create directory structure
```bash
mkdir -p text dict
```

**Step 2**: Create `dict/myarticle.voc`
```
Ris_my_predicate
Omy_functor
```

**Step 3**: Create `text/myarticle.miz`
```mizar
:: My First Mizar Article

environ
 vocabularies MYARTICLE, XBOOLE_0;
 notations XBOOLE_0;
 constructors XBOOLE_0;

begin

definition
  let X be set;
  pred X is_my_predicate means
  X = {};
end;
```

**Step 4**: Compile
```bash
mizf text/myarticle.miz
```

**Expected**: 0 errors!

---

## Vocabulary Files Deep Dive

### What Are Vocabulary Files?

Vocabulary (.voc) files are Mizar's lexicon registration system. They tell the parser which symbols exist and what category they belong to.

### Symbol Qualifiers

Each line in a .voc file starts with a qualifier letter:

| Qualifier | Symbol Type | Example | Usage in .miz |
|-----------|-------------|---------|---------------|
| `R` | Predicate | `Ris_prefix_of` | `pred p is_prefix_of q means ...` |
| `O` | Functor | `Oconcat` or `O^` | `func p ^ q equals ...` |
| `M` | Mode | `MFinSeq` | `mode FinSeq means ...` |
| `V` | Attribute | `Vprefix_free` | `attr S is prefix_free means ...` |
| `G` | Structure | `GQuantaleStr` | `struct QuantaleStr (# ... #);` |
| `U` | Selector | `Ucarrier` | `the carrier of S` |
| `K` | Left bracket | `K{` | For custom bracket notation |
| `L` | Right bracket | `L}` | For custom bracket notation |

### Vocabulary File Format

```
RsymbolName1
RsymbolName2
Osymbol
O+ 32
Mmode_name
```

**Rules**:
- One symbol per line
- Qualifier letter comes first (NO space after it)
- Symbol names can contain underscores but NOT spaces
- For functors, optional priority 0-255 (default 64): `O+ 32`
- No double colons, control characters, or special chars
- Plain text with Unix (LF) or DOS (CR LF) line endings

### Common Mistakes

❌ **WRONG**:
```
R is_prefix_of     # Space in symbol name!
is_prefix_of       # Missing qualifier!
R:is_prefix_of     # Wrong separator!
```

✅ **CORRECT**:
```
Ris_prefix_of
```

### Referencing Vocabularies in Articles

In your `.miz` file's `environ` section:

```mizar
environ
 vocabularies MYARTICLE, XBOOLE_0, FINSEQ_1;  # UPPERCASE, no extension!
```

**Order matters**: List YOUR vocabulary FIRST, then MML vocabularies.

### Tools for Managing Vocabularies

```bash
# Check vocabulary for errors
checkvoc MYARTICLE

# Find which vocabulary contains a symbol
findvoc -w 'is_prefix_of'

# List contents of vocabulary
listvoc MYARTICLE

# Remove unused vocabulary imports
irrvoc MYARTICLE
```

### Example from 4CP

```mizar
:: In dict/set_parity.voc
OSET_PARITY
Veven           :: attribute for natural numbers
Veven_card      :: attribute for finite sets
Oparity         :: functor returning BOOLEAN
```

---

## Common Constructs

### Predicates

**Vocabulary**: `Ris_subset_of`

**Definition**:
```mizar
definition
  let X, Y be set;
  pred X is_subset_of Y means
  for x being object st x in X holds x in Y;
end;
```

**Key Points**:
- Can optionally have label (`:Def1:`) after `means` if you want to reference in proofs
- Use `let` to declare parameters
- Can be unary (`pred X is_empty`) or binary (`pred X is_subset_of Y`)

### Functors

**Vocabulary**: `Oconcat` or `O^`

**Definition**:
```mizar
definition
  let p, q be FinSequence;
  func p ^ q -> FinSequence equals
  :Def1:
  p concatenated with q;
  correctness;
end;
```

**Key Points**:
- YES, need label (`:Def1:`) after `equals`
- Must specify return type (`-> FinSequence`)
- **IMPORTANT**: Use `correctness;` (not `coherence;`) for structural validation
- Can use symbols like `^`, `+`, `*` if declared in .voc

### Modes (Types)

**Vocabulary**: `Mmy_mode`

**Definition**:
```mizar
definition
  mode my_mode is set;  # Simple alias
  correctness;
end;

definition
  mode my_mode means   # With condition
  :Def1:
  ex x being object st it = {x};
  correctness;
end;
```

**Key from 4CP**: Always add `correctness;` after mode definitions (Error 73 otherwise).

### Attributes

**Vocabulary**: `Vprefix_free`

**Definition**:
```mizar
definition
  let S be set;
  attr S is prefix_free means
  :Def1:
  for p, q being FinSequence st p in S & q in S holds
    p = q or not p is_prefix_of q;
end;
```

**Key Points**:
- YES, need label after `means`
- Used to define properties of objects
- Can be used in type specifications: `for S being prefix_free set`

### Structures

**Vocabulary**: `GMyStruct`, `Ucarrier`, `Uoperation`

**Definition**:
```mizar
definition
  struct MyStruct (#
    carrier -> set,
    operation -> Function
  #);
end;
```

**Accessing fields**:
```mizar
the carrier of S
the operation of S
```

---

## Proof Patterns from 4CP

### 1. Parity Decomposition Pattern

**Use Case**: Any proof involving odd/even natural numbers.

**Pattern**: First prove the decomposition lemma, then use it:

```mizar
theorem Th_parity_decomposition:
  for n being Nat holds n is even or ex k being Nat st n = 2*k + 1
proof
  defpred P[Nat] means $1 is even or ex k being Nat st $1 = 2*k + 1;

  :: Base case
  A0: P[0]
  proof
    0 is even;
    hence thesis;
  end;

  :: Inductive step
  A1: for r being Nat st P[r] holds P[r+1]
  proof
    let r be Nat;
    assume Hr: P[r];
    per cases by Hr;
    suppose r is even;
      then consider t being Nat such that E: r = 2*t by Def_even;
      take t;
      thus r+1 = 2*t + 1 by E;
    end;
    suppose ex t being Nat st r = 2*t + 1;
      then consider t being Nat such that E: r = 2*t + 1;
      r+1 = 2*(t+1) by E;
      hence P[r+1];
    end;
  end;

  thus for n being Nat holds P[n] from NAT_1:sch 1(A0, A1);
end;
```

**Key Points**:
- Use `defpred P[Nat] means ...` for the induction predicate
- Prove base case `P[0]` separately
- Prove inductive step `P[r] => P[r+1]` separately
- Invoke scheme with `from NAT_1:sch 1(A0, A1)`
- Remember to add `schemes NAT_1;` in environ section

**Then use it**:
```mizar
theorem Th_odd_plus_odd_even:
  for m, n being Nat st not m is even & not n is even
  holds m + n is even
proof
  let m, n be Nat;
  assume Hm: not m is even;
  assume Hn: not n is even;

  :: Get odd-form witnesses using decomposition
  consider k being Nat such that Km: m = 2*k + 1
    by Hm, Th_parity_decomposition;
  consider j being Nat such that Jn: n = 2*j + 1
    by Hn, Th_parity_decomposition;

  :: Construct witness for evenness
  take k + j + 1;
  thus m + n = 2 * (k + j + 1) by Km, Jn;
end;
```

**Source**: GPT-5 Pro proof for `Th_odd_plus_odd_even` in set_parity.miz

---

### 2. Scheme Invocation Syntax

**Environment Setup**:
```mizar
environ
  schemes NAT_1;        :: needed for NAT_1:sch 1 (induction)
  requirements ARITHM;  :: arithmetic automation
```

**General Pattern**:
```mizar
proof
  defpred P[Type] means <property>;

  A0: P[base_case] proof ... end;

  A1: for x being Type st P[x] holds P[successor(x)]
  proof ... end;

  thus for x being Type holds P[x] from SCHEME_NAME(A0, A1);
end;
```

**Common Schemes**:
- `NAT_1:sch 1` - Natural number induction
- `FUNCT_2:sch 3` - Function existence by cases
- `FUNCT_2:sch 4` - Function defined by term
- `XBOOLE_0:sch 1` - Set comprehension existence
- `XBOOLE_0:sch 3` - Set comprehension uniqueness

---

### 3. Witness Construction for Existentials

**Anti-pattern**: Hoping Mizar finds the witness
```mizar
:: BAD - Mizar may not find the witness
proof
  assume m is even & n is even;
  thus m + n is even;  :: Mizar: "Where's the witness k?"
end;
```

**Pattern**: Explicitly construct with `take`
```mizar
:: GOOD - Explicit witness construction
proof
  assume m is even;
  then consider k1 being Nat such that A1: m = 2 * k1 by Def_even;
  assume n is even;
  then consider k2 being Nat such that A2: n = 2 * k2 by Def_even;

  take k1 + k2;  :: <-- Explicit witness
  thus m + n = 2 * k1 + 2 * k2 by A1, A2
             .= 2 * (k1 + k2);
end;
```

**Key**: For `ex k being Type st P[k]`, use `take witness;` before the proof.

---

## Arithmetic Automation

### Requirements ARITHM

**What it does**: The Checker automatically handles routine arithmetic equalities.

**Examples that "just work"**:
```mizar
requirements ARITHM;

:: These need no detailed justification:
thus (2*k+1) + (2*j+1) = 2*(k+j+1);
thus 2*k + 2*j = 2*(k+j);
thus m + n - m = n;
```

**What it doesn't do**:
- Inequalities (still need `by NAT_1:4`)
- Modular arithmetic (need NAT_D)
- Non-obvious algebraic manipulations

**Usage Pattern**:
```mizar
environ
  requirements SUBSET, NUMERALS, BOOLE, ARITHM;

proof
  consider k being Nat such that m = 2*k + 1;
  consider j being Nat such that n = 2*j + 1;

  :: No detailed steps needed - ARITHM handles it
  thus m + n = 2*(k + j + 1) by previous_facts;
end;
```

---

## Advanced Patterns: Modularity

### 1. The ARTICLES Directive (Importing User Files)

**Problem**: We want to reuse definitions from `face_boundary.miz` in `strong_dual.miz` without copying 200 lines of code.

**Solution**: Use the `articles` directive to import another Mizar article.

**Pattern**:
```mizar
:: In strong_dual.miz
environ
  vocabularies ..., FACEBDRY;      :: Vocabulary names
  notations ..., FACEBDRY;         :: Import notation
  constructors ..., FACEBDRY;      :: Import constructors
  registrations ..., FACEBDRY;     :: Import registrations
  theorems ..., FACEBDRY;          :: Import theorems

  articles FACEBDRY;               :: ← KEY: Import the article!

begin

:: Now we can use GF2_squared, Chain, zero_color from face_boundary.miz!
definition
  let c be Element of GF2_squared;  :: ← Already defined in FACEBDRY
  func c dot zero_color -> Element of BOOLEAN equals ...
  correctness;
end;
```

**Benefits**:
- ✅ No code duplication
- ✅ Single source of truth
- ✅ Modular proof architecture
- ✅ Like `#include` in C or `import` in Python

**Example from 4CP**: `strong_dual.miz` builds on `face_boundary.miz` (reduced from 752 to 362 lines!)

---

### 2. The RESERVE Statement (Cleaner Code)

**Problem**: Writing "for G being _Graph" in every theorem is verbose.

**Anti-pattern**:
```mizar
theorem Th1:
  for G being _Graph
  for c1, c2 being Element of GF2_squared
  holds c1 dot c2 = c2 dot c1
proof
  let G be _Graph;
  let c1, c2 be Element of GF2_squared;
  ...
end;

theorem Th2:
  for G being _Graph
  for c being Element of GF2_squared
  holds zero_color dot c = FALSE
proof
  let G be _Graph;
  let c be Element of GF2_squared;
  ...
end;
```

**Pattern with RESERVE**:
```mizar
reserve G for _Graph,
        c, c1, c2 for Element of GF2_squared,
        y, z for Chain of G;

theorem Th1:
  c1 dot c2 = c2 dot c1  :: ← G implicit!
proof
  :: No "let c1, c2 be..." needed
  ...
end;

theorem Th2:
  zero_color dot c = FALSE
proof
  :: No "let c be..." needed
  ...
end;
```

**When to use**:
- ✅ Variables used in MANY theorems (G, c, etc.)
- ✅ Verbose types (Element of GF2_squared)
- ✅ Clean, mathematical presentation

**When NOT to use**:
- ❌ One-off variables
- ❌ Complex dependent types that vary by theorem

**Note**: Still need `let` in definitions! Reserve only applies to theorems.

---

### 3. CLUSTERS (Automatic Type Inference)

**Problem**: Mizar doesn't automatically infer that `zero_chain(G)` has type `Chain of G`.

**Pattern**:
```mizar
registration
  let G be _Graph;
  cluster zero_chain(G) -> Chain of G;
  coherence by Def_zero_chain;
end;

:: Now Mizar knows:
set z = zero_chain(G);
:: Automatically: z is Chain of G (no explicit typing needed!)
```

**Use case**: When a functor always produces a specific type, register it as a cluster.

---

### 4. Other Advanced Patterns

**IDENTIFY** (Definitional Equality):
```mizar
identify zero_chain(G) with (the_Edges_of G) --> zero_color;
:: Tells Mizar: these are interchangeable
```

**RECONSIDER** (Type Coercion - used in 4CP!):
```mizar
let x be object;
assume x in zero_boundary_set(G);
then reconsider x as Chain of G by ...;
:: x now has type Chain of G
```

**DEFFUNC/DEFPRED** (Local Definitions - used in 4CP!):
```mizar
deffunc F(Nat) = 2 * $1 + 1;      :: Local function
defpred P[Nat] means $1 is even;  :: Local predicate
```

---

### Summary: Modularity Best Practices

| Pattern | Use When | Benefits |
|---------|----------|----------|
| `articles` | Building on another .miz file | Avoid duplication, modularity |
| `reserve` | Common variables across many theorems | Cleaner code, less boilerplate |
| `cluster` | Type always determinable | Automatic inference |
| `identify` | Two forms mean same thing | Interchangeable in proofs |

**Example**: See `strong_dual.miz` for `articles` and `reserve` in practice.

---

## Error Resolution

### Error 72: "Unexpected correctness condition"
### Error 73: "Correctness condition missing"

**Context**: During 4CP formalization, we fixed 66 instances of these errors. They're structural issues with Mizar's definition validation system.

**Pattern 1 - Simple equals definitions**:
```mizar
// WRONG:
definition
  func GF2_squared -> set equals [: BOOLEAN, BOOLEAN :];
  coherence;  // ← Error 72
end;

// CORRECT:
definition
  func GF2_squared -> set equals [: BOOLEAN, BOOLEAN :];
  correctness;  // ← Use correctness, not coherence
end;
```

**Pattern 2 - Equals with proofs**:
```mizar
// WRONG:
definition
  func c1 (+) c2 -> Element of GF2_squared equals
  [c1`1 'xor' c2`1, c1`2 'xor' c2`2];
  coherence  // ← Error 72
  proof
    ...
  end;
end;

// CORRECT:
definition
  func c1 (+) c2 -> Element of GF2_squared equals
  [c1`1 'xor' c2`1, c1`2 'xor' c2`2];
  correctness  // ← Use correctness
  proof
    ...
  end;
end;
```

**Pattern 3 - Mode definitions**:
```mizar
// WRONG:
definition
  let G be _Graph;
  mode Chain of G is Function of the_Edges_of G, GF2_squared;
end;  // ← Error 73: missing correctness

// CORRECT:
definition
  let G be _Graph;
  mode Chain of G is Function of the_Edges_of G, GF2_squared;
  correctness;  // ← Add this
end;
```

**Pattern 4 - Means definitions**:
```mizar
// WRONG:
definition
  func indicator_chain(gamma, S) -> Chain of G means
  :Def_indicator:
  for e being Element of the_Edges_of G holds ...;
  existence  // ← Error 72: needs wrapper
  proof
    ...
  end;
  uniqueness  // ← Error 72: needs wrapper
  proof
    ...
  end;
end;

// CORRECT:
definition
  func indicator_chain(gamma, S) -> Chain of G means
  :Def_indicator:
  for e being Element of the_Edges_of G holds ...;
  correctness  // ← Wrap both blocks
  proof
    existence
    proof
      ...
    end;
    uniqueness
    proof
      ...
    end;
  end;
end;
```

**Lesson**: Modern Mizar (post-2020) requires `correctness` keyword consistently. Replace `coherence;` with `correctness;` and wrap proof blocks properly.

---

### Error 301: "Predicate symbol expected"

**Cause**: Symbol not in vocabulary file

**Fix**:
1. Add `Ris_your_symbol` to `dict/yourfile.voc`
2. Add `vocabularies YOURFILE` to environ
3. Recompile

---

### Error 203: "Unknown token"

**Causes**:
1. Missing vocabulary (same fix as 301)
2. Spaces in symbol names (use underscores)
3. Special characters in names (use only letters, numbers, underscores)
4. `end.` at end of file (remove it!)

---

### Error 216: "Unexpected end"

**Causes**:
1. `end.` at end of file - remove it! Files should end with `end;` from last definition
2. Unclosed definition block
3. Missing semicolons

**Fix**: Remove `end.`, ensure all definitions close with `end;`

---

### Error 140/142: "Unknown variable" / "Unknown locus"

**Causes**:
1. Missing `let` declaration in definition
2. Using undefined type
3. Missing vocabulary import

**Fix**:
```mizar
definition
  let X be set;      # Must declare parameters with types!
  pred X is_empty means
  X = {};
end;
```

---

### Error 4: "This inference is not accepted"

**Status from 4CP**: Often acceptable! This is the MML automation boundary.

**When to worry**: If it's in a definition or key theorem
**When not to worry**: If it's in routine set/arithmetic steps

**Strategy**: Defer Error 4 during structural setup, tackle during proof completion phase.

---

### Error 100: "Expression type"

**Causes**:
- Type mismatch
- Missing type registrations

**Fix**:
- Add to environ: `registrations XBOOLE_0, FINSEQ_1;`
- Check type conversions are valid

---

## Best Practices

### 1. Directory Structure

**Always use**:
```
myproject/
  text/           # .miz files here
  dict/           # .voc files here
  prel/           # Format files (optional)
```

---

### 2. Vocabulary First

**Workflow**:
1. Plan what symbols you need
2. Create .voc file with all symbols
3. Write .miz file
4. Compile and debug

**Don't** try to write the .miz file first!

---

### 3. Start From Working Examples

**Process**:
1. Find similar construct in MML
2. Copy entire file and verify it compiles (0 errors)
3. Modify ONE thing at a time
4. After each change, recompile
5. Document what breaks

---

### 4. Environ Section Order

```mizar
environ
 vocabularies YOUR_NEW_VOC, MML_VOCS;    # Your vocab FIRST
 notations XBOOLE_0, FINSEQ_1;           # What notation you use
 constructors XBOOLE_0, FINSEQ_1;        # What constructors you need
 registrations XBOOLE_0, FINSEQ_1;       # Type system extensions
 schemes NAT_1;                          # If using induction/schemes
 requirements SUBSET, NUMERALS, ARITHM;  # Automation features
```

---

### 5. No `end.` at File End

**Wrong**:
```mizar
definition
  ...
end;

end.    ← Remove this!
```

**Right**:
```mizar
definition
  ...
end;    ← File ends here
```

---

### 6. Label Usage

**Predicates**: Optional labels (use if you want to reference in proofs)
```mizar
pred X is_empty means  # No label - simple case
X = {};

pred X is_empty means  # With label - for proof references
:Def1:
X = {};
```

**Attributes/Functors**: YES labels (required for reference)
```mizar
attr S is finite means
:Def1:
...

func f(x) equals
:Def1:
...
```

---

### 7. Incremental Complexity

**Start simple**:
1. Single predicate definition
2. Add second definition
3. Add theorem (may be hard!)
4. Add proof

Don't try to write complete article at once!

---

### 8. Use Reserve for Common Variables

**In begin section**:
```mizar
reserve X, Y for set;
reserve p, q for FinSequence;
reserve n, m for Nat;
```

**Benefits**: Less repetition in theorems

**BUT**: Still need `let` in definitions!

---

## Common Pitfalls

### 1. Forgetting to Add Schemes

**Symptom**: "Unknown scheme" or verification fails mysteriously

**Fix**:
```mizar
environ
  schemes NAT_1;  :: <-- Add this!
```

---

### 2. Using Edit Tool with Multiline Strings

**Problem**: Exact whitespace matching is fragile

**Solution**: When adding large blocks, consider using multiple smaller edits or checking exact formatting first.

---

### 3. Coherence vs Correctness Confusion

**Problem**: Using `coherence;` when Mizar expects `correctness;`

**Solution**: Use `correctness;` universally for definitions (Error 72/73 pattern from 4CP).

---

## Real-World Examples

### Example 1: prefix_free.miz (Basic Pattern)

**Problem**: Defining prefix-free sets for Kraft's inequality

**Step 1**: Create `dict/prefix_free.voc`
```
Ris_prefix_of
Vprefix_free
```

**Step 2**: Create `text/prefix_free.miz`
```mizar
environ
 vocabularies PREFIX_FREE, FINSEQ_1, XBOOLE_0, SUBSET_1;
 notations FINSEQ_1, XBOOLE_0;
 constructors FINSEQ_1;
 registrations FINSEQ_1, XBOOLE_0;

begin

definition
  let p, q be FinSequence;
  pred p is_prefix_of q means
  ex r being FinSequence st q = p ^ r;
end;

definition
  let S be set;
  attr S is prefix_free means
  :Def1:
  for p, q being FinSequence st p in S & q in S holds
    p = q or not p is_prefix_of q;
end;
```

---

### Example 2: set_parity.miz (Complete 4CP Example)

**Complete example using all patterns** (610 lines, all proofs complete):
- Parity decomposition with induction
- Scheme invocation (NAT_1:sch 1)
- Witness construction
- ARITHM requirements
- Full proof completion

**Key theorems**:
- `Th_parity_decomposition` - Foundation for all parity proofs
- `Th_odd_plus_odd_even` - Using decomposition pattern
- `Th_even_card_symdiff` - Set parity preservation

---

### Example 3: strong_dual.miz (Modularity in Action)

**Demonstrates**:
- `articles` directive to import face_boundary.miz
- `reserve` statement for clean theorem signatures
- Building complex theory on existing infrastructure
- Reduced from 752 to 362 lines via modularity

---

## Summary Checklist

Before starting any Mizar article:

- [ ] Created `text/` and `dict/` directories
- [ ] Created `.voc` file with ALL new symbols
- [ ] Used correct qualifiers (R, O, M, V, G, U)
- [ ] No spaces in symbol names
- [ ] One symbol per line in .voc
- [ ] Added `vocabularies MYFILE` to environ (FIRST position)
- [ ] Used `let` to declare parameters in definitions
- [ ] NO `end.` at end of file
- [ ] Used `correctness;` (not `coherence;`) for all definitions
- [ ] Labels for attributes/functors, optional for predicates
- [ ] Added `schemes` if using induction
- [ ] Added `requirements ARITHM` if doing arithmetic
- [ ] Started with working MML example

**Follow this checklist and you'll avoid 90% of beginner errors!**

---

## Additional Resources

- [Mizar Home Page](https://mizar.uwb.edu.pl/)
- [MML Browser](http://mizar.org/version/current/html/)
- [Mizar Manual PDF](https://www.cse.chalmers.se/research/group/logic/TypesSS05/Extra/wiedijk_1.pdf)
- [Mizar Lecture Notes](http://markun.cs.shinshu-u.ac.jp/kiso/projects/proofchecker/mizar/Mizar4/printout/mizar4en_prn.pdf)
- **4CP Formalization**: See `theories/` directory for real-world examples
- **GPT-5 Pro**: Source of advanced proof patterns and scheme invocations

---

*Last updated: 2025-10-15*
*Merged from: how_to_miz.md (4CP lessons) + MIZAR_HOWTO.md (foundational guide)*
*Contributors: Claude Code + GPT-5 Pro assistance*
