# GF Formalization in Lean 4

Lean 4 formalization of Grammatical Framework (GF) abstract syntax, two concrete
grammars (Czech, English), and a verified semantic bridge to OSLF evidence semantics.

## Authorship

- Primary author: **Oruží (AI)**
- Human lead/editor: Zar

## Scope

This formalizes a **subset** of the GF Resource Grammar Library (RGL). It is not a
complete port of the RGL. Specifically:

- **Abstract syntax**: 170 core GF RGL function signatures with typed categories
- **Czech**: Morphology engine (14 declension paradigms, verbs, adjectives, pronouns,
  numerals) with partial linearization. Does not cover full clause construction.
- **English**: Morphology plus clause construction (tense/aspect/polarity, do-support,
  relative clauses, VP slash). Broader syntactic coverage than Czech but still partial.
- **Semantic bridge**: GF abstract trees to OSLF rewrite rules to evidence-valued
  denotational semantics via the Grothendieck construction (NativeTypeTheory).

**Not included**: PGF runtime, PMCFG parsing, chart parsing, full conjunction
linearization, full numeral linearization in English.

## Proof Status

Zero sorries. Zero axioms. Every theorem is proven.

## Architecture

```
Core.lean            GF categories (112), AbstractTree, ConcreteForm, Grammar
Abstract.lean        All RGL function signatures, AbstractNode constructors
Concrete.lean        InflectionTable, morphophonological operations
Typing.lean          GF-to-OSLF type checking, Frege compositionality
KernelConfluence     Proven confluence of the GF rewrite kernel
SemanticKernel...    Proven semantic-level confluence (10 rewrite rules)
OSLFBridge.lean      GF abstract syntax as OSLF LanguageDef
                    (170 core signatures; 985 generated grammar rules)
WorldModelSem...     Evidence-valued denotational semantics for GF trees
VisibleLayer.lean    TUG visible semantic layer (V1-V4 actions)
VisibleLayerGF...    GF-specific NPReplacer and VisibleCfg
StoreToLogical...    GrammarState to QFormula2 conversion
WorldModelVis...     Store-aware evidence bridge
OSLFToNTT.lean       Composition into NativeTypeTheory (Grothendieck ∫ Sub)
LinguisticInv...     Cross-linguistic invariance theorems
RoundTripRegr...     Proven roundtrip regression (0 failures, both languages)
Czech/               Czech morphology engine (see Czech/README.md)
English/             English morphology and clause construction (see English/README.md)
Examples/            End-to-end pipeline examples (see Examples/README.md)
```

## Key Results

- **Kernel confluence**: `kernel_confluence_mod` (syntactic), plus semantic-level
  commutation and determinism theorems
- **Cross-linguistic invariance**: English and Czech share operational semantics
  (`english_czech_reduces_iff`, `english_czech_sem_iff`)
- **Roundtrip regression**: `totalFailureCount_zero` (proven 0 failures across
  36 corpus entries)
- **End-to-end pipeline**: Three worked examples proving the complete
  GF tree -> Pattern -> Store -> QFormula -> Evidence pipeline

## References

- Ranta, A. (2004). *Grammatical Framework: Programming with Multilingual Grammars*
- Meredith & Stay, "Operational Semantics in Logical Form"
- GF RGL source: https://github.com/GrammaticalFramework/gf-rgl
