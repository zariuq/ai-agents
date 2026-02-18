# Czech Morphology Engine

Lean 4 formalization of Czech nominal and verbal morphology, ported from the GF RGL
source files (ResCze.gf, ParadigmsCze.gf, MorphoCze.gf).

**This is a morphology engine, not a complete Czech grammar.** It covers declension,
conjugation, and agreement but does not implement full Czech clause construction
(VP/S-level linearization is partial compared to the English formalization).

## Coverage

### Nouns (Declensions.lean)
14 declension paradigms covering all standard Czech noun classes:
- Masculine animate: PAN, MUZ, PREDSEDA, SOUDCE
- Masculine inanimate: HRAD, STROJ
- Feminine: ZENA, RUZE, PISEN, KOST
- Neuter: MESTO, KURE, MORE, STAVENI

Each paradigm generates forms for 7 cases x 2 numbers = 14 forms.
Form counts are proven correct by `decide`.

### Verbs (Verbs.lean)
`VerbForms` with 10 fields (infinitive, present 1sg/2sg/3sg/1pl/2pl/3pl,
past participle, imperative 2sg, verbal noun). Covers copula, -ovat class.

### Adjectives (Adjectives.lean)
5 paradigm types: mlady (hard), jarni (soft), otcuv (possessive m.),
matcin (possessive f.), invariable. 15 named slots are mapped to the full
Gender x Number x Case table (56 parameter combinations with syncretism).

### Pronouns (Pronouns.lean)
8 personal pronouns (ja/ty/on/ona/ono/my/vy/oni), 7 possessive forms,
reflexive (se/si), demonstrative (ten/ta/to), interrogative (kdo/co).

### Numerals (Numerals.lean)
jeden/dva/tri/ctyri with full case declension, 5+ pattern, invariable higher.

### Agreement (Agreement.lean)
NumSize-based case/number selection for numeral-noun agreement.

## What's Proven

- Form counts for all 14 declension paradigms (Properties.lean)
- String-level regression tests for PAN paradigm: all 13 forms (Tests.lean)
- 18-entry roundtrip corpus with proven completeness (RoundTripCorpus.lean)
- Zero sorries, zero axioms

## What's Missing

- Full clause construction (SentenceCze.gf equivalent) — not formalized
- Verbal aspect pairs — not modeled
- Full sentence-level Czech linearization comparable to the English layer
- Numeral-noun agreement beyond basic NumSize patterns

## Source Attribution

Ported from GF RGL Czech concrete syntax:
https://github.com/GrammaticalFramework/gf-rgl/tree/master/src/czech
