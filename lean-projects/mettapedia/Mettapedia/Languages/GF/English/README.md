# English Morphology and Clause Construction

Lean 4 formalization of English morphology and syntactic linearization, ported from
the GF RGL source files (ResEng.gf, ParadigmsEng.gf, SentenceEng.gf, RelativeEng.gf).

This covers more syntactic ground than the Czech formalization: full clause
construction with tense/aspect/polarity, do-support, relative clauses, and
transitive verb complements. It is still a partial port of the GF RGL English.

## Coverage

### Morphology (Morphology.lean)
Core parameter types: Case (2), Number (2), Gender (3), Person (3),
Agr (8 agreement values), VForm (5 verb forms), Tense (4), Anteriority (2),
CPolarity (3: positive, negative, contracted negative), Polarity (2),
Order (2: declarative/interrogative), Degree (3).

### Nouns (Nouns.lean)
Pluralization rules (`addS`), genitive formation, `mk4N`/`mk2N`/`regN`/`compoundN`.
Includes irregular nouns (man/woman/mouse/foot/tooth/child/ox/sheep),
gendered nouns, and compound nouns.

### Adjectives (Adjectives.lean)
Regular, compound, irregular, invariable paradigms. `compStem` for comparative
formation.

### Verbs (Verbs.lean)
5-form verb paradigm (infinitive, past, past participle, present 3sg, present
participle). Regular, irregular (3-form, 4-form) constructors. Full auxiliary
verb paradigms (be/have/do) with polarity-sensitive forms.
`EnglishV2` for transitive verbs with complement preposition.

### Syntax (Syntax.lean)
Full clause construction:
- Tense x anteriority combinations with positive and negative (contracted and
  uncontracted) realizations
- Do-support for questions and negation
- Declarative and interrogative word orders
- `EnglishVP`, `EnglishVPSlash` (for extraction), `EnglishClause`
- Article selection (a/an/the), mass nouns
- VP modification (adverbs), VP complementation

### Relative Clauses (Relatives.lean)
`EnglishRP`, `EnglishRCl`, `EnglishRS`, `EnglishClSlash`.
`relVP` (subject relative), `relSlash` (object relative with extraction),
`useRCl` (tense/polarity).

### Pronouns (Pronouns.lean)
8 personal pronouns with full case forms, 5 demonstrative determiners,
5 quantifier determiners, interrogatives (who/what).
`EnglishPrep` (9 prepositions + 1 postposition), `EnglishConj` (5 patterns),
`EnglishSubj` (8 subordinating conjunctions).

### Linearization (Linearization.lean)
`EnglishLinEnv` bridge from GF abstract trees to English surface strings.
`NodeLinearize` instance for the English grammar.

## What's Proven

- Core morphology and syntax constructors are executable and regression-checked
- Theorem-backed example suite in `Examples.lean` (including tense, negation,
  questions, irregular verbs, transitive complements, relative clauses,
  subordination, and garden-path disambiguation)
- Garden-path disambiguation ("The old man the boats")
- 18-entry roundtrip corpus with proven completeness (RoundTripCorpus.lean)
- Zero sorries, zero axioms

## What's Missing

- Full numeral linearization (type defined but not linearized)
- Conjunction linearization (types defined, no surface generation)
- Passive voice morphology
- Comparative/superlative clause-level constructions
- Many GF RGL functions not covered (Idiom, Extend, Construction modules)

## Source Attribution

Ported from GF RGL English concrete syntax:
https://github.com/GrammaticalFramework/gf-rgl/tree/master/src/english
