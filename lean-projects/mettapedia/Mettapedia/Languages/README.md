# Mettapedia/Languages

Formal linguistics, natural language semantics, and process calculi formalization.

## Modules

### GF/ (Grammatical Framework)

Lean 4 formalization of a GF RGL subset: 170 abstract syntax signatures, two concrete
grammars (Czech morphology, English clause construction), and a verified semantic bridge
from GF abstract trees through OSLF evidence semantics to NativeTypeTheory.

- **Czech**: 14 declension paradigms, verb conjugation, adjectives, pronouns, numerals
- **English**: Full clause construction (tense/aspect/polarity), do-support, relative clauses
- **Semantic bridge**: GF -> Pattern -> Store -> QFormula -> Evidence -> NTT
- **Proof status**: Zero sorries, zero axioms, 36-entry roundtrip corpus (18 per language)

See `GF/README.md` for full architecture and file map.

#### GF/SUMO/ — SUMO Ontology Repair Pipeline

Top-down repair of the SUMO upper ontology through the GF->OSLF->WM pipeline.
Compares three sources: SUMO KIF (387k lines), Enache's original SUMO-GF encoding
(30k lines, GF 3.3), and our flattened Lean encoding (~50 FOET-relevant classes).

**Full pipeline**: SUMO KIF -> GF Pattern -> GSLT (LanguageDef) -> OSLF (diamond/box) -> WM (checkLang)

The class hierarchy IS a rewrite system (subclass = coercion). Modeled as a GSLT
with proven Galois connection, NTT extraction, and formal inconsistency detection
via the proven-sound `checkLang` formula checker.

**6 automated repair patterns**: counting, definitional unfolding, domain lookup,
vacuity detection, superrelation widening, WM evidence evaluation.

**File map**:
- `SumoAbstract.lean` — ~50 FOET classes, ~350 function signatures, transitive closure
- `SumoOSLFBridge.lean` — Pipeline bridge, Galois connection (proven), Stage 1-2 diagnostics
- `SumoNTT.lean` — Class hierarchy as GSLT, NTT extraction, Stage 3 WM checkLang evaluation
- `SumoRepairRunner.lean` — Three-source diff: 53 classes, flags disagreements
- `SumoAxiomCensus.lean` — Per-concept usage evidence for flagged concepts
- `RepairLog.lean` — 20 repair decisions (19 automatable) + 4 strengthening proposals
- `original/` — Downloaded Enache & Angelov SUMO-GF (read-only reference)

**Current status** (2026-02-19):
- Layer 1 (strata 0-1) complete: 33 classes, 153 transitive edges, full pipeline
- 20 repair decisions: 19 automatable, Pain resolved via EmotionalState (39:1 peer match)
- FOET KIF: 12 fixes applied (syntax, arg swaps, VirtuousAgent, attribute->property)
- Formal inconsistency detection: checkLang proves (contraryAttribute Pleasure Pain) ill-typed
- 53 classes analyzed: 25 agree, 5 missing from GF, 1 flattened, 3 infrastructure sorts, 19 FOET-only
- 3 relation typing issues found and 1 fixed (attribute domain: Agent -> Object)
- Transitive closure: 54 direct edges -> full closure (13 classes reach Attribute, 9 reach Object)
- Pain/Attribute type conflict automatically detected via coercion path analysis
- All files build clean, zero sorries

### ProcessCalculi/

Pi-calculus and rho-calculus formalized with operational semantics, structural congruence,
and OSLF instances. Includes the Lybech (2022) pi-to-rho encoding with proven forward
simulation, and Meredith's spice calculus (n-step lookahead).

- **Pi-calculus**: 16 files, asynchronous choice-free fragment (Lybech 2022)
- **Rho-calculus**: 11 files, locally nameless with COMM reduction + spice rule
- **Encoding**: Pi-to-rho forward simulation (restriction-free fragment, proven)
- **Proof status**: Zero sorries

See `ProcessCalculi/README.md` for details.
