# OSLF in Mettapedia

Operational Semantics in Logical Form (OSLF) over `LanguageDef` rewrite systems,
with premise-aware execution, checker soundness, and presheaf-topos bridge layers.

## Current Entry Points

- `Mettapedia/OSLF/CoreMain.lean`
  - Core-first entrypoint (intended for review of the current OSLF/GSLT stack).
  - Excludes `PiCalculus.Main` on purpose.
- `Mettapedia/OSLF/Main.lean`
  - Kitchen-sink entrypoint including π-calculus modules (still WIP in places).

## What Is Implemented

### 1) LanguageDef → RewriteSystem → OSLFTypeSystem

Main synthesis pipeline:
- `Mettapedia/OSLF/Framework/TypeSynthesis.lean`
  - `langRewriteSystemUsing`
  - `langDiamondUsing`, `langBoxUsing`
  - `langGaloisUsing`
  - `langOSLF`

This is the core "derive a type system from operational semantics" path.

### 2) Premise-Aware Operational Semantics

- `Mettapedia/OSLF/MeTTaIL/Syntax.lean`
  - `Premise`, `RewriteRule`, `LanguageDef`
- `Mettapedia/OSLF/MeTTaIL/Engine.lean`
  - `RelationEnv`
  - `applyRuleWithPremisesUsing`
  - `rewriteWithContextWithPremisesUsing`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`
  - executable/declarative bridge with soundness/completeness theorems

### 3) Formula Layer + Checker Soundness

- `Mettapedia/OSLF/Formula.lean`
  - `OSLFFormula`, `sem`, `checkLangUsing`
  - checker-soundness bridges into semantic satisfaction and sort-fiber predicates
  - graph-object checker soundness corollaries for both `.dia` and `.box`

### 4) Presheaf/Topos Lift Integration Status

The authoritative tracker is:
- `Mettapedia/OSLF/Framework/FULLStatus.lean`

Use this file for done/in-progress/missing milestones with code anchors.

### 5) Concrete Clients

- `Mettapedia/OSLF/Framework/TinyMLInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaFullInstance.lean`
- `Mettapedia/OSLF/MeTTaCore/FullLanguageDef.lean`
- `Mettapedia/OSLF/MeTTaCore/Premises.lean`

## Language Workflow (Practical)

1. Define a language in `LanguageDef`:
   - sorts (`types`)
   - constructors (`terms`)
   - rewrites (`rewrites`)
   - premises (`Premise`)
2. If needed, define external premise relations via `RelationEnv`.
3. Instantiate `langOSLF` (usually with your process sort).
4. Use `checkLangUsing` + soundness bridges in `Formula.lean`.
5. Add an instance file with end-to-end theorem(s) (TinyML/MeTTa pattern).

## Build

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF.CoreMain
lake build Mettapedia.OSLF.Main
```

## Notes

- `CoreMain` is the recommended target for core OSLF/GSLT validation.
- `Main` includes additional modules that may still carry WIP proof obligations
  (especially in π-calculus layers).
- For exact completion claims, rely on `FULLStatus.lean` and concrete theorem names,
  not static line-count snapshots.

## Lean ↔ Rust Example

For the concrete Lean-export → Rust-runtime roundtrip demo (TinyML smoke):

- Repo: <https://github.com/zariuq/mettail-rust>
- Branch: <https://github.com/zariuq/mettail-rust/tree/feature/lean-language-export-tinyml-smoke>

Related local files:
- `Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean`
- `hyperon/mettail-rust/scripts/roundtrip_tinymlsmoke.sh`
