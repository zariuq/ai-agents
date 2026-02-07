import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Soundness
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.RhoCalculus.Engine
import Mettapedia.OSLF.PiCalculus.Main
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Formula

/-!
# Operational Semantics in Logical Form (OSLF)

Re-exports for the OSLF formalization, connecting MeTTaIL language definitions
to categorical semantics via the OSLF algorithm.

## Module Structure

```
OSLF/
├── Main.lean                -- This file (re-exports)
├── Framework/
│   ├── RewriteSystem.lean      -- Abstract OSLF: RewriteSystem -> OSLFTypeSystem
│   ├── RhoInstance.lean        -- ρ-calculus instance (proven Galois connection)
│   ├── DerivedModalities.lean  -- Derived ◇/□ from adjoint triple (0 sorries)
│   ├── CategoryBridge.lean     -- Categorical lift: GaloisConnection → Adjunction, SubobjectFibration
│   ├── TypeSynthesis.lean      -- LanguageDef → OSLFTypeSystem (auto Galois)
│   ├── GeneratedTyping.lean    -- Generated typing rules from grammar
│   ├── SynthesisBridge.lean    -- Bridge: generated ↔ hand-written types
│   └── LambdaInstance.lean     -- Lambda calculus OSLF instance (2nd example)
├── MeTTaIL/
│   ├── Syntax.lean          -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean       -- InterpObj, pattern interpretation
│   ├── Substitution.lean    -- Capture-avoiding substitution
│   ├── Match.lean           -- Generic pattern matching (multiset, alpha-rename)
│   ├── Engine.lean          -- Generic rewrite engine for any LanguageDef
│   └── DeclReduces.lean     -- Declarative reduction (proven ↔ engine)
├── RhoCalculus/
│   ├── Types.lean           -- Namespaces, codespaces, bisimulation
│   ├── Reduction.lean       -- COMM/DROP/PAR, modal operators, Galois connection
│   ├── Soundness.lean       -- Substitutability, progress, type preservation
│   ├── StructuralCongruence.lean
│   ├── CommRule.lean
│   ├── SpiceRule.lean
│   ├── PresentMoment.lean
│   └── Engine.lean         -- Executable rewrite engine (reduceStep, proven sound)
├── Formula.lean             -- Formula AST + bounded model checker (proven sound)
├── PiCalculus/              -- π-calculus and ρ-encoding
└── NativeType/
    └── Construction.lean    -- NT as (sort, pred) pairs, type formation rules
```

## Architecture

The formalization has two layers:

### Abstract Layer (Framework/)
- `RewriteSystem`: sorts + terms + reduction (INPUT to OSLF)
- `OSLFTypeSystem`: predicates + Frame + diamond/box + Galois connection (OUTPUT)
- `NativeTypeOf`: native type = (sort, predicate) pair

### Concrete Layer (RhoCalculus/)
- `Reduces`: COMM, DROP, PAR, EQUIV rules (Type-valued)
- `possiblyProp` / `relyProp`: modal operators on `Pattern -> Prop`
- `galois_connection`: proven diamond -| box
- `HasType`: Typing judgment with substitutability and progress

The concrete layer is fully proven (0 sorries). The abstract framework
(`rhoOSLF`) instantiates the general OSLF construction for ρ-calculus,
lifting the proven Galois connection.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF

-- Re-export MeTTaIL modules
export Mettapedia.OSLF.MeTTaIL.Syntax (
  CollType
  TypeExpr
  TermParam
  SyntaxItem
  GrammarRule
  Pattern
  FreshnessCondition
  Premise
  Equation
  RewriteRule
  LanguageDef
  rhoCalc
)

export Mettapedia.OSLF.MeTTaIL.Semantics (
  InterpObj
  WellFormedLanguage
)

export Mettapedia.OSLF.MeTTaIL.Substitution (
  SubstEnv
  applySubst
  freeVars
  isFresh
  commSubst
)

export Mettapedia.OSLF.MeTTaIL.Match (
  matchPattern
  matchBag
  matchArgs
  applyBindings
  applyRule
  rewriteStep
)

export Mettapedia.OSLF.MeTTaIL.Engine (
  rewriteWithContext
  fullRewriteToNormalForm
)

export Mettapedia.OSLF.MeTTaIL.DeclReduces (
  DeclReduces
  engine_sound
  engine_complete
  declReduces_iff_langReduces
)

-- Re-export RhoCalculus modules
export Mettapedia.OSLF.RhoCalculus (
  ProcObj
  NameObj
  NamePred
  ProcPred
  BarbedParams
  BarbedRelation
  ProcEquiv
)

export Mettapedia.OSLF.RhoCalculus.Soundness (
  NativeType
  TypingContext
  HasType
  substitutability
  comm_preserves_type
)

export Mettapedia.OSLF.RhoCalculus.Reduction (
  Reduces
  possiblyProp
  relyProp
  galois_connection
)

-- Re-export Engine module
export Mettapedia.OSLF.RhoCalculus.Engine (
  reduceStep
  reduceToNormalForm
  reduceAll
  reduceStep_sound
)

-- Re-export Framework modules
export Mettapedia.OSLF.Framework (
  RewriteSystem
  OSLFTypeSystem
  NativeTypeOf
  Substitutability
)

export Mettapedia.OSLF.Framework.RhoInstance (
  RhoSort
  rhoRewriteSystem
  rhoOSLF
  rho_mathlib_galois
)

export Mettapedia.OSLF.Framework.DerivedModalities (
  ReductionSpan
  derivedDiamond
  derivedBox
  derived_galois
  rhoSpan
  derived_diamond_eq_possiblyProp
  derived_box_eq_relyProp
  rho_galois_from_span
)

export Mettapedia.OSLF.Framework.TypeSynthesis (
  langReduces
  langRewriteSystem
  langSpan
  langDiamond
  langBox
  langGalois
  langOSLF
  langNativeType
)

export Mettapedia.OSLF.Framework.GeneratedTyping (
  GenNativeType
  GenTypingContext
  GenHasType
  topPred
)

export Mettapedia.OSLF.Framework.SynthesisBridge (
  langDiamond_implies_possibly_at
  possibly_implies_langDiamond_at
  specialized_possibly
  specialized_rely_check
  specialized_can_reduce
  nativeToGen
  ctxToGen
)

export Mettapedia.OSLF.Framework.CategoryBridge (
  langDiamond_monotone
  langBox_monotone
  PredLattice
  langGaloisL
  langModalAdjunction
  rhoModalAdjunction
  SortCategory
  predFibration
  oslf_fibration
)

export Mettapedia.OSLF.Framework.LambdaInstance (
  lambdaCalc
  lambdaOSLF
  lambdaGalois
)

-- Re-export Formula module (OSLF output artifact)
export Mettapedia.OSLF.Formula (
  OSLFFormula
  sem
  sem_dia_eq_langDiamond
  sem_box_eq_langBox
  formula_galois
  CheckResult
  check
  check_sat_sound
  aggregateBox
  aggregateBox_sat
  checkWithPred
  checkWithPred_sat_sound
  rhoAtoms
  rhoAtomSem
  rhoAtoms_sound
)

end Mettapedia.OSLF
