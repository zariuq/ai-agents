import Mettapedia.OSLF.MeTTaIL.PremiseDatalog

/-!
# HE MeTTa Premises as PremiseProgram

Defines the premise relations needed by `mettaHE : LanguageDef` rewrite rules.
These capture HE's evaluation dispatch decisions: metatype checking, function
type applicability, equation query, grounded dispatch, etc.

## Relation Summary

| Relation | Arity | Description |
|----------|-------|-------------|
| isEmpty | 1 | Atom is the Empty sentinel |
| isError | 1 | Atom matches (Error _ _) pattern |
| metaType | 2 | Intrinsic metatype of atom |
| typeMatchesMetaOrAtom | 2 | type == Atom or type == metatype or metatype == Variable |
| typeNotMatchesMetaOrAtom | 2 | explicit positive complement of typeMatchesMetaOrAtom |
| needsTypeCast | 2 | metaType ∈ {Symbol, Grounded} and NOT typeMatchesMetaOrAtom |
| needsInterpExpr | 2 | metaType == Expression and NOT typeMatchesMetaOrAtom |
| atomTypes | 3 | Type annotations (: atom type) from space |
| isFuncType | 1 | Type is an arrow (-> ...) |
| applicableFuncType | 5 | Function type is applicable to expression with expected type |
| needsTupleInterp | 3 | No applicable func type + has non-func types |
| noTypeAtAll | 2 | Expression head has no type annotations in space |
| notExpression | 1 | Atom is not an Expression (metatype != Expression) |
| eqQueryResult | 3 | Equation query: (= pattern rhs) matched, rhs resolved |
| eqQueryHas | 2 | Witness that at least one equation matched |
| noEqQuery | 2 | No matching equations in space (index-backed check) |
| groundedCallResult | 3 | Grounded dispatch → Ok result |
| isExecutable | 1 | Atom is an executable grounded atom |
| notExecutable | 1 | Negation of isExecutable |
| typeOf | 3 | Atom has type in space (via annotations) |
| typeMismatch | 4 | Atom's actual type != expected type |
| funcArgTypes | 2 | Extract argument type list from ArrowType |
| changedToEmpty | 2 | New atom is Empty and changed from original |
| changedToError | 2 | New atom is Error and changed from original |
| interpFuncResult | (removed) | moved to explicit rewrite transitions |
| interpTupleResult | (removed) | moved to explicit rewrite transitions |

## Design Notes

- Recursive evaluation semantics should be encoded as explicit rewrite transitions
  in `HELanguageDef.lean`, not hidden in opaque premise builtins.
- Simpler relations (isEmpty, isError, metaType) are pure structural checks
  that compile directly to Ascent pattern matching.
-/

namespace Mettapedia.Languages.MeTTa.HE.Premises

open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

/-! ## Atom Predicate Relations -/

/-- `isEmpty(atom)`: atom is the Empty sentinel. -/
private def isEmptyRules : List PRule :=
  [ { headRel := "isEmpty"
      headArgs := [.var "atom"]
      body := [.eq (.var "atom") (.ctor "Empty" [])]
      clauseName := some "isEmpty_check" } ]

/-- `isError(atom)`: atom matches ErrorAtom(source, code). -/
private def isErrorRules : List PRule :=
  [ { headRel := "isError"
      headArgs := [.var "atom"]
      body := [.deconstruct (.var "atom") "ErrorAtom" ["_source", "_code"]]
      clauseName := some "isError_check" } ]

/-- `changedToEmpty(orig, new)`:
    short-circuit guard used by interpretArgs: new == Empty and new != orig. -/
private def changedToEmptyRules : List PRule :=
  [ { headRel := "changedToEmpty"
      headArgs := [.var "orig", .var "new"]
      body := [ .relQuery "isEmpty" [.var "new"]
              , .neq (.var "new") (.var "orig") ]
      clauseName := some "changedToEmpty_guard" } ]

/-- `changedToError(orig, new)`:
    short-circuit guard used by interpretArgs: new is Error and new != orig. -/
private def changedToErrorRules : List PRule :=
  [ { headRel := "changedToError"
      headArgs := [.var "orig", .var "new"]
      body := [ .relQuery "isError" [.var "new"]
              , .neq (.var "new") (.var "orig") ]
      clauseName := some "changedToError_guard" } ]

/-! ## Metatype Relations -/

/-- `metaType(atom, mt)`: intrinsic metatype of atom.
    Ref: metta.md `get_meta_type`. -/
private def metaTypeRules : List PRule :=
  [ -- Symbol atoms → "Symbol"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "SymbolType" []]
      body := [.deconstruct (.var "atom") "SymAtom" ["_"]]
      clauseName := some "metaType_symbol" }
  , -- Variable atoms → "Variable"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "VariableType" []]
      body := [.deconstruct (.var "atom") "VarAtom" ["_"]]
      clauseName := some "metaType_variable" }
  , -- Expression atoms → "Expression"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "ExpressionType" []]
      body := [.deconstruct (.var "atom") "ExprCons" ["_", "_"]]
      clauseName := some "metaType_expression_cons" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "ExpressionType" []]
      body := [.eq (.var "atom") (.ctor "ExprNil" [])]
      clauseName := some "metaType_expression_nil" }
  , -- Grounded atoms → "Grounded"
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GInt" ["_"]]
      clauseName := some "metaType_grounded_int" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GString" ["_"]]
      clauseName := some "metaType_grounded_string" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.deconstruct (.var "atom") "GBool" ["_"]]
      clauseName := some "metaType_grounded_bool" }
  , -- Built-in grounded operators
    { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpAdd" [])]
      clauseName := some "metaType_grounded_op_add" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpSub" [])]
      clauseName := some "metaType_grounded_op_sub" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpMul" [])]
      clauseName := some "metaType_grounded_op_mul" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpDiv" [])]
      clauseName := some "metaType_grounded_op_div" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpMod" [])]
      clauseName := some "metaType_grounded_op_mod" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpLt" [])]
      clauseName := some "metaType_grounded_op_lt" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpGt" [])]
      clauseName := some "metaType_grounded_op_gt" }
  , { headRel := "metaType"
      headArgs := [.var "atom", .ctor "GroundedType" []]
      body := [.eq (.var "atom") (.ctor "OpEq" [])]
      clauseName := some "metaType_grounded_op_eq" }
  ]

/-! ## Metta Dispatch Relations -/

/-- `typeMatchesMetaOrAtom(atom, type)`:
    type == Atom OR type == metatype(atom) OR metatype(atom) == Variable.
    Ref: metta.md line 255. The `%Undefined%` wildcard belongs later in the
    `matchTypes`-style `typeOf`/`typeMismatch` path, not in early `metta`
    dispatch, otherwise untyped expressions short-circuit before
    `interpretExpression` / `mettaCall`. -/
private def typeMatchesMetaOrAtomRules : List PRule :=
  [ -- type == Atom
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.eq (.var "ty") (.ctor "AtomType" [])]
      clauseName := some "typeMatch_atomType" }
  , -- type == metatype(atom)
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.relQuery "metaType" [.var "atom", .var "ty"]]
      clauseName := some "typeMatch_sameMetaType" }
  , -- metatype(atom) == Variable
    { headRel := "typeMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [.relQuery "metaType" [.var "atom", .ctor "VariableType" []]]
      clauseName := some "typeMatch_variable" }
  ]

/-- `typeNotMatchesMetaOrAtom(atom, type)`:
    explicit positive complement for dispatch, avoiding negation cycles. -/
private def typeNotMatchesMetaOrAtomRules : List PRule :=
  [ { headRel := "typeNotMatchesMetaOrAtom"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .var "mt"]
              , .neq (.var "ty") (.ctor "AtomType" [])
              , .neq (.var "mt") (.ctor "VariableType" [])
              , .neq (.var "mt") (.var "ty") ]
      clauseName := some "typeNotMatch_explicit" } ]

/-- `needsTypeCast(atom, type)`:
    metatype ∈ {Symbol, Grounded} AND NOT typeMatchesMetaOrAtom.
    Ref: metta.md line 259. -/
private def needsTypeCastRules : List PRule :=
  [ -- Symbol atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "SymbolType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_symbol" }
  , -- Grounded atom, type doesn't match
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "GroundedType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_grounded" }
  , -- Unit expression ()
    { headRel := "needsTypeCast"
      headArgs := [.var "atom", .var "ty"]
      body := [ .eq (.var "atom") (.ctor "ExprNil" [])
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsTypeCast_unit" }
  ]

/-- `needsInterpExpr(atom, type)`:
    metatype == Expression AND NOT typeMatchesMetaOrAtom.
    Ref: metta.md lines 261-272. -/
private def needsInterpExprRules : List PRule :=
  [ { headRel := "needsInterpExpr"
      headArgs := [.var "atom", .var "ty"]
      body := [ .relQuery "metaType" [.var "atom", .ctor "ExpressionType" []]
              , .relQuery "typeNotMatchesMetaOrAtom" [.var "atom", .var "ty"] ]
      clauseName := some "needsInterpExpr_expression" } ]

/-! ## InterpExpr Dispatch Relations -/

/-- `notExpression(atom)`: atom is not an Expression. -/
private def notExpressionRules : List PRule :=
  [ { headRel := "notExpression"
      headArgs := [.var "atom"]
      body := [ .relQuery "metaType" [.var "atom", .var "mt"]
              , .neq (.var "mt") (.ctor "ExpressionType" []) ]
      clauseName := some "notExpression_check" } ]

/-! ## MettaCall Relations -/

/-- `isExecutable(op)`: op is an executable grounded atom.
    In HE, grounded atoms with execute capability are executable. -/
private def isExecutableRules : List PRule :=
  [ { headRel := "isExecutable"
      headArgs := [.var "op"]
      body := [.compute "checkExecutable" [.var "op"] "_"]
      clauseName := some "isExecutable_grounded" } ]

/-- `notExecutable(op)`: negation of isExecutable. -/
private def notExecutableRules : List PRule :=
  [ { headRel := "notExecutable"
      headArgs := [.var "op"]
      body := [.compute "checkNotExecutable" [.var "op"] "_"]
      clauseName := some "notExecutable_check" } ]

/-! ## Type System Relations -/

/-- `typeOfRaw(space, atom, type)`: raw type annotation lookup.
    Looks for (: atom type) entries in the space's atom list. -/
private def typeOfRawRules : List PRule :=
  [ { headRel := "typeOfRaw"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .deconstruct (.var "sp") "Space" ["atoms"]
              , .compute "findTypeAnnotation" [.var "atoms", .var "atom"] "ty" ]
      clauseName := some "typeOfRaw_annotation" } ]

/-- `typeOf(space, atom, type)`: atom has type annotation in space. -/
private def typeOfRules : List PRule :=
  [ { headRel := "typeOf"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .relQuery "typeOfRaw" [.var "sp", .var "atom", .var "ty"] ]
      clauseName := some "typeOf_from_raw" } ]

/-- `typeMismatch(space, atom, expectedType, actualType)`:
    atom has type actualType != expectedType in space.
    Used to produce BadType errors. -/
private def typeMismatchRules : List PRule :=
  [ { headRel := "typeMismatch"
      headArgs := [.var "sp", .var "atom", .var "expected", .var "actual"]
      body := [ .relQuery "typeOf" [.var "sp", .var "atom", .var "actual"]
              , .neq (.var "actual") (.var "expected") ]
      clauseName := some "typeMismatch_check" } ]

/-- `funcArgTypes(opType, argTypes)`:
    structural extractor for ArrowType argument lists. -/
private def funcArgTypesRules : List PRule :=
  [ { headRel := "funcArgTypes"
      headArgs := [.var "opType", .var "argTypes"]
      body := [ .deconstruct (.var "opType") "ArrowType" ["argTypes", "_ret"] ]
      clauseName := some "funcArgTypes_arrow" } ]

/-! ## Equation Query Relations -/

/-- `eqQueryResult(space, atom, rhs)`:
    Equation query: finds (= pattern rhs) in space where pattern matches atom.
    Returns the resolved rhs (with bindings applied).
    Ref: metta.md line 538. -/
private def eqQueryRawRules : List PRule :=
  [ { headRel := "eqQueryRaw"
      headArgs := [.var "sp", .var "atom", .var "rhs"]
      body := [ .computeMany "queryEquationsInSpace" [.var "sp", .var "atom"] "rhs" ]
      clauseName := some "eqQueryRaw_match" } ]

/-- `eqQueryResult(space, atom, rhs)`:
    projected equation query relation derived from `eqQueryRaw`. -/
private def eqQueryResultRules : List PRule :=
  [ { headRel := "eqQueryResult"
      headArgs := [.var "sp", .var "atom", .var "rhs"]
      body := [ .relQuery "eqQueryRaw" [.var "sp", .var "atom", .var "rhs"] ]
      clauseName := some "eqQueryResult_from_raw" } ]

/-- `eqQueryHas(space, atom)`: witness that an equation query has at least one rhs. -/
private def eqQueryHasRules : List PRule :=
  [ { headRel := "eqQueryHas"
      headArgs := [.var "sp", .var "atom"]
      body := [ .relQuery "eqQueryRaw" [.var "sp", .var "atom", .wild] ]
      clauseName := some "eqQueryHas_witness" } ]

/-- `noEqQuery(space, atom)`: no equations match in space. -/
private def noEqQueryRules : List PRule :=
  [ { headRel := "noEqQuery"
      headArgs := [.var "sp", .var "atom"]
      body := [ .notIn "eqQueryHas" [.var "sp", .var "atom"] ]
      clauseName := some "noEqQuery_notIn_has" } ]

/-! ## Complex Structural Relations (Builtins)

These builtins are structural queries over the current space/atom data.
Recursive evaluation is encoded in `HELanguageDef.lean` rewrite transitions. -/

/-- `applicableFuncTypeRaw(space, atom, expectedType, opType_retType)`:
    Raw lookup for applicable function type candidates (packed pair). -/
private def applicableFuncTypeRawRules : List PRule :=
  [ { headRel := "applicableFuncTypeRaw"
      headArgs := [.var "sp", .var "atom", .var "ty", .var "opType_retType"]
      body := [ .compute "findApplicableFuncType"
                  [.var "sp", .var "atom", .var "ty"] "opType_retType" ]
      clauseName := some "applicableFuncTypeRaw_check" } ]

/-- `applicableFuncType(space, atom, expectedType, opType, retType)`:
    Projected relation derived from raw applicable function-type lookup. -/
private def applicableFuncTypeRules : List PRule :=
  [ { headRel := "applicableFuncType"
      headArgs := [.var "sp", .var "atom", .var "ty", .var "opType", .var "retType"]
      body := [ .relQuery "applicableFuncTypeRaw"
                  [.var "sp", .var "atom", .var "ty", .var "opType_retType"]
              , .deconstruct (.var "opType_retType") "ExprCons" ["opType", "retType"] ]
      clauseName := some "applicableFuncType_from_raw" } ]

/-- `applicableFuncTypeHas(space, atom, expectedType)`:
    Witness that at least one applicable function type exists. -/
private def applicableFuncTypeHasRules : List PRule :=
  [ { headRel := "applicableFuncTypeHas"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .relQuery "applicableFuncTypeRaw"
                  [.var "sp", .var "atom", .var "ty", .wild] ]
      clauseName := some "applicableFuncTypeHas_witness" } ]

/-- `needsTupleInterp(space, atom, type)`:
    No applicable function type AND has non-function types.
    Ref: metta.md lines 350-355. -/
private def needsTupleInterpRules : List PRule :=
  [ { headRel := "needsTupleInterp"
      headArgs := [.var "sp", .var "atom", .var "ty"]
      body := [ .compute "hasNonFuncTypes" [.var "sp", .var "atom"] "ty"
              , .notIn "applicableFuncTypeHas" [.var "sp", .var "atom", .var "ty"] ]
      clauseName := some "needsTupleInterp_check" } ]

/-- `noTypeAtAll(space, atom)`:
    Expression head has no type annotations in the current space.
    This is the untyped-function fallback path needed for ordinary equation-
    defined heads like `(id 5)` to reach `mettaCall`.
    Ref: upstream Hyperon HE evaluates `(= (id $x) $x)` / `!(id 5)` to `5`
    without requiring `(: id ...)`. -/
private def noTypeAtAllRules : List PRule :=
  [ { headRel := "noTypeAtAll"
      headArgs := [.var "sp", .var "atom"]
      body := [ .compute "checkNoTypeAtAll" [.var "sp", .var "atom"] "_" ]
      clauseName := some "noTypeAtAll_missing_head_type" } ]

/-- `groundedCallResult(space, atom, result)`:
    Grounded dispatch result.
    Extracts op and args from expression, calls grounded dispatch. -/
private def groundedCallResultRules : List PRule :=
  [ { headRel := "groundedCallResult"
      headArgs := [.var "sp", .var "atom", .var "result"]
      body := [ .deconstruct (.var "atom") "ExprCons" ["op", "argsTail"]
              , .relQuery "isExecutable" [.var "op"]
              , .compute "evalGroundedDispatch" [.var "op", .var "argsTail"] "result" ]
      clauseName := some "groundedCallResult_dispatch" } ]

/-! ## Control Flow Relations (mettaCall control forms)

These support the MC_SwitchMinimal, MC_Assert, and MC_Case rewrite rules
in HELanguageDef.lean. Ref: Interpreter.lean:342-396. -/

/-- `parseSwitchMinimalCall(atom, scrutinee, rawCases)`:
    Recognizes (switch-minimal scrutinee rawCases) or (switch scrutinee rawCases).
    Extracts scrutinee and rawCases from the expression. -/
private def parseSwitchMinimalCallRules : List PRule :=
  [ { headRel := "parseSwitchMinimalCall"
      headArgs := [.var "atom", .var "scrutinee", .var "rawCases"]
      body := [ .compute "parseSwitchMinimalCallArgs" [.var "atom"] "packed"
              , .deconstruct (.var "packed") "ExprCons" ["scrutinee", "rawCases"] ]
      clauseName := some "parseSwitchMinimalCall_check" } ]

/-- `parseCaseCall(atom, scrutinee, rawCases)`:
    Recognizes (case scrutinee rawCases). Extracts components. -/
private def parseCaseCallRules : List PRule :=
  [ { headRel := "parseCaseCall"
      headArgs := [.var "atom", .var "scrutinee", .var "rawCases"]
      body := [ .compute "parseCaseCallArgs" [.var "atom"] "packed"
              , .deconstruct (.var "packed") "ExprCons" ["scrutinee", "rawCases"] ]
      clauseName := some "parseCaseCall_check" } ]

/-- `parseAssertCall(atom, asserted)`:
    Recognizes (assert asserted). Extracts the asserted expression. -/
private def parseAssertCallRules : List PRule :=
  [ { headRel := "parseAssertCall"
      headArgs := [.var "atom", .var "asserted"]
      body := [ .compute "parseAssertCallArg" [.var "atom"] "asserted" ]
      clauseName := some "parseAssertCall_check" } ]

/-- `selectSwitchResult(scrutinee, rawCases, template)`:
    Pattern-match scrutinee against case patterns in rawCases.
    Returns first matching template (nondeterministic within a match). -/
private def selectSwitchResultRules : List PRule :=
  [ { headRel := "selectSwitchResult"
      headArgs := [.var "scrutinee", .var "rawCases", .var "template"]
      body := [ .computeMany "selectSwitchTemplate"
                  [.var "scrutinee", .var "rawCases"] "template" ]
      clauseName := some "selectSwitchResult_match" } ]

/-- `isNotReducible(atom)`: atom is the sentinel SymAtom("NotReducible").
    Used by switch-minimal to detect exhausted case list. -/
private def isNotReducibleRules : List PRule :=
  [ { headRel := "isNotReducible"
      headArgs := [.var "atom"]
      body := [ .compute "checkIsNotReducible" [.var "atom"] "_" ]
      clauseName := some "isNotReducible_check" } ]

/-- `isReducible(atom)`: atom is NOT the NotReducible sentinel.
    Positive complement of isNotReducible. -/
private def isReducibleRules : List PRule :=
  [ { headRel := "isReducible"
      headArgs := [.var "atom"]
      body := [ .compute "checkIsReducible" [.var "atom"] "_" ]
      clauseName := some "isReducible_check" } ]

/-- `assertMatchesTrue(atom)`: atom matches the True atom.
    Used by MC_Assert_True. -/
private def assertMatchesTrueRules : List PRule :=
  [ { headRel := "assertMatchesTrue"
      headArgs := [.var "atom"]
      body := [ .eq (.var "atom") (.ctor "True" []) ]
      clauseName := some "assertMatchesTrue_check" } ]

/-- `assertNotTrue(atom)`: atom does NOT match True.
    Used by MC_Assert_NotTrue. -/
private def assertNotTrueRules : List PRule :=
  [ { headRel := "assertNotTrue"
      headArgs := [.var "atom"]
      body := [ .neq (.var "atom") (.ctor "True" []) ]
      clauseName := some "assertNotTrue_check" } ]

/-- `mkAssertError(asserted, assertedVal, errAtom)`:
    Construct the HE assert error shape:
    (Error (assert asserted) (assertedVal "not" "True"))
    Ref: Interpreter.lean:74-76 -/
private def mkAssertErrorRules : List PRule :=
  [ { headRel := "mkAssertError"
      headArgs := [.var "asserted", .var "assertedVal", .var "errAtom"]
      body := [ .compute "buildAssertError"
                  [.var "asserted", .var "assertedVal"] "errAtom" ]
      clauseName := some "mkAssertError_build" } ]

/-! ## Minimal Instruction Relations (superpose, match, unify, collapse)

These support the MC_Superpose, MC_Match, MC_Unify, and MC_Collapse rewrite
rules in HELanguageDef.lean. These are language-level primitives from the
minimal MeTTa instruction set, NOT grounded builtins.
Ref: OpProfile.lean — category: minimalInstruction. -/

/-- `parseSuperpose(atom, elem)`:
    Recognizes `(superpose (e1 e2 ...))`, yields one binding per element.
    Multi-result premise: template engine gets N bindings for N elements. -/
private def parseSuperoseRules : List PRule :=
  [ { headRel := "parseSuperpose"
      headArgs := [.var "atom", .var "elem"]
      body := [ .computeMany "parseSuperposElements" [.var "atom"] "elem" ]
      clauseName := some "parseSuperpose_elements" } ]

/-- `isSuperpose_empty(atom)`:
    Recognizes `(superpose ())` — superpose with empty argument list. -/
private def isSuperpose_emptyRules : List PRule :=
  [ { headRel := "isSuperpose_empty"
      headArgs := [.var "atom"]
      body := [ .compute "checkSuperposeEmpty" [.var "atom"] "_" ]
      clauseName := some "isSuperpose_empty_check" } ]

/-- `parseMatchCall(atom, pattern, template)`:
    Recognizes `(match spaceRef pattern template)`.
    Extracts pattern and template; spaceRef is checked but resolved
    via the runtime space object (not a template variable). -/
private def parseMatchCallRules : List PRule :=
  [ { headRel := "parseMatchCall"
      headArgs := [.var "atom", .var "pattern", .var "template"]
      body := [ .compute "parseMatchCallArgs" [.var "atom"] "packed"
              , .deconstruct (.var "packed") "ExprCons" ["pattern", "template"] ]
      clauseName := some "parseMatchCall_check" } ]

/-- `spaceQueryMatch(pattern, template, result)`:
    Multi-result: iterates space atoms, matches pattern against each,
    substitutes bindings into template. Yields one result per match. -/
private def spaceQueryMatchRules : List PRule :=
  [ { headRel := "spaceQueryMatch"
      headArgs := [.var "pattern", .var "template", .var "result"]
      body := [ .computeMany "spacePatternQuery"
                  [.var "pattern", .var "template"] "result" ]
      clauseName := some "spaceQueryMatch_query" } ]

/-- `spaceQueryNoMatch(pattern)`:
    Predicate: no space atom matches pattern. -/
private def spaceQueryNoMatchRules : List PRule :=
  [ { headRel := "spaceQueryNoMatch"
      headArgs := [.var "pattern"]
      body := [ .compute "checkSpaceNoMatch" [.var "pattern"] "_" ]
      clauseName := some "spaceQueryNoMatch_check" } ]

/-- `parseUnifyCall(atom, target, pattern, success, failure)`:
    Recognizes `(unify target pattern success failure)`.
    Extracts all four arguments. -/
private def parseUnifyCallRules : List PRule :=
  [ { headRel := "parseUnifyCall"
      headArgs := [.var "atom", .var "target", .var "pattern",
                   .var "success", .var "failure"]
      body := [ .compute "parseUnifyCallArgs" [.var "atom"] "packed"
              , .deconstruct (.var "packed") "ExprCons" ["target", "rest1"]
              , .deconstruct (.var "rest1") "ExprCons" ["pattern", "rest2"]
              , .deconstruct (.var "rest2") "ExprCons" ["success", "failure"] ]
      clauseName := some "parseUnifyCall_check" } ]

/-- `localMatch(target, pattern, success, result)`:
    Single `metta_match(pattern, target)` + `metta_subst(success, bindings)`.
    Returns substituted success template. -/
private def localMatchRules : List PRule :=
  [ { headRel := "localMatch"
      headArgs := [.var "target", .var "pattern",
                   .var "success", .var "result"]
      body := [ .compute "localPatternMatch"
                  [.var "target", .var "pattern", .var "success"] "result" ]
      clauseName := some "localMatch_compute" } ]

/-- `localNoMatch(target, pattern)`:
    Predicate: `metta_match(pattern, target)` returns None. -/
private def localNoMatchRules : List PRule :=
  [ { headRel := "localNoMatch"
      headArgs := [.var "target", .var "pattern"]
      body := [ .compute "checkLocalNoMatch" [.var "target", .var "pattern"] "_" ]
      clauseName := some "localNoMatch_check" } ]

/-- `parseCollapseCall(atom, expr)`:
    Recognizes `(collapse expr)`. Extracts the expression to evaluate. -/
private def parseCollapseCallRules : List PRule :=
  [ { headRel := "parseCollapseCall"
      headArgs := [.var "atom", .var "expr"]
      body := [ .compute "parseCollapseCallArg" [.var "atom"] "expr" ]
      clauseName := some "parseCollapseCall_check" } ]

/-- `collapseBind(expr, ty, packed)`:
    Oracle premise: runs nested `run_transition_graph()` on expr,
    collects all terminal Return(value) states, packs as MeTTa list.
    The Rust evaluator handles the actual nested evaluation. -/
private def collapseBindRules : List PRule :=
  [ { headRel := "collapseBind"
      headArgs := [.var "expr", .var "ty", .var "packed"]
      body := [ .compute "evalCollapseBind"
                  [.var "expr", .var "ty"] "packed" ]
      clauseName := some "collapseBind_oracle" } ]

/-! ## Builtin Functions -/

private def heBuiltins : List BuiltinFn :=
  [ { name := "checkExecutable", arity := 1 }
  , { name := "checkNotExecutable", arity := 1 }
  , { name := "findTypeAnnotation", arity := 2 }
  , { name := "queryEquationsInSpace", arity := 2 }
  , { name := "findApplicableFuncType", arity := 3 }
  , { name := "hasNonFuncTypes", arity := 2 }
  , { name := "checkNoTypeAtAll", arity := 2 }
  , { name := "evalGroundedDispatch", arity := 2 }
  -- Control flow builtins
  , { name := "parseSwitchMinimalCallArgs", arity := 1 }
  , { name := "parseCaseCallArgs", arity := 1 }
  , { name := "parseAssertCallArg", arity := 1 }
  , { name := "selectSwitchTemplate", arity := 2 }
  , { name := "checkIsNotReducible", arity := 1 }
  , { name := "checkIsReducible", arity := 1 }
  , { name := "buildAssertError", arity := 2 }
  -- Minimal instruction builtins
  , { name := "parseSuperposElements", arity := 1 }
  , { name := "checkSuperposeEmpty", arity := 1 }
  , { name := "parseMatchCallArgs", arity := 1 }
  , { name := "spacePatternQuery", arity := 2 }
  , { name := "checkSpaceNoMatch", arity := 1 }
  , { name := "parseUnifyCallArgs", arity := 1 }
  , { name := "localPatternMatch", arity := 3 }
  , { name := "checkLocalNoMatch", arity := 2 }
  , { name := "parseCollapseCallArg", arity := 1 }
  , { name := "evalCollapseBind", arity := 2 }
  ]

private def heAscentHints : List BackendHint :=
  [ { builtinName := "checkExecutable", backend := "ascent"
      template := "is_executable_grounded({0})" }
  , { builtinName := "checkNotExecutable", backend := "ascent"
      template := "is_not_executable_grounded({0})" }
  , { builtinName := "findTypeAnnotation", backend := "ascent"
      template := "find_type_annotation({0}, {1})" }
  , { builtinName := "queryEquationsInSpace", backend := "ascent"
      template := "query_equations_in_space({0}, {1})" }
  , { builtinName := "findApplicableFuncType", backend := "ascent"
      template := "find_applicable_func_type({0}, {1}, &{2})" }
  , { builtinName := "hasNonFuncTypes", backend := "ascent"
      template := "has_non_func_types({0}, {1})" }
  , { builtinName := "checkNoTypeAtAll", backend := "ascent"
      template := "check_no_type_at_all({0}, {1})" }
  , { builtinName := "evalGroundedDispatch", backend := "ascent"
      template := "eval_grounded_dispatch({0}.clone(), {1}.clone())" }
  ]

/-! ## Complete Premise Program -/

/-- The complete premise program for HE MeTTa.

This captures all premise-driven semantics needed by `mettaHE : LanguageDef`.
Backend renderers compile this to executable code (Ascent rules + Rust helpers). -/
def mettaHEPremises : PremiseProgram where
  relations :=
    [ { name := "isEmpty", paramTypes := ["Atom"] }
    , { name := "isError", paramTypes := ["Atom"] }
    , { name := "metaType", paramTypes := ["Atom", "Atom"] }
    , { name := "typeMatchesMetaOrAtom", paramTypes := ["Atom", "Atom"] }
    , { name := "typeNotMatchesMetaOrAtom", paramTypes := ["Atom", "Atom"] }
    , { name := "needsTypeCast", paramTypes := ["Atom", "Atom"] }
    , { name := "needsInterpExpr", paramTypes := ["Atom", "Atom"] }
    , { name := "notExpression", paramTypes := ["Atom"] }
    , { name := "isExecutable", paramTypes := ["Atom"] }
    , { name := "notExecutable", paramTypes := ["Atom"] }
    , { name := "typeOfRaw", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "typeOf", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "typeMismatch", paramTypes := ["Space", "Atom", "Atom", "Atom"] }
    , { name := "funcArgTypes", paramTypes := ["Atom", "Atom"] }
    , { name := "changedToEmpty", paramTypes := ["Atom", "Atom"] }
    , { name := "changedToError", paramTypes := ["Atom", "Atom"] }
    , { name := "eqQueryRaw", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "eqQueryResult", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "eqQueryHas", paramTypes := ["Space", "Atom"] }
    , { name := "noEqQuery", paramTypes := ["Space", "Atom"], hasNegation := true }
    , { name := "groundedCallResult", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "applicableFuncTypeRaw", paramTypes := ["Space", "Atom", "Atom", "Atom"] }
    , { name := "applicableFuncType", paramTypes := ["Space", "Atom", "Atom", "Atom", "Atom"] }
    , { name := "applicableFuncTypeHas", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "needsTupleInterp", paramTypes := ["Space", "Atom", "Atom"] }
    , { name := "noTypeAtAll", paramTypes := ["Space", "Atom"] }
    -- Control flow relations
    , { name := "parseSwitchMinimalCall", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "parseCaseCall", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "parseAssertCall", paramTypes := ["Atom", "Atom"] }
    , { name := "selectSwitchResult", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "isNotReducible", paramTypes := ["Atom"] }
    , { name := "isReducible", paramTypes := ["Atom"] }
    , { name := "assertMatchesTrue", paramTypes := ["Atom"] }
    , { name := "assertNotTrue", paramTypes := ["Atom"] }
    , { name := "mkAssertError", paramTypes := ["Atom", "Atom", "Atom"] }
    -- Minimal instruction relations
    , { name := "parseSuperpose", paramTypes := ["Atom", "Atom"] }
    , { name := "isSuperpose_empty", paramTypes := ["Atom"] }
    , { name := "parseMatchCall", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "spaceQueryMatch", paramTypes := ["Atom", "Atom", "Atom"] }
    , { name := "spaceQueryNoMatch", paramTypes := ["Atom"] }
    , { name := "parseUnifyCall", paramTypes := ["Atom", "Atom", "Atom", "Atom", "Atom"] }
    , { name := "localMatch", paramTypes := ["Atom", "Atom", "Atom", "Atom"] }
    , { name := "localNoMatch", paramTypes := ["Atom", "Atom"] }
    , { name := "parseCollapseCall", paramTypes := ["Atom", "Atom"] }
    , { name := "collapseBind", paramTypes := ["Atom", "Atom", "Atom"] }
    ]
  rules :=
    isEmptyRules
    ++ isErrorRules
    ++ changedToEmptyRules
    ++ changedToErrorRules
    ++ metaTypeRules
    ++ typeMatchesMetaOrAtomRules
    ++ typeNotMatchesMetaOrAtomRules
    ++ needsTypeCastRules
    ++ needsInterpExprRules
    ++ notExpressionRules
    ++ isExecutableRules
    ++ notExecutableRules
    ++ typeOfRawRules
    ++ typeOfRules
    ++ typeMismatchRules
    ++ funcArgTypesRules
    ++ eqQueryRawRules
    ++ eqQueryResultRules
    ++ eqQueryHasRules
    ++ noEqQueryRules
    ++ groundedCallResultRules
    ++ applicableFuncTypeRawRules
    ++ applicableFuncTypeRules
    ++ applicableFuncTypeHasRules
    ++ needsTupleInterpRules
    ++ noTypeAtAllRules
    -- Control flow rules
    ++ parseSwitchMinimalCallRules
    ++ parseCaseCallRules
    ++ parseAssertCallRules
    ++ selectSwitchResultRules
    ++ isNotReducibleRules
    ++ isReducibleRules
    ++ assertMatchesTrueRules
    ++ assertNotTrueRules
    ++ mkAssertErrorRules
    -- Minimal instruction rules
    ++ parseSuperoseRules
    ++ isSuperpose_emptyRules
    ++ parseMatchCallRules
    ++ spaceQueryMatchRules
    ++ spaceQueryNoMatchRules
    ++ parseUnifyCallRules
    ++ localMatchRules
    ++ localNoMatchRules
    ++ parseCollapseCallRules
    ++ collapseBindRules
  builtins := heBuiltins
  backendHints := heAscentHints
  coreGroundEvalRelation := none  -- HE does not use a fast-path evaluator
  stateConstructor := some "State"

/-! ## Smoke Checks -/

#eval do
  let prog := mettaHEPremises
  IO.println s!"HE Premises: {prog.relations.length} relations, {prog.rules.length} rules, {prog.builtins.length} builtins"

#eval do
  let wf := mettaHEPremises.wellFormed
  IO.println s!"mettaHEPremises well-formed: {wf}"

#eval do
  match mettaHEPremises.stratify with
  | some strata =>
      IO.println "mettaHEPremises stratification:"
      for (rel, stratum) in strata do
        IO.println s!"  stratum {stratum}: {rel}"
  | none =>
      IO.println "ERROR: mettaHEPremises is NOT stratifiable!"

end Mettapedia.Languages.MeTTa.HE.Premises
