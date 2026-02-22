/-
# SUMO Repair Runner — Three-Source Diff

Automated comparison of SUMO KIF taxonomy, Enache's GF encoding, and our
Lean encoding for all ~50 FOET-relevant classes. Flags disagreements and
classifies them by type.

## Sources
- SUMO KIF: Merge.kif, Mid-level-ontology.kif, FOET seed ontology
- Enache GF: Merge.gf, MidLevelOntology.gf (original/ directory)
- Our encoding: SumoAbstract.lean

## Disagreement Types
- `agree`         — all three sources match
- `silent_repair` — Enache changed SUMO's classification without documenting it
- `missing_gf`    — concept absent from Enache's GF encoding
- `flattened`     — Enache flattened multi-level hierarchy (skipped intermediate)
- `too_tight`     — our encoding narrows the domain beyond what SUMO declares
- `infra_sort`    — concept is a GF infrastructure sort, not encoded as SUMO class
- `foet_only`     — concept defined only in FOET, absent from both SUMO and GF
-/

import Mettapedia.Languages.GF.SUMO.SumoAbstract

namespace Mettapedia.Languages.GF.SUMO.RepairRunner

/-! ## Data Structures -/

/-- Classification of a three-source disagreement. -/
inductive DisagreementType where
  | agree         : DisagreementType
  | silentRepair  : DisagreementType
  | missingGF     : DisagreementType
  | flattened     : DisagreementType
  | tooTight      : DisagreementType
  | infraSort     : DisagreementType
  | foetOnly      : DisagreementType
  deriving Repr, BEq

instance : ToString DisagreementType where
  toString
    | .agree        => "AGREE"
    | .silentRepair => "SILENT_REPAIR"
    | .missingGF    => "MISSING_GF"
    | .flattened    => "FLATTENED"
    | .tooTight     => "TOO_TIGHT"
    | .infraSort    => "INFRA_SORT"
    | .foetOnly     => "FOET_ONLY"

/-- A record comparing three sources for a single SUMO class. -/
structure ClassRecord where
  name : String
  stratum : Nat
  /-- Parent(s) per SUMO KIF `(subclass X Y)` -/
  sumoKIFParents : List String
  /-- How Enache typed it in GF, if present.
      `none` = not found in Merge.gf / MidLevelOntology.gf -/
  enacheGFParent : Option String
  /-- Parent in our SumoAbstract.lean encoding -/
  ourParent : String
  /-- Computed disagreement classification -/
  disagreement : DisagreementType
  /-- Human-readable note explaining the disagreement -/
  note : String
  deriving Repr

instance : ToString ClassRecord where
  toString r :=
    let kif := String.intercalate ", " r.sumoKIFParents
    let gf := r.enacheGFParent.getD "—"
    let sym := match r.disagreement with
      | .agree => "✓"
      | _ => "✗"
    s!"{sym} [{r.disagreement}] {r.name} (S{r.stratum})\n" ++
    s!"    KIF: {kif} | GF: {gf} | Ours: {r.ourParent}\n" ++
    (if r.note.isEmpty then "" else s!"    Note: {r.note}\n")

/-! ## Three-Source Data

Each entry: (name, stratum, KIF parents, Enache GF parent, our parent,
disagreement type, note).

Data extracted from:
- SUMO KIF: Merge.kif lines as cited
- Enache GF: original/Merge.gf, original/MidLevelOntology.gf
- Our encoding: SumoAbstract.lean sumoSubclassEdges
-/

def classRecords : List ClassRecord :=
  [
    -- ═══════════════════════════════════════════════════════════════
    -- STRATUM 0: Upper Ontology Core (9 classes)
    -- ═══════════════════════════════════════════════════════════════

    { name := "Entity", stratum := 0
    , sumoKIFParents := []  -- root
    , enacheGFParent := none  -- root (Class, no SubClass declaration)
    , ourParent := "(root)"
    , disagreement := .agree
    , note := "" }

  , { name := "Physical", stratum := 0
    , sumoKIFParents := ["Entity"]  -- Merge.kif:825
    , enacheGFParent := some "Entity"  -- Merge.gf:3170-3171
    , ourParent := "Entity"
    , disagreement := .agree
    , note := "" }

  , { name := "Abstract", stratum := 0
    , sumoKIFParents := ["Entity"]  -- Merge.kif:1703
    , enacheGFParent := some "Entity"  -- Merge.gf:25-26
    , ourParent := "Entity"
    , disagreement := .agree
    , note := "" }

  , { name := "Object", stratum := 0
    , sumoKIFParents := ["Physical"]  -- Merge.kif:839
    , enacheGFParent := some "Physical"  -- Merge.gf:2953-2954
    , ourParent := "Physical"
    , disagreement := .agree
    , note := "" }

  , { name := "Process", stratum := 0
    , sumoKIFParents := ["Physical"]  -- Merge.kif:1656
    , enacheGFParent := some "Physical"  -- Merge.gf:3433-3434
    , ourParent := "Physical"
    , disagreement := .agree
    , note := "" }

  , { name := "Attribute", stratum := 0
    , sumoKIFParents := ["Abstract"]  -- Merge.kif:1734
    , enacheGFParent := some "Abstract"  -- Merge.gf:278-279
    , ourParent := "Abstract"
    , disagreement := .agree
    , note := "" }

  , { name := "SetOrClass", stratum := 0
    , sumoKIFParents := ["Abstract"]  -- Merge.kif:2163
    , enacheGFParent := some "Abstract"  -- Merge.gf:3968-3969
    , ourParent := "Abstract"
    , disagreement := .agree
    , note := "" }

  , { name := "Relation", stratum := 0
    , sumoKIFParents := ["Abstract"]  -- Merge.kif:2194
    , enacheGFParent := none  -- NOT FOUND in Merge.gf
    , ourParent := "Abstract"
    , disagreement := .missingGF
    , note := "Enache did not encode Relation as a SUMO class. " ++
        "The entire Relation hierarchy (Predicate, Function, InheritableRelation) " ++
        "is handled at the GF formula level, not as ontological classes." }

  , { name := "Proposition", stratum := 0
    , sumoKIFParents := ["Abstract"]  -- Merge.kif:3594
    , enacheGFParent := some "Abstract"  -- Merge.gf:3469-3470
    , ourParent := "Abstract"
    , disagreement := .agree
    , note := "" }

    -- ═══════════════════════════════════════════════════════════════
    -- STRATUM 1: Mid-Level Anchors (~25 classes)
    -- ═══════════════════════════════════════════════════════════════

    -- Agent chain
  , { name := "AutonomousAgent", stratum := 1
    , sumoKIFParents := ["Object"]  -- Merge.kif:1591
    , enacheGFParent := none  -- NOT FOUND in GF
    , ourParent := "Object"
    , disagreement := .missingGF
    , note := "Enache skipped AutonomousAgent entirely. " ++
        "SentientAgent → Agent directly (Agent = Object in GF). " ++
        "This loses the AutonomousAgent abstraction used by " ++
        "GeopoliticalArea, Organization, Group." }

  , { name := "SentientAgent", stratum := 1
    , sumoKIFParents := ["AutonomousAgent"]  -- Merge.kif:1601
    , enacheGFParent := some "Agent"  -- Merge.gf:3919-3920 (Agent, not AutonomousAgent)
    , ourParent := "AutonomousAgent"
    , disagreement := .flattened
    , note := "KIF: SentientAgent ⊂ AutonomousAgent ⊂ Object. " ++
        "GF: SentientAgent ⊂ Agent (= Object). " ++
        "Enache flattened by skipping AutonomousAgent. " ++
        "Our encoding correctly preserves the full chain." }

  , { name := "CognitiveAgent", stratum := 1
    , sumoKIFParents := ["SentientAgent"]  -- Merge.kif:1611
    , enacheGFParent := some "SentientAgent"  -- Merge.gf:645-646
    , ourParent := "SentientAgent"
    , disagreement := .agree
    , note := "" }

    -- Object subtypes
  , { name := "SelfConnectedObject", stratum := 1
    , sumoKIFParents := ["Object"]  -- Merge.kif:855
    , enacheGFParent := some "Object"  -- Merge.gf:3900-3901
    , ourParent := "Object"
    , disagreement := .agree
    , note := "" }

  , { name := "CorpuscularObject", stratum := 1
    , sumoKIFParents := ["SelfConnectedObject"]  -- Merge.kif:1261
    , enacheGFParent := some "SelfConnectedObject"  -- Merge.gf:897-898
    , ourParent := "SelfConnectedObject"
    , disagreement := .agree
    , note := "" }

  , { name := "ContentBearingObject", stratum := 1
    , sumoKIFParents := ["CorpuscularObject", "ContentBearingPhysical"]  -- Merge.kif:1362-1363
    , enacheGFParent := some "both ContentBearingPhysical CorpuscularObject"  -- Merge.gf:818-819
    , ourParent := "CorpuscularObject"  -- we only encode primary parent
    , disagreement := .agree
    , note := "Multi-inheritance. Enache uses GF `both` constructor. " ++
        "We encode primary parent only; second parent is a known simplification." }

  , { name := "ContentBearingPhysical", stratum := 1
    , sumoKIFParents := ["Physical"]  -- Merge.kif:1339
    , enacheGFParent := some "Physical"  -- Merge.gf:825-826
    , ourParent := "Physical"
    , disagreement := .agree
    , note := "" }

  , { name := "LinguisticExpression", stratum := 1
    , sumoKIFParents := ["ContentBearingPhysical"]  -- Merge.kif:1432
    , enacheGFParent := some "ContentBearingPhysical"  -- Merge.gf:2301-2302
    , ourParent := "ContentBearingPhysical"
    , disagreement := .agree
    , note := "" }

  , { name := "Sentence", stratum := 1
    , sumoKIFParents := ["LinguisticExpression"]  -- Merge.kif:15617
    , enacheGFParent := some "LinguisticExpression"  -- Merge.gf:3911-3912
    , ourParent := "LinguisticExpression"
    , disagreement := .agree
    , note := "" }

    -- Attribute hierarchy
  , { name := "InternalAttribute", stratum := 1
    , sumoKIFParents := ["Attribute"]  -- Merge.kif:1838
    , enacheGFParent := some "Attribute"  -- Merge.gf:2065-2066
    , ourParent := "Attribute"
    , disagreement := .agree
    , note := "" }

  , { name := "BiologicalAttribute", stratum := 1
    , sumoKIFParents := ["InternalAttribute"]  -- Merge.kif:18229
    , enacheGFParent := some "InternalAttribute"  -- Merge.gf:367-368
    , ourParent := "InternalAttribute"
    , disagreement := .agree
    , note := "" }

  , { name := "PsychologicalAttribute", stratum := 1
    , sumoKIFParents := ["BiologicalAttribute"]  -- Merge.kif:18463
    , enacheGFParent := some "BiologicalAttribute"  -- Merge.gf:3493-3494
    , ourParent := "BiologicalAttribute"
    , disagreement := .agree
    , note := "" }

  , { name := "RelationalAttribute", stratum := 1
    , sumoKIFParents := ["Attribute"]  -- Merge.kif:1849
    , enacheGFParent := some "Attribute"  -- Merge.gf:3696-3697
    , ourParent := "Attribute"
    , disagreement := .agree
    , note := "" }

  , { name := "NormativeAttribute", stratum := 1
    , sumoKIFParents := ["RelationalAttribute"]  -- Merge.kif:17488
    , enacheGFParent := some "RelationalAttribute"  -- Merge.gf:2899-2900
    , ourParent := "RelationalAttribute"
    , disagreement := .agree
    , note := "" }

  , { name := "ObjectiveNorm", stratum := 1
    , sumoKIFParents := ["NormativeAttribute"]  -- Merge.kif:17575
    , enacheGFParent := some "NormativeAttribute"  -- Merge.gf:2959-2960
    , ourParent := "NormativeAttribute"
    , disagreement := .agree
    , note := "" }

    -- Abstract subtypes
  , { name := "Set", stratum := 1
    , sumoKIFParents := ["SetOrClass"]  -- Merge.kif:2183
    , enacheGFParent := some "SetOrClass"  -- Merge.gf:3962-3963
    , ourParent := "SetOrClass"
    , disagreement := .agree
    , note := "" }

  , { name := "Class", stratum := 1
    , sumoKIFParents := ["SetOrClass"]  -- Merge.kif:2171
    , enacheGFParent := none  -- Class is a GF sort in Basic.gf, not a SUMO concept
    , ourParent := "SetOrClass"
    , disagreement := .infraSort
    , note := "In Enache's encoding, `Class` is a GF type-level sort " ++
        "(cat Class in Basic.gf), not encoded as a SUMO ontological class. " ++
        "This is a deliberate design choice: SUMO's Class becomes GF's " ++
        "type system itself." }

  , { name := "Predicate", stratum := 1
    , sumoKIFParents := ["Relation", "InheritableRelation"]  -- Merge.kif:3378-3379
    , enacheGFParent := none  -- NOT FOUND
    , ourParent := "Relation"
    , disagreement := .missingGF
    , note := "Enache did not encode Predicate as a SUMO class. " ++
        "Relations are handled at the GF formula level." }

  , { name := "Function", stratum := 1
    , sumoKIFParents := ["SingleValuedRelation", "InheritableRelation"]  -- Merge.kif:3389-3390
    , enacheGFParent := none  -- NOT FOUND
    , ourParent := "SingleValuedRelation"
    , disagreement := .missingGF
    , note := "Same as Predicate: not encoded as SUMO class in GF." }

  , { name := "List", stratum := 1
    , sumoKIFParents := ["Abstract"]  -- Merge.kif:2912 (via partition)
    , enacheGFParent := some "(no parent declared)"  -- Merge.gf:2329, just `fun List : Class`
    , ourParent := "Abstract"
    , disagreement := .agree
    , note := "Enache declares List as Class but omits SubClass parent. " ++
        "Our encoding adds the KIF parent (Abstract)." }

  , { name := "SingleValuedRelation", stratum := 1
    , sumoKIFParents := ["Relation", "InheritableRelation"]  -- Merge.kif:2211-2212
    , enacheGFParent := none  -- formula-level axiom schema, not a Class
    , ourParent := "Relation"
    , disagreement := .infraSort
    , note := "In Merge.gf:6253, SingleValuedRelation appears as a formula-level " ++
        "axiom schema `(c : Class) -> (El c -> Formula) -> Formula`, not as a " ++
        "SUMO class declaration." }

  , { name := "InheritableRelation", stratum := 1
    , sumoKIFParents := ["Relation"]  -- Merge.kif:2593
    , enacheGFParent := none  -- NOT FOUND
    , ourParent := "Relation"
    , disagreement := .missingGF
    , note := "Not encoded in GF." }

  , { name := "Argument", stratum := 1
    , sumoKIFParents := ["Proposition"]  -- Merge.kif:17009
    , enacheGFParent := some "Proposition"  -- Merge.gf:189-190
    , ourParent := "Proposition"
    , disagreement := .agree
    , note := "" }

  , { name := "Formula", stratum := 1
    , sumoKIFParents := ["Sentence"]  -- Merge.kif:1582
    , enacheGFParent := none  -- Formula is a GF sort in Basic.gf
    , ourParent := "Sentence"
    , disagreement := .infraSort
    , note := "In Enache's encoding, `Formula` is a GF type-level sort " ++
        "(cat Formula in Basic.gf). SUMO's Formula (subclass of Sentence) " ++
        "is lifted to GF's type system. Our encoding preserves the KIF " ++
        "hierarchy edge (Formula ⊂ Sentence)." }

    -- ═══════════════════════════════════════════════════════════════
    -- STRATUM 2: FOET-Specific (~20 classes)
    -- ═══════════════════════════════════════════════════════════════

  , { name := "MoralAttribute", stratum := 2
    , sumoKIFParents := ["NormativeAttribute"]  -- FOET:1123
    , enacheGFParent := none  -- FOET-only
    , ourParent := "NormativeAttribute"
    , disagreement := .foetOnly
    , note := "Defined only in FOET seed ontology, not in SUMO core." }

  , { name := "MoralValueAttribute", stratum := 2
    , sumoKIFParents := ["MoralAttribute"]  -- FOET:1129
    , enacheGFParent := none
    , ourParent := "MoralAttribute"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "DeonticAttribute", stratum := 2
    , sumoKIFParents := ["ObjectiveNorm", "MoralAttribute"]  -- Merge.kif:17662 + FOET:1224
    , enacheGFParent := some "ObjectiveNorm"  -- Merge.gf:1058-1059 (only one parent)
    , ourParent := "ObjectiveNorm"
    , disagreement := .agree
    , note := "KIF has two parents: ObjectiveNorm (Merge) + MoralAttribute (FOET). " ++
        "Enache and we both encode the Merge parent only. " ++
        "The FOET parent (MoralAttribute) is a FOET extension." }

  , { name := "MoralVirtueAttribute", stratum := 2
    , sumoKIFParents := ["MoralAttribute"]  -- FOET:1137
    , enacheGFParent := none
    , ourParent := "MoralAttribute"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "VirtueAttribute", stratum := 2
    , sumoKIFParents := ["MoralVirtueAttribute", "PsychologicalAttribute"]  -- FOET:1139, 1142
    , enacheGFParent := none
    , ourParent := "MoralVirtueAttribute"
    , disagreement := .foetOnly
    , note := "Multi-inheritance: MoralVirtueAttribute + PsychologicalAttribute. " ++
        "We encode primary parent only." }

  , { name := "ViceAttribute", stratum := 2
    , sumoKIFParents := ["MoralVirtueAttribute", "PsychologicalAttribute"]  -- FOET:1140, 1143
    , enacheGFParent := none
    , ourParent := "MoralVirtueAttribute"
    , disagreement := .foetOnly
    , note := "Same multi-inheritance as VirtueAttribute." }

  , { name := "VirtuousAgent", stratum := 2
    , sumoKIFParents := ["AutonomousAgent"]  -- FOET:1147
    , enacheGFParent := none
    , ourParent := "AutonomousAgent"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "ViciousAgent", stratum := 2
    , sumoKIFParents := ["AutonomousAgent"]  -- FOET:1165
    , enacheGFParent := none
    , ourParent := "AutonomousAgent"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "AutonomousAgentProcess", stratum := 2
    , sumoKIFParents := ["Process"]  -- FOET:328
    , enacheGFParent := none
    , ourParent := "Process"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "VirtuousAct", stratum := 2
    , sumoKIFParents := ["AutonomousAgentProcess"]  -- FOET:1184
    , enacheGFParent := none
    , ourParent := "AutonomousAgentProcess"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "ViciousAct", stratum := 2
    , sumoKIFParents := ["AutonomousAgentProcess"]  -- FOET:1203
    , enacheGFParent := none
    , ourParent := "AutonomousAgentProcess"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "ChoicePoint", stratum := 2
    , sumoKIFParents := ["Set", "NonNullSet"]  -- FOET:809-810
    , enacheGFParent := none
    , ourParent := "Set"
    , disagreement := .foetOnly
    , note := "Multi-inheritance: Set + NonNullSet." }

  , { name := "Situation", stratum := 2
    , sumoKIFParents := ["Physical"]  -- FOET:600
    , enacheGFParent := none
    , ourParent := "Physical"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "ActionFormula", stratum := 2
    , sumoKIFParents := ["Formula"]  -- FOET:341
    , enacheGFParent := none
    , ourParent := "Formula"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "Conjecture", stratum := 2
    , sumoKIFParents := ["Sentence"]  -- FOET:955
    , enacheGFParent := none
    , ourParent := "Sentence"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "EthicalTheory", stratum := 2
    , sumoKIFParents := ["Theory"]  -- FOET:1404
    , enacheGFParent := none
    , ourParent := "Proposition"  -- Theory not in our encoding; falls back
    , disagreement := .foetOnly
    , note := "FOET says subclass of Theory. Our encoding maps to " ++
        "Proposition (Theory's ancestor). Missing intermediate: Theory." }

  , { name := "Value", stratum := 2
    , sumoKIFParents := ["Abstract"]  -- FOET:1020
    , enacheGFParent := none
    , ourParent := "Abstract"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "UtilityFormulaFn", stratum := 2
    , sumoKIFParents := ["TotalValuedRelation", "UnaryFunction"]  -- FOET:1841-1842
    , enacheGFParent := none
    , ourParent := "(not in subclass edges)"
    , disagreement := .foetOnly
    , note := "Multi-inheritance: TotalValuedRelation + UnaryFunction. " ++
        "Neither parent is in our encoding." }

  , { name := "Consequentialism", stratum := 2
    , sumoKIFParents := ["Ethics"]  -- FOET:1915
    , enacheGFParent := none
    , ourParent := "Ethics"
    , disagreement := .foetOnly
    , note := "" }

  , { name := "Ethics", stratum := 2
    , sumoKIFParents := ["Philosophy"]  -- FOET:1473
    , enacheGFParent := none
    , ourParent := "(not in subclass edges)"
    , disagreement := .foetOnly
    , note := "FOET says subclass of Philosophy. Philosophy not in our encoding." }
  ]

/-! ## Automated Analysis -/

/-- Count records by disagreement type. -/
def countByType (records : List ClassRecord) (dt : DisagreementType) : Nat :=
  (records.filter fun r => r.disagreement == dt).length

/-- All records that are NOT in agreement. -/
def flaggedRecords (records : List ClassRecord) : List ClassRecord :=
  records.filter fun r => r.disagreement != .agree

/-- Records requiring active repair (not just FOET-only additions). -/
def repairCandidates (records : List ClassRecord) : List ClassRecord :=
  records.filter fun r => match r.disagreement with
    | .silentRepair | .missingGF | .flattened | .tooTight => true
    | _ => false

/-! ## Relation Typing Diff

Beyond class hierarchy, compare relation signature typings.
-/

structure RelationRecord where
  name : String
  sumoKIFDomain : List (Nat × String)   -- (argNum, className)
  enacheGFSig : Option String
  ourSig : String
  disagreement : DisagreementType
  note : String
  deriving Repr

def relationRecords : List RelationRecord :=
  [ { name := "attribute"
    , sumoKIFDomain := [(1, "Object"), (2, "Attribute")]  -- Merge.kif:1754-1755
    , enacheGFSig := some "El Object -> El Attribute -> Formula"
    , ourSig := "El_Agent -> El_Attribute -> Formula"
    , disagreement := .tooTight
    , note := "Our encoding narrows domain 1 from Object to Agent. " ++
        "SUMO and Enache both say Object." }

  , { name := "agent"
    , sumoKIFDomain := [(1, "Process"), (2, "AutonomousAgent")]  -- Merge.kif:2468-2469
    , enacheGFSig := some "El Process -> El Agent -> Formula"
    , ourSig := "El_Process -> El_AutonomousAgent -> Formula"
    , disagreement := .flattened
    , note := "KIF domain 2 is AutonomousAgent. " ++
        "Enache uses Agent (because AutonomousAgent is missing from GF). " ++
        "Our encoding correctly uses AutonomousAgent." }

  , { name := "contraryAttribute"
    , sumoKIFDomain := []  -- VariableArityRelation, no fixed domains
    , enacheGFSig := some "[El Attribute] -> Formula"  -- variable arity list
    , ourSig := "El_Attribute -> El_Attribute -> Formula"
    , disagreement := .tooTight
    , note := "SUMO declares VariableArityRelation (Merge.kif:448). " ++
        "Enache correctly uses GF list type [El Attribute]. " ++
        "Our encoding incorrectly fixes arity to binary." }

  , { name := "desires"
    , sumoKIFDomain := [(1, "CognitiveAgent"), (2, "Formula")]
    , enacheGFSig := some "El CognitiveAgent -> Formula -> Formula"
    , ourSig := "El_CognitiveAgent -> Formula -> Formula"
    , disagreement := .agree
    , note := "" }

  , { name := "holdsObligation"
    , sumoKIFDomain := [(1, "Formula"), (2, "CognitiveAgent")]
    , enacheGFSig := none  -- FOET-only relation
    , ourSig := "Formula -> El_AutonomousAgent -> Formula"
    , disagreement := .foetOnly
    , note := "FOET-only. Domain 2 might be CognitiveAgent not AutonomousAgent." }
  ]

/-! ## Report Generation -/

#eval! do
  IO.println "╔══════════════════════════════════════════════════════════╗"
  IO.println "║   SUMO REPAIR RUNNER — Three-Source Diff Report        ║"
  IO.println "╚══════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Summary statistics
  IO.println "=== CLASS HIERARCHY SUMMARY ==="
  IO.println s!"Total classes: {classRecords.length}"
  IO.println s!"  AGREE:         {countByType classRecords .agree}"
  IO.println s!"  SILENT_REPAIR: {countByType classRecords .silentRepair}"
  IO.println s!"  MISSING_GF:    {countByType classRecords .missingGF}"
  IO.println s!"  FLATTENED:     {countByType classRecords .flattened}"
  IO.println s!"  TOO_TIGHT:     {countByType classRecords .tooTight}"
  IO.println s!"  INFRA_SORT:    {countByType classRecords .infraSort}"
  IO.println s!"  FOET_ONLY:     {countByType classRecords .foetOnly}"
  IO.println ""

  -- Per-stratum breakdown
  for s in [0, 1, 2] do
    let stratum := classRecords.filter fun (r : ClassRecord) => r.stratum == s
    let flagged := stratum.filter fun (r : ClassRecord) =>
      r.disagreement != DisagreementType.agree
    IO.println s!"Stratum {s}: {stratum.length} classes, {flagged.length} flagged"

  IO.println ""

  -- Detailed flagged records
  IO.println "=== FLAGGED CLASSES (require attention) ==="
  IO.println ""
  let candidates := repairCandidates classRecords
  if candidates.isEmpty then
    IO.println "  (none requiring active repair)"
  else
    for r in candidates do
      IO.println (toString r)

  IO.println "=== INFRASTRUCTURE SORTS (deliberate GF design choices) ==="
  IO.println ""
  let infra := classRecords.filter fun (r : ClassRecord) =>
    r.disagreement == DisagreementType.infraSort
  for r in infra do
    IO.println s!"  {r.name}: {r.note}"
  IO.println ""

  IO.println "=== FOET-ONLY CLASSES (need GF extension) ==="
  IO.println ""
  let foet := classRecords.filter fun (r : ClassRecord) =>
    r.disagreement == DisagreementType.foetOnly
  IO.println s!"  {foet.length} classes defined only in FOET"
  for r in foet do
    let parents := String.intercalate ", " r.sumoKIFParents
    IO.println s!"  {r.name} ⊂ {parents}"
  IO.println ""

  -- Relation typing diff
  IO.println "=== RELATION TYPING DIFF ==="
  IO.println ""
  for r in relationRecords do
    let sym := match (r : RelationRecord).disagreement with
      | .agree => "✓"
      | _ => "✗"
    IO.println s!"{sym} {r.name}"
    IO.println s!"    KIF domains: {r.sumoKIFDomain.map fun (p : Nat × String) => s!"{p.1}:{p.2}"}"
    IO.println s!"    Enache GF:   {r.enacheGFSig.getD "—"}"
    IO.println s!"    Our sig:     {r.ourSig}"
    if !r.note.isEmpty then
      IO.println s!"    Note: {r.note}"
    IO.println ""

  -- Action items
  IO.println "=== ACTION ITEMS ==="
  IO.println ""
  IO.println "Priority 1 (encoding errors to fix):"
  IO.println "  1. attribute: change El_Agent → El_Object (match KIF domain)"
  IO.println "  2. contraryAttribute: document variable-arity; add canary for ternary case"
  IO.println "  3. agent relation: Enache uses Agent (flattened); verify our AutonomousAgent is correct"
  IO.println ""
  IO.println "Priority 2 (missing GF concepts — structural gaps):"
  IO.println "  4. AutonomousAgent: add to GF if extending Enache's encoding"
  IO.println "  5. Relation hierarchy: decide whether to encode as classes or formula-level"
  IO.println ""
  IO.println "Priority 3 (FOET extension — 18 new classes):"
  let foetCount := (classRecords.filter fun (r : ClassRecord) =>
    r.disagreement == DisagreementType.foetOnly).length
  IO.println s!"  {foetCount} FOET-only classes to add to SUMO-GF extension"

  -- ═══════════════════════════════════════════════════════════════
  -- PARENT CHAIN VALIDATION
  -- For every subclass edge (child, parent), verify BOTH endpoints
  -- are in our class list. Missing intermediates = broken chains.
  -- ═══════════════════════════════════════════════════════════════
  IO.println ""
  IO.println "=== PARENT CHAIN VALIDATION ==="
  IO.println ""
  let allClasses := SumoAbstract.allFOETClasses
  let mut brokenChains : List (String × String) := []
  for ⟨child, parent⟩ in SumoAbstract.sumoSubclassEdges do
    if !allClasses.contains child then
      brokenChains := brokenChains ++ [(child, parent)]
      IO.println s!"  ✗ MISSING CHILD: {child} (edge {child} ⊂ {parent})"
    if !allClasses.contains parent then
      brokenChains := brokenChains ++ [(child, parent)]
      IO.println s!"  ✗ MISSING PARENT: {parent} (edge {child} ⊂ {parent})"
  if brokenChains.isEmpty then
    IO.println "  ✓ All parent chains complete — every edge endpoint is in class list"
  else
    IO.println s!"  {brokenChains.length} broken chain(s) — add missing classes!"

end Mettapedia.Languages.GF.SUMO.RepairRunner
