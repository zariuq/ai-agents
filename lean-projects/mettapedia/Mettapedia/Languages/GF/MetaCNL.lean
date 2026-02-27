/-
# Meta CNL — Cross-cutting Patterns

Controlled Natural Language for definitions, examples, comparisons,
and other cross-cutting patterns used across all CNL modules.

Shared across Phases A-D of the GF-aligned English plan.
-/

namespace Mettapedia.Languages.GF.MetaCNL

/-! ## Definitions -/

/-- A definitional statement: "X is defined as Y" -/
structure Definition where
  term : String
  meaning : String
  deriving DecidableEq, Repr, Inhabited

/-! ## Examples -/

/-- An illustrative example with optional label -/
inductive Example where
  | positive (concept : String) (instance_ : String)
  | negative (concept : String) (nonInstance : String)
  | neutral (text : String)
  deriving DecidableEq, Repr, Inhabited

/-! ## Comparisons -/

/-- A comparison between two items along an aspect -/
structure Comparison where
  itemA : String
  itemB : String
  aspect : String
  deriving DecidableEq, Repr, Inhabited

/-! ## Lists -/

/-- A structured list with optional title -/
structure ItemList where
  title : String := ""
  items : List String
  deriving DecidableEq, Repr, Inhabited

/-! ## Meta Statements -/

/-- Cross-cutting meta-statement -/
inductive MetaStmt where
  | define (d : Definition)
  | example_ (e : Example)
  | compare (c : Comparison)
  | list_ (l : ItemList)
  | note (text : String)
  deriving DecidableEq, Repr, Inhabited

/-! ## English Linearization -/

def linDefinition (d : Definition) : String :=
  d.term ++ " is defined as " ++ d.meaning

def linExample : Example → String
  | .positive concept inst => "for example, " ++ inst ++ " is a " ++ concept
  | .negative concept non => "for example, " ++ non ++ " is not a " ++ concept
  | .neutral text => "for example, " ++ text

def linComparison (c : Comparison) : String :=
  c.itemA ++ " vs " ++ c.itemB ++ " in terms of " ++ c.aspect

def linItemList (l : ItemList) : String :=
  let header := if l.title.isEmpty then "" else l.title ++ ": "
  let rec go : List String → Nat → List String
    | [], _ => []
    | item :: rest, n => (toString n ++ ". " ++ item) :: go rest (n + 1)
  header ++ "\n".intercalate (go l.items 1)

def linMetaStmt : MetaStmt → String
  | .define d => linDefinition d
  | .example_ e => linExample e
  | .compare c => linComparison c
  | .list_ l => linItemList l
  | .note text => "note: " ++ text

/-! ## Determinism -/

theorem linMetaStmt_deterministic (s : MetaStmt) :
    linMetaStmt s = linMetaStmt s := rfl

/-! ## Test Examples -/

-- Example 1: Definition
#eval linDefinition { term := "CNL", meaning := "a controlled natural language with formal semantics" }

-- Example 2: Positive example
#eval linExample (.positive "subclass relation" "Pain is a subclass of StateOfMind")

-- Example 3: Negative example
#eval linExample (.negative "subclass relation" "Object is a subclass of Process")

-- Example 4: Comparison
#eval linComparison { itemA := "ACE", itemB := "GF", aspect := "syntactic unambiguity" }

-- Example 5: Item list
#eval linItemList { title := "CNL modules", items := [
  "OntologyCNL — ontology declarations",
  "PolicyProcessCNL — directives and workflows",
  "ReportCNL — progress reports",
  "CommentCNL — code annotations",
  "PaperCNL — academic prose"
]}

-- Example 6: Meta statement
#eval linMetaStmt (.note "all linearizations are deterministic by construction")

end Mettapedia.Languages.GF.MetaCNL
