import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Hintikka

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Paper-facing abstract choice of eta-normal representative for closed formulas. -/
structure EtaNormalizer (Const : Ty Base → Type v) where
  nf : ClosedFormula Const → ClosedFormula Const
  betaEtaEq_nf :
    ∀ φ : ClosedFormula Const,
      BetaEtaEq (Base := Base) (Const := Const) φ (nf φ)

/-- A signed forcing statement `B_p ⊩ A` from Section 5.1. -/
structure KSignedFormula (K : Type w) (Const : Ty Base → Type v) where
  sign : Sign
  world : K
  formula : ClosedFormula Const

namespace KSignedFormula

variable {K : Type w}

/-- Polarity reversal on paper-facing signed forcing statements. -/
def flip (sf : KSignedFormula K Const) : KSignedFormula K Const :=
  { sf with sign := sf.sign.flip }

/-- Constructor for positive forcing statements. -/
def trueAt (p : K) (φ : ClosedFormula Const) : KSignedFormula K Const :=
  ⟨.trueE, p, φ⟩

/-- Constructor for negative forcing statements. -/
def falseAt (p : K) (φ : ClosedFormula Const) : KSignedFormula K Const :=
  ⟨.falseE, p, φ⟩

@[simp] theorem flip_flip (sf : KSignedFormula K Const) : sf.flip.flip = sf := by
  cases sf
  simp [flip, Sign.flip_flip]

@[simp] theorem trueAt_sign (p : K) (φ : ClosedFormula Const) :
    (trueAt (Const := Const) p φ).sign = .trueE := rfl

@[simp] theorem falseAt_sign (p : K) (φ : ClosedFormula Const) :
    (falseAt (Const := Const) p φ).sign = .falseE := rfl

end KSignedFormula

/-- Finite paper-facing Hintikka paths. Their underlying sets are obtained by
ignoring multiplicity and order. -/
abbrev KHintikkaPath (K : Type w) (Const : Ty Base → Type v) :=
  List (KSignedFormula K Const)

namespace KHintikkaPath

variable {K : Type w} [Preorder K]

/-- The worlds that actually occur on a finite Hintikka path. -/
def WorldOccurs (π : KHintikkaPath K Const) (p : K) : Prop :=
  ∃ s φ, (⟨s, p, φ⟩ : KSignedFormula K Const) ∈ π

/-- Definition 5.1: `c` is a `p`-constant for `π` when it occurs in some signed
formula at a world `q ≤ p`. -/
def PConstant (π : KHintikkaPath K Const) (p : K) {σ : Ty Base} (c : Const σ) : Prop :=
  ∃ q : K, q ≤ p ∧
    ∃ s : Sign, ∃ φ : ClosedFormula Const,
      (⟨s, q, φ⟩ : KSignedFormula K Const) ∈ π ∧
      ¬ NoConstOccurrence c φ

/-- Definition 5.1: a closed term is a `p`-term if all constants occurring in it
already occur at or below `p` on the path. -/
def PTerm (π : KHintikkaPath K Const) (p : K) {τ : Ty Base} (t : Term Const [] τ) : Prop :=
  ∀ {σ : Ty Base} (c : Const σ), ¬ π.PConstant p c → NoConstOccurrence c t

/-- Definition 5.1 specialized to closed propositions. -/
def PFormula (π : KHintikkaPath K Const) (p : K) (φ : ClosedFormula Const) : Prop :=
  π.PTerm p φ

/-- Definition 5.5: positively forced formulas below world `p`. -/
def positiveAt [DecidableRel ((· ≤ ·) : K → K → Prop)]
    (π : KHintikkaPath K Const) (p : K) : List (ClosedFormula Const) :=
  π.filterMap fun
    | ⟨.trueE, q, φ⟩ => if q ≤ p then some φ else none
    | _ => none

/-- Definition 5.5: negatively forced formulas exactly at world `p`. -/
def negativeAt [DecidableEq K]
    (π : KHintikkaPath K Const) (p : K) : List (ClosedFormula Const) :=
  π.filterMap fun
    | ⟨.falseE, q, φ⟩ => if q = p then some φ else none
    | _ => none

/-- Definition 5.3. -/
def Contradictory [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
    (∃ (p : K) (φ : ClosedFormula Const),
      KSignedFormula.trueAt (Const := Const) p φ ∈ π ∧
      KSignedFormula.falseAt (Const := Const) p φ ∈ π)
  ∨ (∃ p : K, KSignedFormula.trueAt (Const := Const) p (.bot : ClosedFormula Const) ∈ π)
  ∨ (∃ p : K, KSignedFormula.falseAt (Const := Const) p (.top : ClosedFormula Const) ∈ π)

/-- Definition 5.4, restricted to worlds that occur on the finite path. -/
def Closed [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄, π.WorldOccurs p →
    KSignedFormula.trueAt (Const := Const) p (.top : ClosedFormula Const) ∈ π ∧
    KSignedFormula.falseAt (Const := Const) p (.bot : ClosedFormula Const) ∈ π

/-- Definition 5.5 for finite paths. -/
def ICTTConsistent [DecidableEq K] [DecidableRel ((· ≤ ·) : K → K → Prop)]
    (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ : ClosedFormula Const⦄,
    φ ∈ π.negativeAt p →
      ¬ Derivable (Base := Base) (Const := Const) (π.positiveAt p) φ

/-- Definition 5.2, clause 1, parameterized by the chosen eta normalizer. -/
def EtaClause (N : EtaNormalizer (Base := Base) Const) (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃s : Sign⦄ ⦃p : K⦄ ⦃φ : ClosedFormula Const⦄,
    (⟨s, p, φ⟩ : KSignedFormula K Const) ∈ π →
      φ ≠ N.nf φ →
        (⟨s, p, N.nf φ⟩ : KSignedFormula K Const) ∈ π

/-- Definition 5.2, clause 2. -/
def TrueAndClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.trueAt (Const := Const) p (.and φ ψ) ∈ π →
      KSignedFormula.trueAt (Const := Const) p φ ∈ π ∧
      KSignedFormula.trueAt (Const := Const) p ψ ∈ π

/-- Definition 5.2, clause 3. -/
def FalseAndClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.falseAt (Const := Const) p (.and φ ψ) ∈ π →
      KSignedFormula.falseAt (Const := Const) p φ ∈ π ∨
      KSignedFormula.falseAt (Const := Const) p ψ ∈ π

/-- Definition 5.2, clause 4. -/
def TrueOrClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.trueAt (Const := Const) p (.or φ ψ) ∈ π →
      KSignedFormula.trueAt (Const := Const) p φ ∈ π ∨
      KSignedFormula.trueAt (Const := Const) p ψ ∈ π

/-- Definition 5.2, clause 5. -/
def FalseOrClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.falseAt (Const := Const) p (.or φ ψ) ∈ π →
      KSignedFormula.falseAt (Const := Const) p φ ∈ π ∧
      KSignedFormula.falseAt (Const := Const) p ψ ∈ π

/-- Definition 5.2, clause 6. -/
def TrueImpClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p q : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.trueAt (Const := Const) p (.imp φ ψ) ∈ π →
      π.WorldOccurs q →
        p ≤ q →
          KSignedFormula.falseAt (Const := Const) q φ ∈ π ∨
          KSignedFormula.trueAt (Const := Const) q ψ ∈ π

/-- Definition 5.2, clause 7. -/
def FalseImpClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃φ ψ : ClosedFormula Const⦄,
    KSignedFormula.falseAt (Const := Const) p (.imp φ ψ) ∈ π →
      ∃ q, p ≤ q ∧
        KSignedFormula.trueAt (Const := Const) q φ ∈ π ∧
        KSignedFormula.falseAt (Const := Const) q ψ ∈ π

/-- Definition 5.2, clause 8. -/
def TrueExClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃σ : Ty Base⦄ ⦃φ : Formula Const [σ]⦄,
    KSignedFormula.trueAt (Const := Const) p (.ex φ) ∈ π →
      ∃ c : Const σ,
        KSignedFormula.trueAt (Const := Const) p
          (instantiate (Base := Base) (.const c) φ) ∈ π

/-- Definition 5.2, clause 9. -/
def FalseExClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃σ : Ty Base⦄ ⦃φ : Formula Const [σ]⦄,
    KSignedFormula.falseAt (Const := Const) p (.ex φ) ∈ π →
      ∀ ⦃t : Term Const [] σ⦄,
        π.PTerm p t →
          KSignedFormula.falseAt (Const := Const) p
            (instantiate (Base := Base) t φ) ∈ π

/-- Definition 5.2, clause 10. -/
def TrueAllClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p q : K⦄ ⦃σ : Ty Base⦄ ⦃φ : Formula Const [σ]⦄,
    KSignedFormula.trueAt (Const := Const) p (.all φ) ∈ π →
      π.WorldOccurs q →
        p ≤ q →
          ∀ ⦃t : Term Const [] σ⦄,
            π.PTerm q t →
              KSignedFormula.trueAt (Const := Const) q
                (instantiate (Base := Base) t φ) ∈ π

/-- Definition 5.2, clause 11. -/
def FalseAllClause [DecidableEq K] (π : KHintikkaPath K Const) : Prop :=
  ∀ ⦃p : K⦄ ⦃σ : Ty Base⦄ ⦃φ : Formula Const [σ]⦄,
    KSignedFormula.falseAt (Const := Const) p (.all φ) ∈ π →
      ∃ q, p ≤ q ∧
        ∃ c : Const σ,
          KSignedFormula.falseAt (Const := Const) q
            (instantiate (Base := Base) (.const c) φ) ∈ π

/-- Definition 5.2 assembled in one place. -/
def IsKHintikkaSet
    [DecidableEq K]
    (N : EtaNormalizer (Base := Base) Const)
    (π : KHintikkaPath K Const) : Prop :=
    π.EtaClause N
  ∧ π.TrueAndClause
  ∧ π.FalseAndClause
  ∧ π.TrueOrClause
  ∧ π.FalseOrClause
  ∧ π.TrueImpClause
  ∧ π.FalseImpClause
  ∧ π.TrueExClause
  ∧ π.FalseExClause
  ∧ π.TrueAllClause
  ∧ π.FalseAllClause

/-- Definition 5.7. -/
def ForGoal [DecidableEq K]
    (π : KHintikkaPath K Const)
    (p0 : K)
    (Γ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  (∀ ⦃γ : ClosedFormula Const⦄, γ ∈ Γ →
      KSignedFormula.trueAt (Const := Const) p0 γ ∈ π)
    ∧ KSignedFormula.falseAt (Const := Const) p0 φ ∈ π

/-- Clause-preserving embedding of the existing one-world Hintikka staging layer
at a chosen world `p`. -/
def ofHintikkaSet (p : K) (H : HintikkaSet Const []) : KHintikkaPath K Const :=
  H.formulas.map fun
    | (s, φ) => ⟨s, p, φ⟩

/-- Initial paper-facing path for a closed goal at root world `p0`. -/
def ofHintikkaGoal (p0 : K) (g : HintikkaGoal Const []) : KHintikkaPath K Const :=
  (ofHintikkaSet (Const := Const) p0 g.toHintikkaSet)

omit [Preorder K] in
@[simp] theorem mem_trueAt_ofHintikkaSet_iff {p q : K} {H : HintikkaSet Const []}
    {φ : ClosedFormula Const} :
    KSignedFormula.trueAt (Const := Const) q φ ∈ ofHintikkaSet (Const := Const) p H ↔
      q = p ∧ (Sign.trueE, φ) ∈ H.formulas := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨⟨s, ψ⟩, hsf, hs⟩
    cases s <;> simp [KSignedFormula.trueAt] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, hsf⟩
  · intro h
    rcases h with ⟨rfl, h⟩
    exact List.mem_map.mpr ⟨(Sign.trueE, φ), h, by rfl⟩

omit [Preorder K] in
@[simp] theorem mem_falseAt_ofHintikkaSet_iff {p q : K} {H : HintikkaSet Const []}
    {φ : ClosedFormula Const} :
    KSignedFormula.falseAt (Const := Const) q φ ∈ ofHintikkaSet (Const := Const) p H ↔
      q = p ∧ (Sign.falseE, φ) ∈ H.formulas := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨⟨s, ψ⟩, hsf, hs⟩
    cases s <;> simp [KSignedFormula.falseAt] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, hsf⟩
  · intro h
    rcases h with ⟨rfl, h⟩
    exact List.mem_map.mpr ⟨(Sign.falseE, φ), h, by rfl⟩

section Decidable

variable [DecidableEq K] [DecidableRel ((· ≤ ·) : K → K → Prop)]

omit [DecidableEq K] in
@[simp] theorem positiveAt_nil (p : K) :
    (positiveAt (Base := Base) (Const := Const) ([] : KHintikkaPath K Const) p) = [] := rfl

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_nil (p : K) :
    (negativeAt (Base := Base) (Const := Const) ([] : KHintikkaPath K Const) p) = [] := rfl

omit [DecidableEq K] in
theorem mem_positiveAt_of_mem
    {π : KHintikkaPath K Const} {p q : K} {φ : ClosedFormula Const}
    (h : KSignedFormula.trueAt (Const := Const) q φ ∈ π)
    (hq : q ≤ p) :
    φ ∈ π.positiveAt p := by
  unfold positiveAt
  exact List.mem_filterMap.mpr ⟨_, h, by
    simp [KSignedFormula.trueAt, hq]⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem mem_negativeAt_of_mem
    {π : KHintikkaPath K Const} {p : K} {φ : ClosedFormula Const}
    (h : KSignedFormula.falseAt (Const := Const) p φ ∈ π) :
    φ ∈ π.negativeAt p := by
  unfold negativeAt
  exact List.mem_filterMap.mpr ⟨_, h, by
    simp [KSignedFormula.falseAt]⟩

omit [DecidableEq K] in
@[simp] theorem positiveAt_ofHintikkaSet
    (p : K) (H : HintikkaSet Const []) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).positiveAt p = H.trueFormulas := by
  cases H with
  | mk formulas =>
      induction formulas with
      | nil =>
          rfl
      | cons sf tl ih =>
          cases sf with
          | mk s φ =>
              cases s <;> simpa [ofHintikkaSet, positiveAt, HintikkaSet.trueFormulas] using ih

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_ofHintikkaSet
    (p : K) (H : HintikkaSet Const []) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).negativeAt p = H.falseFormulas := by
  cases H with
  | mk formulas =>
      induction formulas with
      | nil =>
          rfl
      | cons sf tl ih =>
          cases sf with
          | mk s φ =>
              cases s <;> simpa [ofHintikkaSet, negativeAt, HintikkaSet.falseFormulas] using ih

theorem icttConsistent_ofHintikkaSet_iff
    (p : K) (H : HintikkaSet Const []) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).ICTTConsistent ↔
      H.ICTTConsistent := by
  constructor
  · intro hCons φ hφ
    have hφ' : φ ∈ (ofHintikkaSet (Base := Base) (Const := Const) p H).negativeAt p := by
      simpa [negativeAt_ofHintikkaSet] using hφ
    have hnot := hCons (p := p) hφ'
    simpa [positiveAt_ofHintikkaSet] using hnot
  · intro hCons q φ hφ
    rcases List.mem_filterMap.mp hφ with ⟨sf, hsf, hsimp⟩
    rcases List.mem_map.mp hsf with ⟨⟨s, ψ⟩, hsrc, rfl⟩
    cases s <;> simp at hsimp
    rcases hsimp with ⟨rfl, rfl⟩
    have hsrc' : ψ ∈ H.falseFormulas := by
      exact HintikkaSet.false_mem_falseFormulas (Base := Base) (Const := Const) hsrc
    simpa [positiveAt_ofHintikkaSet] using hCons hsrc'

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem trueAndClause_ofHintikkaSet
    {p : K} {H : HintikkaSet Const []}
    (hSat : H.LocallySaturated) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).TrueAndClause := by
  intro q φ ψ h
  rcases (mem_trueAt_ofHintikkaSet_iff.mp h) with ⟨rfl, hSrc⟩
  have h' := HintikkaSet.trueAnd_mem_of_locallySaturated (Base := Base) (Const := Const) hSat hSrc
  constructor
  · exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl, h'.1⟩
  · exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl, h'.2⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem falseAndClause_ofHintikkaSet
    {p : K} {H : HintikkaSet Const []}
    (hSat : H.BranchClosed) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).FalseAndClause := by
  intro q φ ψ h
  rcases (mem_falseAt_ofHintikkaSet_iff.mp h) with ⟨rfl, hSrc⟩
  have h' := HintikkaSet.falseAnd_mem_of_branchClosed (Base := Base) (Const := Const) hSat hSrc
  rcases h' with h' | h'
  · left
    exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl, h'⟩
  · right
    exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl, h'⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem trueOrClause_ofHintikkaSet
    {p : K} {H : HintikkaSet Const []}
    (hSat : H.BranchClosed) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).TrueOrClause := by
  intro q φ ψ h
  rcases (mem_trueAt_ofHintikkaSet_iff.mp h) with ⟨rfl, hSrc⟩
  have h' := HintikkaSet.trueOr_mem_of_branchClosed (Base := Base) (Const := Const) hSat hSrc
  rcases h' with h' | h'
  · left
    exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl, h'⟩
  · right
    exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl, h'⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem falseOrClause_ofHintikkaSet
    {p : K} {H : HintikkaSet Const []}
    (hSat : H.LocallySaturated) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).FalseOrClause := by
  intro q φ ψ h
  rcases (mem_falseAt_ofHintikkaSet_iff.mp h) with ⟨rfl, hSrc⟩
  have h' := HintikkaSet.falseOr_mem_of_locallySaturated (Base := Base) (Const := Const) hSat hSrc
  constructor
  · exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl, h'.1⟩
  · exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl, h'.2⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem closed_ofHintikkaSet
    {p : K} {H : HintikkaSet Const []}
    (hClosed : H.Closed) :
    (ofHintikkaSet (Base := Base) (Const := Const) p H).Closed := by
  intro q hq
  rcases hq with ⟨s, φ, hq⟩
  have hp : q = p := by
    rcases List.mem_map.mp hq with ⟨sf, _, hEq⟩
    cases sf with
    | mk s' φ' =>
        cases hEq
        rfl
  subst hp
  constructor
  · exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl,
      HintikkaSet.trueTop_mem_of_closed (Base := Base) (Const := Const) hClosed⟩
  · exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl,
      HintikkaSet.falseBot_mem_of_closed (Base := Base) (Const := Const) hClosed⟩

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
theorem forGoal_ofHintikkaGoal
    (p0 : K) (g : HintikkaGoal Const []) :
    (ofHintikkaGoal (Base := Base) (Const := Const) p0 g).ForGoal p0 g.antecedents g.succedent := by
  constructor
  · intro γ hγ
    exact mem_trueAt_ofHintikkaSet_iff.mpr ⟨rfl,
      HintikkaGoal.true_mem_toHintikkaSet (Base := Base) (Const := Const) hγ⟩
  · exact mem_falseAt_ofHintikkaSet_iff.mpr ⟨rfl,
      HintikkaGoal.false_mem_toHintikkaSet (Base := Base) (Const := Const) g⟩

/-- Generic false-extension step used in the easy half of the finite-path
extension analysis from Theorem 5.9. -/
def extendFalse (π : KHintikkaPath K Const) (p : K) (φ : ClosedFormula Const) :
    KHintikkaPath K Const :=
  π ++ [KSignedFormula.falseAt (Const := Const) p φ]

/-- The `F(∧)` left branch from Theorem 5.9. -/
def extendFalseAndLeft (π : KHintikkaPath K Const) (p : K)
    (φ _ψ : ClosedFormula Const) : KHintikkaPath K Const :=
  π.extendFalse p φ

/-- The `F(∧)` right branch from Theorem 5.9. -/
def extendFalseAndRight (π : KHintikkaPath K Const) (p : K)
    (_φ ψ : ClosedFormula Const) : KHintikkaPath K Const :=
  π.extendFalse p ψ

/-- The deterministic `F(∨)` extension from Theorem 5.9. -/
def extendFalseOr (π : KHintikkaPath K Const) (p : K)
    (φ ψ : ClosedFormula Const) : KHintikkaPath K Const :=
  π ++ [KSignedFormula.falseAt (Const := Const) p φ,
    KSignedFormula.falseAt (Const := Const) p ψ]

omit [DecidableEq K] in
@[simp] theorem positiveAt_extendFalse
    (π : KHintikkaPath K Const) (p q : K) (φ : ClosedFormula Const) :
    (π.extendFalse p φ).positiveAt q = π.positiveAt q := by
  simp [extendFalse, positiveAt, List.filterMap_append, KSignedFormula.falseAt]

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_extendFalse_same
    (π : KHintikkaPath K Const) (p : K) (φ : ClosedFormula Const) :
    (π.extendFalse p φ).negativeAt p = π.negativeAt p ++ [φ] := by
  simp [extendFalse, negativeAt, List.filterMap_append, KSignedFormula.falseAt]

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_extendFalse_other
    (π : KHintikkaPath K Const) {p q : K} (φ : ClosedFormula Const) (h : q ≠ p) :
    (π.extendFalse p φ).negativeAt q = π.negativeAt q := by
  have hpq : p ≠ q := by
    intro hpqEq
    exact h hpqEq.symm
  simp [extendFalse, negativeAt, List.filterMap_append, KSignedFormula.falseAt, hpq]

theorem derivable_of_not_icttConsistent_extendFalse
    (π : KHintikkaPath K Const) {p : K} {φ : ClosedFormula Const}
    (hCons : π.ICTTConsistent)
    (hNot : ¬ (π.extendFalse p φ).ICTTConsistent) :
    Derivable (Base := Base) (Const := Const) (π.positiveAt p) φ := by
  classical
  by_contra hDerive
  apply hNot
  intro q ψ hψ hDer
  by_cases hq : q = p
  · cases hq
    have hsplit : ψ ∈ π.negativeAt p ∨ ψ = φ := by
      simpa [negativeAt_extendFalse_same] using hψ
    rcases hsplit with hOld | rfl
    · exact hCons hOld (by simpa [positiveAt_extendFalse] using hDer)
    · exact hDerive (by simpa [positiveAt_extendFalse] using hDer)
  · have hOld : ψ ∈ π.negativeAt q := by
      simpa [negativeAt_extendFalse_other (h := hq)] using hψ
    exact hCons hOld (by simpa [positiveAt_extendFalse] using hDer)

omit [DecidableEq K] in
@[simp] theorem positiveAt_extendFalseOr
    (π : KHintikkaPath K Const) (p q : K) (φ ψ : ClosedFormula Const) :
    (π.extendFalseOr p φ ψ).positiveAt q = π.positiveAt q := by
  simp [extendFalseOr, positiveAt, List.filterMap_append, KSignedFormula.falseAt]

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_extendFalseOr_same
    (π : KHintikkaPath K Const) (p : K) (φ ψ : ClosedFormula Const) :
    (π.extendFalseOr p φ ψ).negativeAt p = π.negativeAt p ++ [φ, ψ] := by
  simp [extendFalseOr, negativeAt, List.filterMap_append, KSignedFormula.falseAt]

omit [Preorder K] [DecidableRel ((· ≤ ·) : K → K → Prop)] in
@[simp] theorem negativeAt_extendFalseOr_other
    (π : KHintikkaPath K Const) {p q : K} (φ ψ : ClosedFormula Const) (h : q ≠ p) :
    (π.extendFalseOr p φ ψ).negativeAt q = π.negativeAt q := by
  have hpq : p ≠ q := by
    intro hpqEq
    exact h hpqEq.symm
  simp [extendFalseOr, negativeAt, List.filterMap_append, KSignedFormula.falseAt, hpq]

theorem falseOr_extension_icttConsistent
    (π : KHintikkaPath K Const)
    {p : K} {φ ψ : ClosedFormula Const}
    (hCons : π.ICTTConsistent)
    (hFalseOr : KSignedFormula.falseAt (Const := Const) p (.or φ ψ) ∈ π) :
    (π.extendFalseOr p φ ψ).ICTTConsistent := by
  classical
  intro q θ hθ hDer
  by_cases hq : q = p
  · cases hq
    have hsplit : θ ∈ π.negativeAt p ∨ θ = φ ∨ θ = ψ := by
      simpa [negativeAt_extendFalseOr_same] using hθ
    rcases hsplit with hOld | rfl | rfl
    · exact hCons hOld (by
        simpa [positiveAt_extendFalseOr] using hDer)
    · exact (hCons (mem_negativeAt_of_mem hFalseOr))
        (Derivable.orR₁ (by simpa [positiveAt_extendFalseOr] using hDer))
    · exact (hCons (mem_negativeAt_of_mem hFalseOr))
        (Derivable.orR₂ (by simpa [positiveAt_extendFalseOr] using hDer))
  · have hOld : θ ∈ π.negativeAt q := by
      simpa [negativeAt_extendFalseOr_other (h := hq)] using hθ
    exact hCons hOld (by simpa [positiveAt_extendFalseOr] using hDer)

theorem falseAnd_branches_not_both_inconsistent
    (π : KHintikkaPath K Const)
    {p : K} {φ ψ : ClosedFormula Const}
    (hCons : π.ICTTConsistent)
    (hFalseAnd : KSignedFormula.falseAt (Const := Const) p (.and φ ψ) ∈ π) :
    ¬ (¬ (π.extendFalseAndLeft p φ ψ).ICTTConsistent ∧
        ¬ (π.extendFalseAndRight p φ ψ).ICTTConsistent) := by
  intro hBoth
  have hφ :
      Derivable (Base := Base) (Const := Const) (π.positiveAt p) φ :=
    derivable_of_not_icttConsistent_extendFalse
      (π := π) (p := p) (φ := φ) hCons hBoth.1
  have hψ :
      Derivable (Base := Base) (Const := Const) (π.positiveAt p) ψ :=
    derivable_of_not_icttConsistent_extendFalse
      (π := π) (p := p) (φ := ψ) hCons hBoth.2
  exact (hCons (mem_negativeAt_of_mem hFalseAnd))
    (Derivable.andR hφ hψ)

theorem false_betaEta_extension_icttConsistent
    (π : KHintikkaPath K Const)
    {p : K} {φ ψ : ClosedFormula Const}
    (hCons : π.ICTTConsistent)
    (hFalse : KSignedFormula.falseAt (Const := Const) p φ ∈ π)
    (hEq : BetaEtaEq (Base := Base) (Const := Const) φ ψ) :
    (π.extendFalse p ψ).ICTTConsistent := by
  intro q θ hθ hDer
  by_cases hq : q = p
  · cases hq
    have hsplit : θ ∈ π.negativeAt p ∨ θ = ψ := by
      simpa [negativeAt_extendFalse_same] using hθ
    rcases hsplit with hOld | rfl
    · exact hCons hOld (by simpa [positiveAt_extendFalse] using hDer)
    · have hφ :
        Derivable (Base := Base) (Const := Const) (π.positiveAt p) φ :=
        Derivable.lam
          (Base := Base) (Const := Const)
          (AntecedentsBetaEtaEq.refl _)
          hEq
          (by simpa [positiveAt_extendFalse] using hDer)
      exact (hCons (mem_negativeAt_of_mem hFalse)) hφ
  · have hOld : θ ∈ π.negativeAt q := by
      simpa [negativeAt_extendFalse_other (h := hq)] using hθ
    exact hCons hOld (by simpa [positiveAt_extendFalse] using hDer)

end Decidable

end KHintikkaPath

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
