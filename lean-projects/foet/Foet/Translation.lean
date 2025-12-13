import Foet.Theory

set_option autoImplicit false

namespace Foet

universe u v w

/-
Minimal translation abstractions for the ESOWIKI/SUMO MVP.

In the wiki/KIF, most “paradigm translation functions” are unary functions between
restricted sentence fragments. The main extra wrinkle is when a translation
*introduces an entity existentially* (e.g. “there exists a virtue …”).

Lean gives two (philosophically different) encodings:
- Prop-level existence: `∃ x, P x`  (no computable witness; compatible with “there is *some* grounding”)
- Witness-carrying:   `PSigma fun x => P x` (computable witness; “this specific grounding”)

We intentionally postpone “cloud/cover of reasons” semantics (where multiple reasons jointly
cover a claim) until we have concrete examples from the ontology that need it.
-/

/-- A translation relation from `S₁` to `S₂`. -/
abbrev TranslationRel (S₁ : Type u) (S₂ : Type v) : Type (max u v) :=
  S₁ → S₂ → Prop

/-- Prop-level existence of some translation target. -/
def Translates {S₁ : Type u} {S₂ : Type v} (R : TranslationRel S₁ S₂) (s : S₁) : Prop :=
  ∃ t, R s t

/-- Witness-carrying existence of a translation target. -/
abbrev Witnessed {S₁ : Type u} {S₂ : Type v} (R : TranslationRel S₁ S₂) (s : S₁) :=
  PSigma fun t : S₂ => R s t

theorem witnessed_to_translates {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {s : S₁} :
    Witnessed R s → Translates R s := by
  intro h
  exact ⟨h.fst, h.snd⟩

theorem translates_to_nonempty_witnessed {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {s : S₁} :
    Translates R s → Nonempty (Witnessed R s) := by
  intro h
  rcases h with ⟨t, ht⟩
  exact ⟨⟨t, ht⟩⟩

def Witnessed.witness {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {s : S₁} :
    Witnessed R s → S₂ :=
  fun h => h.fst

namespace Theory

/--
Relational pushforward of a theory along a translation relation.

This is the right notion for KIF “translation functions” that *introduce existentials*:
we cannot (and philosophically often should not) pick a unique output sentence, but we can
still form the image theory consisting of all possible translation targets.
-/
def relMap {S₁ : Type u} {S₂ : Type v} (R : TranslationRel S₁ S₂) (T : Theory S₁) : Theory S₂ :=
  fun s₂ => ∃ s₁, s₁ ∈ T ∧ R s₁ s₂

theorem mem_relMap_iff {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {T : Theory S₁} {s₂ : S₂} :
    s₂ ∈ relMap R T ↔ ∃ s₁, s₁ ∈ T ∧ R s₁ s₂ :=
  Iff.rfl

theorem mem_relMap_of_mem {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {T : Theory S₁}
    {s₁ : S₁} {s₂ : S₂} (hs₁ : s₁ ∈ T) (hR : R s₁ s₂) :
    s₂ ∈ relMap R T :=
  ⟨s₁, hs₁, hR⟩

theorem relMap_graph_eq_map {S₁ : Type u} {S₂ : Type v} (f : S₁ → S₂) (T : Theory S₁) :
    relMap (fun s₁ s₂ => f s₁ = s₂) T = map f T := by
  rfl

/-- Every sentence in the theory has *some* translation target (Prop-level). -/
def TotalOn {S₁ : Type u} {S₂ : Type v} (R : TranslationRel S₁ S₂) (T : Theory S₁) : Prop :=
  ∀ s₁, s₁ ∈ T → Translates R s₁

/-- Every sentence in the theory has a *chosen* witness translation target (Sigma-level). -/
def WitnessTotalOn {S₁ : Type u} {S₂ : Type v} (R : TranslationRel S₁ S₂) (T : Theory S₁) : Type (max u v) :=
  ∀ s₁, s₁ ∈ T → Witnessed R s₁

theorem witnessTotalOn_to_totalOn {S₁ : Type u} {S₂ : Type v} {R : TranslationRel S₁ S₂} {T : Theory S₁} :
    WitnessTotalOn R T → TotalOn R T := by
  intro h s₁ hs₁
  exact witnessed_to_translates (h s₁ hs₁)

end Theory

/-! ## Relational model/entailment transport (soundness/completeness) -/

def RelSound {S₁ : Type u} {S₂ : Type v} {M : Type w} (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (R : TranslationRel S₁ S₂) : Prop :=
  ∀ m s₁ s₂, R s₁ s₂ → sem₁.Sat m s₁ → sem₂.Sat m s₂

/-- `R` is complete for `(sem₁, sem₂)` if related sentences reflect satisfaction. -/
def RelComplete {S₁ : Type u} {S₂ : Type v} {M : Type w} (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (R : TranslationRel S₁ S₂) : Prop :=
  ∀ m s₁ s₂, R s₁ s₂ → sem₂.Sat m s₂ → sem₁.Sat m s₁

theorem models_relMap_of_models {S₁ : Type u} {S₂ : Type v} {M : Type w} {sem₁ : Semantics S₁ M} {sem₂ : Semantics S₂ M}
    {R : TranslationRel S₁ S₂} {m : M} {T : Theory S₁}
    (hSound : RelSound sem₁ sem₂ R) :
    Models sem₁ m T → Models sem₂ m (Theory.relMap R T) := by
  intro hT
  intro s₂ hs₂
  rcases hs₂ with ⟨s₁, hs₁, hR⟩
  exact hSound m s₁ s₂ hR (hT s₁ hs₁)

theorem models_of_models_relMap_of_witnessTotal {S₁ : Type u} {S₂ : Type v} {M : Type w} {sem₁ : Semantics S₁ M}
    {sem₂ : Semantics S₂ M} {R : TranslationRel S₁ S₂} {m : M} {T : Theory S₁}
    (hComplete : RelComplete sem₁ sem₂ R)
    (hTotal : Theory.WitnessTotalOn R T) :
    Models sem₂ m (Theory.relMap R T) → Models sem₁ m T := by
  intro hTf
  intro s₁ hs₁
  have hw : Witnessed R s₁ :=
    hTotal s₁ hs₁
  have hs₂ : hw.fst ∈ Theory.relMap R T :=
    Theory.mem_relMap_of_mem (T := T) (hs₁ := hs₁) (hR := hw.snd)
  have hSat₂ : sem₂.Sat m hw.fst :=
    hTf hw.fst hs₂
  exact hComplete m s₁ hw.fst hw.snd hSat₂

theorem entails_relMap_of_entails_of_witnessTotal {S₁ : Type u} {S₂ : Type v} {M : Type w} {sem₁ : Semantics S₁ M}
    {sem₂ : Semantics S₂ M} {R : TranslationRel S₁ S₂} {T : Theory S₁} {s₁ : S₁} {s₂ : S₂}
    (hSound : RelSound sem₁ sem₂ R)
    (hComplete : RelComplete sem₁ sem₂ R)
    (hTotal : Theory.WitnessTotalOn R T)
    (hR : R s₁ s₂) :
    Entails sem₁ T s₁ → Entails sem₂ (Theory.relMap R T) s₂ := by
  intro hEnt m hm
  have hmT : Models sem₁ m T :=
    models_of_models_relMap_of_witnessTotal (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (m := m) (T := T)
      hComplete hTotal hm
  have hSat₁ : sem₁.Sat m s₁ :=
    hEnt m hmT
  exact hSound m s₁ s₂ hR hSat₁

theorem entails_of_entails_relMap {S₁ : Type u} {S₂ : Type v} {M : Type w} {sem₁ : Semantics S₁ M} {sem₂ : Semantics S₂ M}
    {R : TranslationRel S₁ S₂} {T : Theory S₁} {s₁ : S₁} {s₂ : S₂}
    (hSound : RelSound sem₁ sem₂ R)
    (hComplete : RelComplete sem₁ sem₂ R)
    (hR : R s₁ s₂) :
    Entails sem₂ (Theory.relMap R T) s₂ → Entails sem₁ T s₁ := by
  intro hEnt m hm
  have hm₂ : Models sem₂ m (Theory.relMap R T) :=
    models_relMap_of_models (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (m := m) (T := T) hSound hm
  have hSat₂ : sem₂.Sat m s₂ :=
    hEnt m hm₂
  exact hComplete m s₁ s₂ hR hSat₂

theorem entails_iff_entails_relMap_of_witnessTotal {S₁ : Type u} {S₂ : Type v} {M : Type w} {sem₁ : Semantics S₁ M}
    {sem₂ : Semantics S₂ M} {R : TranslationRel S₁ S₂} {T : Theory S₁} {s₁ : S₁} {s₂ : S₂}
    (hSound : RelSound sem₁ sem₂ R)
    (hComplete : RelComplete sem₁ sem₂ R)
    (hTotal : Theory.WitnessTotalOn R T)
    (hR : R s₁ s₂) :
    Entails sem₁ T s₁ ↔ Entails sem₂ (Theory.relMap R T) s₂ := by
  constructor
  · exact entails_relMap_of_entails_of_witnessTotal (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (T := T)
      (s₁ := s₁) (s₂ := s₂) hSound hComplete hTotal hR
  · exact entails_of_entails_relMap (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (T := T)
      (s₁ := s₁) (s₂ := s₂) hSound hComplete hR

end Foet
