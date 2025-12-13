set_option autoImplicit false

namespace Foet

/-
Lean core does not ship a dedicated `Set` module in this environment.
We define the minimal set primitives we need: a set is just a predicate.
-/

universe u v w

abbrev Set (α : Type u) : Type u :=
  α → Prop

instance {α : Type u} : Membership α (Set α) where
  mem s x := s x

namespace Set

def singleton {α : Type u} (a : α) : Set α :=
  fun x => x = a

theorem mem_singleton_iff {α : Type u} {a x : α} : x ∈ singleton a ↔ x = a :=
  Iff.rfl

def insert {α : Type u} (a : α) (s : Set α) : Set α :=
  fun x => x = a ∨ x ∈ s

def union {α : Type u} (s t : Set α) : Set α :=
  fun x => x ∈ s ∨ x ∈ t

def subset {α : Type u} (s t : Set α) : Prop :=
  ∀ x, x ∈ s → x ∈ t

end Set

/--
A `Theory S` is a set of sentences of type `S`.

This mirrors the KIF/SUMO style where theories are sets of sentences (`element ?S ?T`).
-/
abbrev Theory (S : Type u) : Type u := Set S

namespace Theory

/-- Push a theory forward along a sentence translation function. -/
def map {α : Type u} {β : Type v} (f : α → β) (T : Theory α) : Theory β :=
  fun b => ∃ a, a ∈ T ∧ f a = b

theorem mem_map_of_mem {α : Type u} {β : Type v} {f : α → β} {T : Theory α} {a : α} (h : a ∈ T) :
    f a ∈ map f T :=
  ⟨a, h, rfl⟩

theorem map_singleton {α : Type u} {β : Type v} (f : α → β) (a : α) :
    map f (Set.singleton a) = Set.singleton (f a) := by
  funext b
  apply propext
  constructor
  · intro hb
    rcases hb with ⟨a', ha', hEq⟩
    -- `ha' : a' = a` because membership in a singleton is definitional equality.
    cases ha'
    exact hEq.symm
  · intro hb
    refine ⟨a, rfl, ?_⟩
    exact hb.symm

end Theory

/-- A semantics for sentences of type `S` in models of type `M`. -/
structure Semantics (S : Type u) (M : Type v) : Type (max u v) where
  Sat : M → S → Prop

/-- A model `m` satisfies a theory `T` if it satisfies every sentence in `T`. -/
def Models {S : Type u} {M : Type v} (sem : Semantics S M) (m : M) (T : Theory S) : Prop :=
  ∀ s, s ∈ T → sem.Sat m s

/--
Semantic entailment: `T ⊨ φ` if every model of `T` satisfies `φ`.

This is the bridge you want to connect “sets of sentences” to semantic evaluators.
-/
def Entails {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) (φ : S) : Prop :=
  ∀ m, Models sem m T → sem.Sat m φ

/--
Entailment under an additional *model-side* condition/premise `C`.

For ethics, `M` is typically `World` and `C : World → Prop` is a “situation description”
formula that we assume holds during evaluation.
-/
def EntailsUnder {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) (C : M → Prop) (φ : S) : Prop :=
  ∀ m, C m → Models sem m T → sem.Sat m φ

/--
Generic model preservation/equivalence for a translation `f`.

If `f` preserves satisfaction *both ways* in a fixed semantics pair, then `T` and `map f T`
have the same models (in those respective semantics).
-/
theorem models_map_iff {S₁ : Type u} {S₂ : Type v} {M : Type w} (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (m : M) (T : Theory S₁) :
    Models sem₁ m T ↔ Models sem₂ m (Theory.map f T) := by
  constructor
  · intro hT
    intro s₂ hs₂
    rcases hs₂ with ⟨s₁, hs₁, hEq⟩
    have hSat₁ : sem₁.Sat m s₁ :=
      hT s₁ hs₁
    have hSat₂ : sem₂.Sat m (f s₁) :=
      (h_sat m s₁).1 hSat₁
    simpa [hEq] using hSat₂
  · intro hTf
    intro s₁ hs₁
    have hs₂ : f s₁ ∈ Theory.map f T :=
      Theory.mem_map_of_mem (T := T) (f := f) (a := s₁) hs₁
    have hSat₂ : sem₂.Sat m (f s₁) :=
      hTf (f s₁) hs₂
    exact (h_sat m s₁).2 hSat₂

/--
Generic entailment preservation/equivalence for a translation `f`.

This is the abstraction behind `entails_deontic_iff_entails_value` and
`entails_utilitarian_iff_entails_value`.
-/
theorem entails_map_iff {S₁ : Type u} {S₂ : Type v} {M : Type w} (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (T : Theory S₁) (s : S₁) :
    Entails sem₁ T s ↔ Entails sem₂ (Theory.map f T) (f s) := by
  constructor
  · intro hEnt m hm
    have hm₁ : Models sem₁ m T :=
      (models_map_iff sem₁ sem₂ f h_sat m T).2 hm
    have hSat₁ : sem₁.Sat m s :=
      hEnt m hm₁
    exact (h_sat m s).1 hSat₁
  · intro hEnt m hm
    have hm₂ : Models sem₂ m (Theory.map f T) :=
      (models_map_iff sem₁ sem₂ f h_sat m T).1 hm
    have hSat₂ : sem₂.Sat m (f s) :=
      hEnt m hm₂
    exact (h_sat m s).2 hSat₂

/-- Contextual variant of `entails_map_iff` (threads an extra model-side premise `C`). -/
theorem entails_map_iff_under {S₁ : Type u} {S₂ : Type v} {M : Type w} (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M)
    (f : S₁ → S₂)
    (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))
    (T : Theory S₁) (C : M → Prop) (s : S₁) :
    EntailsUnder sem₁ T C s ↔ EntailsUnder sem₂ (Theory.map f T) C (f s) := by
  constructor
  · intro hEnt m hC hm
    have hm₁ : Models sem₁ m T :=
      (models_map_iff sem₁ sem₂ f h_sat m T).2 hm
    have hSat₁ : sem₁.Sat m s :=
      hEnt m hC hm₁
    exact (h_sat m s).1 hSat₁
  · intro hEnt m hC hm
    have hm₂ : Models sem₂ m (Theory.map f T) :=
      (models_map_iff sem₁ sem₂ f h_sat m T).1 hm
    have hSat₂ : sem₂.Sat m (f s) :=
      hEnt m hC hm₂
    exact (h_sat m s).2 hSat₂

/-- Satisfiable = has at least one model. -/
def Satisfiable {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) : Prop :=
  ∃ m, Models sem m T

/-- Theories are semantically equivalent if they have the same consequences. -/
def Equivalent {S : Type u} {M : Type v} (sem : Semantics S M) (T₁ T₂ : Theory S) : Prop :=
  ∀ φ, Entails sem T₁ φ ↔ Entails sem T₂ φ

end Foet
