import Foet.EthicsCore
import Foet.Translation

set_option autoImplicit false

namespace Foet

universe u v

/-
Replacing the ad-hoc KIF/SUMO `part`-based “sentence structure” encoding with an
explicit, type-checked syntax tree.

This lets us define paradigm translations by structural recursion (the “correct”
way), and then prove semantic commutation by induction, rather than attempting to
axiomatize recursion indirectly in a first-order ontology.
-/

/-! ## A tiny, typed sentence AST (connectives + quantifiers) -/

inductive StructuredSentence (World : Type u) (Atom : Type (max u 1)) : Type (u + 1) where
  | atom : Atom → StructuredSentence World Atom
  | and : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | or : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | not : StructuredSentence World Atom → StructuredSentence World Atom
  | imp : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | iff : StructuredSentence World Atom → StructuredSentence World Atom → StructuredSentence World Atom
  | forall_ {α : Type u} : (α → StructuredSentence World Atom) → StructuredSentence World Atom
  | exists_ {α : Type u} : (α → StructuredSentence World Atom) → StructuredSentence World Atom

namespace StructuredSentence

def map {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} (f : Atom₁ → Atom₂) :
    StructuredSentence World Atom₁ → StructuredSentence World Atom₂
  | atom a => atom (f a)
  | and p q => and (map f p) (map f q)
  | or p q => or (map f p) (map f q)
  | not p => not (map f p)
  | imp p q => imp (map f p) (map f q)
  | iff p q => iff (map f p) (map f q)
  | forall_ g => forall_ (fun x => map f (g x))
  | exists_ g => exists_ (fun x => map f (g x))

def Sat {World : Type u} {Atom : Type (max u 1)} {M : Type v} (satAtom : M → Atom → Prop) :
    M → StructuredSentence World Atom → Prop
  | m, atom a => satAtom m a
  | m, and p q => Sat satAtom m p ∧ Sat satAtom m q
  | m, or p q => Sat satAtom m p ∨ Sat satAtom m q
  | m, not p => ¬ Sat satAtom m p
  | m, imp p q => Sat satAtom m p → Sat satAtom m q
  | m, iff p q => Sat satAtom m p ↔ Sat satAtom m q
  | m, forall_ g => ∀ x, Sat satAtom m (g x)
  | m, exists_ g => ∃ x, Sat satAtom m (g x)

def semantics {World : Type u} {Atom : Type (max u 1)} {M : Type v} (semAtom : Semantics Atom M) :
    Semantics (StructuredSentence World Atom) M :=
  ⟨fun m s => Sat (fun m a => semAtom.Sat m a) m s⟩

/-! ## Sigma/witness (“Skolem-style”) translation support -/

/--
Lift an atom-level translation relation `R` to structured sentences by requiring the *same*
logical shape, with `R` holding at each atomic leaf.
-/
def relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} (R : TranslationRel Atom₁ Atom₂) :
    TranslationRel (StructuredSentence World Atom₁) (StructuredSentence World Atom₂)
  | atom a₁, atom a₂ => R a₁ a₂
  | and p₁ q₁, and p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | or p₁ q₁, or p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | not p₁, not p₂ => relLift R p₁ p₂
  | imp p₁ q₁, imp p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | iff p₁ q₁, iff p₂ q₂ => relLift R p₁ p₂ ∧ relLift R q₁ q₂
  | forall_ (α := α₁) g₁, forall_ (α := α₂) g₂ =>
      ∃ h : α₁ = α₂, ∀ x : α₁, relLift R (g₁ x) (g₂ (cast h x))
  | exists_ (α := α₁) g₁, exists_ (α := α₂) g₂ =>
      ∃ h : α₁ = α₂, ∀ x : α₁, relLift R (g₁ x) (g₂ (cast h x))
  | _, _ => False

/--
If you can pick a witness translation target for each atom (a “Skolem choice”),
then you can pick a witness translation target for each structured sentence by recursion.
-/
def witnessedLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} (R : TranslationRel Atom₁ Atom₂)
    (choose : ∀ a : Atom₁, Witnessed R a) :
    ∀ s : StructuredSentence World Atom₁, Witnessed (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) s
  | atom a =>
      ⟨atom (choose a).fst, by
        simpa [relLift] using (choose a).snd⟩
  | and p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨and hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | or p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨or hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | not p =>
      let hp := witnessedLift R choose p
      ⟨not hp.fst, by
        simpa [relLift] using hp.snd⟩
  | imp p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨imp hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | iff p q =>
      let hp := witnessedLift R choose p
      let hq := witnessedLift R choose q
      ⟨iff hp.fst hq.fst, by
        simpa [relLift] using And.intro hp.snd hq.snd⟩
  | forall_ g =>
      ⟨forall_ (fun x => (witnessedLift R choose (g x)).fst), by
        refine ⟨rfl, ?_⟩
        intro x
        simpa [relLift] using (witnessedLift R choose (g x)).snd⟩
  | exists_ g =>
      ⟨exists_ (fun x => (witnessedLift R choose (g x)).fst), by
        refine ⟨rfl, ?_⟩
        intro x
        simpa [relLift] using (witnessedLift R choose (g x)).snd⟩

theorem sat_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (m : M) (s : StructuredSentence World Atom₁) :
    (semantics (World := World) sem₁).Sat m s ↔
      (semantics (World := World) sem₂).Sat m (map f s) := by
  induction s generalizing m with
  | atom a =>
      simpa [semantics, Sat, map] using (h_sat m a)
  | and p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      have ihpSat :
          Sat (fun m a => sem₁.Sat m a) m p ↔ Sat (fun m a => sem₂.Sat m a) m (map f p) := by
        simpa [semantics] using ihp'
      have ihqSat :
          Sat (fun m a => sem₁.Sat m a) m q ↔ Sat (fun m a => sem₂.Sat m a) m (map f q) := by
        simpa [semantics] using ihq'
      constructor
      · intro h
        exact ⟨(ihpSat).1 h.1, (ihqSat).1 h.2⟩
      · intro h
        exact ⟨(ihpSat).2 h.1, (ihqSat).2 h.2⟩
  | or p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      have ihpSat :
          Sat (fun m a => sem₁.Sat m a) m p ↔ Sat (fun m a => sem₂.Sat m a) m (map f p) := by
        simpa [semantics] using ihp'
      have ihqSat :
          Sat (fun m a => sem₁.Sat m a) m q ↔ Sat (fun m a => sem₂.Sat m a) m (map f q) := by
        simpa [semantics] using ihq'
      constructor
      · intro h
        cases h with
        | inl hp => exact Or.inl ((ihpSat).1 hp)
        | inr hq => exact Or.inr ((ihqSat).1 hq)
      · intro h
        cases h with
        | inl hp => exact Or.inl ((ihpSat).2 hp)
        | inr hq => exact Or.inr ((ihqSat).2 hq)
  | not p ih =>
      have ih' := ih m
      constructor
      · intro hNot hSat₂
        have hSat₁ : (semantics (World := World) sem₁).Sat m p :=
          ih'.2 hSat₂
        exact hNot hSat₁
      · intro hNot hSat₁
        have hSat₂ : (semantics (World := World) sem₂).Sat m (map f p) :=
          ih'.1 hSat₁
        exact hNot hSat₂
  | imp p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      constructor
      · intro hImp hSat₂p
        have hSat₁p : (semantics (World := World) sem₁).Sat m p :=
          ihp'.2 hSat₂p
        have hSat₁q : (semantics (World := World) sem₁).Sat m q :=
          hImp hSat₁p
        exact ihq'.1 hSat₁q
      · intro hImp hSat₁p
        have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) :=
          ihp'.1 hSat₁p
        have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) :=
          hImp hSat₂p
        exact ihq'.2 hSat₂q
  | iff p q ihp ihq =>
      have ihp' := ihp m
      have ihq' := ihq m
      constructor
      · intro hIff
        constructor
        · intro hSat₂p
          have hSat₁p : (semantics (World := World) sem₁).Sat m p :=
            ihp'.2 hSat₂p
          have hSat₁q : (semantics (World := World) sem₁).Sat m q :=
            (hIff).1 hSat₁p
          exact ihq'.1 hSat₁q
        · intro hSat₂q
          have hSat₁q : (semantics (World := World) sem₁).Sat m q :=
            ihq'.2 hSat₂q
          have hSat₁p : (semantics (World := World) sem₁).Sat m p :=
            (hIff).2 hSat₁q
          exact ihp'.1 hSat₁p
      · intro hIff
        constructor
        · intro hSat₁p
          have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) :=
            ihp'.1 hSat₁p
          have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) :=
            (hIff).1 hSat₂p
          exact ihq'.2 hSat₂q
        · intro hSat₁q
          have hSat₂q : (semantics (World := World) sem₂).Sat m (map f q) :=
            ihq'.1 hSat₁q
          have hSat₂p : (semantics (World := World) sem₂).Sat m (map f p) :=
            (hIff).2 hSat₂q
          exact ihp'.2 hSat₂p
  | forall_ g ih =>
      constructor
      · intro h x
        exact (ih x m).1 (h x)
      · intro h x
        exact (ih x m).2 (h x)
  | exists_ g ih =>
      constructor
      · intro h
        rcases h with ⟨x, hx⟩
        exact ⟨x, (ih x m).1 hx⟩
      · intro h
        rcases h with ⟨x, hx⟩
        exact ⟨x, (ih x m).2 hx⟩

theorem models_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (m : M) (T : Theory (StructuredSentence World Atom₁)) :
    Models (semantics (World := World) sem₁) m T ↔
      Models (semantics (World := World) sem₂) m (Theory.map (map f) T) := by
  simpa using
    (Foet.models_map_iff
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (f := map f)
      (h_sat := fun m s => sat_map_iff (sem₁ := sem₁) (sem₂ := sem₂) (f := f) h_sat m s)
      (m := m) (T := T))

theorem entails_map_iff {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (T : Theory (StructuredSentence World Atom₁)) (s : StructuredSentence World Atom₁) :
    Entails (semantics (World := World) sem₁) T s ↔
      Entails (semantics (World := World) sem₂) (Theory.map (map f) T) (map f s) := by
  simpa using
    (Foet.entails_map_iff
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (f := map f)
      (h_sat := fun m s => sat_map_iff (sem₁ := sem₁) (sem₂ := sem₂) (f := f) h_sat m s)
      (T := T) (s := s))

theorem entails_map_iff_under {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (f : Atom₁ → Atom₂)
    (h_sat : ∀ m a, sem₁.Sat m a ↔ sem₂.Sat m (f a))
    (T : Theory (StructuredSentence World Atom₁)) (C : M → Prop) (s : StructuredSentence World Atom₁) :
    EntailsUnder (semantics (World := World) sem₁) T C s ↔
      EntailsUnder (semantics (World := World) sem₂) (Theory.map (map f) T) C (map f s) := by
  simpa using
    (Foet.entails_map_iff_under
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (f := map f)
      (h_sat := fun m s => sat_map_iff (sem₁ := sem₁) (sem₂ := sem₂) (f := f) h_sat m s)
      (T := T) (C := C) (s := s))

/-! ## Relational soundness/completeness lifts to structured sentences -/

theorem sat_iff_of_relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (R : TranslationRel Atom₁ Atom₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R) :
    ∀ m (s₁ : StructuredSentence World Atom₁) (s₂ : StructuredSentence World Atom₂),
      relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R s₁ s₂ →
        ((semantics (World := World) sem₁).Sat m s₁ ↔ (semantics (World := World) sem₂).Sat m s₂) := by
  intro m s₁ s₂ hR
  induction s₁ generalizing s₂ with
  | atom a₁ =>
      cases s₂ with
      | atom a₂ =>
          constructor
          · intro hSat₁
            have hSat₁' : sem₁.Sat m a₁ := by
              simpa [semantics, Sat] using hSat₁
            have hSat₂' : sem₂.Sat m a₂ :=
              hSound m a₁ a₂ hR hSat₁'
            simpa [semantics, Sat] using hSat₂'
          · intro hSat₂
            have hSat₂' : sem₂.Sat m a₂ := by
              simpa [semantics, Sat] using hSat₂
            have hSat₁' : sem₁.Sat m a₁ :=
              hComplete m a₁ a₂ hR hSat₂'
            simpa [semantics, Sat] using hSat₁'
      | _ => cases hR
  | and p q ihp ihq =>
      cases s₂ with
      | and p₂ q₂ =>
          rcases hR with ⟨hRp, hRq⟩
          have hp : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₂).Sat m p₂ :=
            ihp (s₂ := p₂) hRp
          have hq : (semantics (World := World) sem₁).Sat m q ↔ (semantics (World := World) sem₂).Sat m q₂ :=
            ihq (s₂ := q₂) hRq
          constructor <;> intro hSat <;> rcases (by simpa [semantics, Sat] using hSat) with ⟨hpSat, hqSat⟩
          · have hpSat' := hp.1 hpSat
            have hqSat' := hq.1 hqSat
            simpa [semantics, Sat] using And.intro hpSat' hqSat'
          · have hpSat' := hp.2 hpSat
            have hqSat' := hq.2 hqSat
            simpa [semantics, Sat] using And.intro hpSat' hqSat'
      | _ => cases hR
  | or p q ihp ihq =>
      cases s₂ with
      | or p₂ q₂ =>
          rcases hR with ⟨hRp, hRq⟩
          have hp : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₂).Sat m p₂ :=
            ihp (s₂ := p₂) hRp
          have hq : (semantics (World := World) sem₁).Sat m q ↔ (semantics (World := World) sem₂).Sat m q₂ :=
            ihq (s₂ := q₂) hRq
          constructor
          · intro hSat
            have hSat' : (semantics (World := World) sem₁).Sat m p ∨ (semantics (World := World) sem₁).Sat m q := by
              simpa [semantics, Sat] using hSat
            cases hSat' with
            | inl hpSat =>
                simpa [semantics, Sat] using Or.inl (hp.1 hpSat)
            | inr hqSat =>
                simpa [semantics, Sat] using Or.inr (hq.1 hqSat)
          · intro hSat
            have hSat' : (semantics (World := World) sem₂).Sat m p₂ ∨ (semantics (World := World) sem₂).Sat m q₂ := by
              simpa [semantics, Sat] using hSat
            cases hSat' with
            | inl hpSat =>
                simpa [semantics, Sat] using Or.inl (hp.2 hpSat)
            | inr hqSat =>
                simpa [semantics, Sat] using Or.inr (hq.2 hqSat)
      | _ => cases hR
  | not p ih =>
      cases s₂ with
      | not p₂ =>
          have hp : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₂).Sat m p₂ :=
            ih (s₂ := p₂) hR
          constructor
          · intro hNot hp₂
            have hp₁ : (semantics (World := World) sem₁).Sat m p :=
              hp.2 hp₂
            exact (by
              have : ¬ (semantics (World := World) sem₁).Sat m p := by
                simpa [semantics, Sat] using hNot
              exact this hp₁)
          · intro hNot hp₁
            have hp₂ : (semantics (World := World) sem₂).Sat m p₂ :=
              hp.1 hp₁
            have : ¬ (semantics (World := World) sem₂).Sat m p₂ := by
              simpa [semantics, Sat] using hNot
            exact this hp₂
      | _ => cases hR
  | imp p q ihp ihq =>
      cases s₂ with
      | imp p₂ q₂ =>
          rcases hR with ⟨hRp, hRq⟩
          have hp : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₂).Sat m p₂ :=
            ihp (s₂ := p₂) hRp
          have hq : (semantics (World := World) sem₁).Sat m q ↔ (semantics (World := World) sem₂).Sat m q₂ :=
            ihq (s₂ := q₂) hRq
          constructor
          · intro hImp hp₂Sat
            have hImp' : (semantics (World := World) sem₁).Sat m p → (semantics (World := World) sem₁).Sat m q := by
              simpa [semantics, Sat] using hImp
            have hp₁Sat : (semantics (World := World) sem₁).Sat m p :=
              hp.2 hp₂Sat
            have hq₁Sat : (semantics (World := World) sem₁).Sat m q :=
              hImp' hp₁Sat
            have hq₂Sat : (semantics (World := World) sem₂).Sat m q₂ :=
              hq.1 hq₁Sat
            exact (by
              simpa [semantics, Sat] using hq₂Sat)
          · intro hImp hp₁Sat
            have hImp' : (semantics (World := World) sem₂).Sat m p₂ → (semantics (World := World) sem₂).Sat m q₂ := by
              simpa [semantics, Sat] using hImp
            have hp₂Sat : (semantics (World := World) sem₂).Sat m p₂ :=
              hp.1 hp₁Sat
            have hq₂Sat : (semantics (World := World) sem₂).Sat m q₂ :=
              hImp' hp₂Sat
            have hq₁Sat : (semantics (World := World) sem₁).Sat m q :=
              hq.2 hq₂Sat
            simpa [semantics, Sat] using hq₁Sat
      | _ => cases hR
  | iff p q ihp ihq =>
      cases s₂ with
      | iff p₂ q₂ =>
          rcases hR with ⟨hRp, hRq⟩
          have hp : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₂).Sat m p₂ :=
            ihp (s₂ := p₂) hRp
          have hq : (semantics (World := World) sem₁).Sat m q ↔ (semantics (World := World) sem₂).Sat m q₂ :=
            ihq (s₂ := q₂) hRq
          constructor
          · intro hIff
            have hIff' : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₁).Sat m q := by
              simpa [semantics, Sat] using hIff
            have hIff₂ : (semantics (World := World) sem₂).Sat m p₂ ↔ (semantics (World := World) sem₂).Sat m q₂ := by
              constructor
              · intro hp₂Sat
                have hp₁Sat : (semantics (World := World) sem₁).Sat m p :=
                  hp.2 hp₂Sat
                have hq₁Sat : (semantics (World := World) sem₁).Sat m q :=
                  (hIff').1 hp₁Sat
                exact hq.1 hq₁Sat
              · intro hq₂Sat
                have hq₁Sat : (semantics (World := World) sem₁).Sat m q :=
                  hq.2 hq₂Sat
                have hp₁Sat : (semantics (World := World) sem₁).Sat m p :=
                  (hIff').2 hq₁Sat
                exact hp.1 hp₁Sat
            simpa [semantics, Sat] using hIff₂
          · intro hIff
            have hIff' : (semantics (World := World) sem₂).Sat m p₂ ↔ (semantics (World := World) sem₂).Sat m q₂ := by
              simpa [semantics, Sat] using hIff
            have hIff₁ : (semantics (World := World) sem₁).Sat m p ↔ (semantics (World := World) sem₁).Sat m q := by
              constructor
              · intro hp₁Sat
                have hp₂Sat : (semantics (World := World) sem₂).Sat m p₂ :=
                  hp.1 hp₁Sat
                have hq₂Sat : (semantics (World := World) sem₂).Sat m q₂ :=
                  (hIff').1 hp₂Sat
                exact hq.2 hq₂Sat
              · intro hq₁Sat
                have hq₂Sat : (semantics (World := World) sem₂).Sat m q₂ :=
                  hq.1 hq₁Sat
                have hp₂Sat : (semantics (World := World) sem₂).Sat m p₂ :=
                  (hIff').2 hq₂Sat
                exact hp.2 hp₂Sat
            simpa [semantics, Sat] using hIff₁
      | _ => cases hR
  | forall_ g ih =>
      cases s₂ with
      | forall_ g₂ =>
          rcases hR with ⟨hEq, hRel⟩
          cases hEq
          constructor
          · intro hAll
            have hAll' : ∀ x, (semantics (World := World) sem₁).Sat m (g x) := by
              simpa [semantics, Sat] using hAll
            have hAll₂ : ∀ x, (semantics (World := World) sem₂).Sat m (g₂ x) := by
              intro x
              exact (ih x (g₂ x) (hRel x)).1 (hAll' x)
            simpa [semantics, Sat] using hAll₂
          · intro hAll
            have hAll' : ∀ x, (semantics (World := World) sem₂).Sat m (g₂ x) := by
              simpa [semantics, Sat] using hAll
            have hAll₁ : ∀ x, (semantics (World := World) sem₁).Sat m (g x) := by
              intro x
              exact (ih x (s₂ := g₂ x) (hRel x)).2 (hAll' x)
            simpa [semantics, Sat] using hAll₁
      | _ => cases hR
  | exists_ g ih =>
      cases s₂ with
      | exists_ g₂ =>
          rcases hR with ⟨hEq, hRel⟩
          cases hEq
          constructor
          · intro hEx
            have hEx' : ∃ x, (semantics (World := World) sem₁).Sat m (g x) := by
              simpa [semantics, Sat] using hEx
            rcases hEx' with ⟨x, hx⟩
            have hx₂ : (semantics (World := World) sem₂).Sat m (g₂ x) :=
              (ih x (g₂ x) (hRel x)).1 hx
            simpa [semantics, Sat] using ⟨x, hx₂⟩
          · intro hEx
            have hEx' : ∃ x, (semantics (World := World) sem₂).Sat m (g₂ x) := by
              simpa [semantics, Sat] using hEx
            rcases hEx' with ⟨x, hx⟩
            have hx₁ : (semantics (World := World) sem₁).Sat m (g x) :=
              (ih x (s₂ := g₂ x) (hRel x)).2 hx
            simpa [semantics, Sat] using ⟨x, hx₁⟩
      | _ => cases hR

theorem relSound_relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (R : TranslationRel Atom₁ Atom₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R) :
    RelSound (semantics (World := World) sem₁) (semantics (World := World) sem₂)
      (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) := by
  intro m s₁ s₂ hR hSat
  exact (sat_iff_of_relLift (World := World) (sem₁ := sem₁) (sem₂ := sem₂) (R := R) hSound hComplete m s₁ s₂ hR).1 hSat

theorem relComplete_relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (R : TranslationRel Atom₁ Atom₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R) :
    RelComplete (semantics (World := World) sem₁) (semantics (World := World) sem₂)
      (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) := by
  intro m s₁ s₂ hR hSat
  exact (sat_iff_of_relLift (World := World) (sem₁ := sem₁) (sem₂ := sem₂) (R := R) hSound hComplete m s₁ s₂ hR).2 hSat

def witnessTotalOn_relLift_of_choose {World : Type u} {Atom₁ Atom₂ : Type (max u 1)}
    (R : TranslationRel Atom₁ Atom₂) (choose : ∀ a : Atom₁, Witnessed R a)
    (T : Theory (StructuredSentence World Atom₁)) :
    Theory.WitnessTotalOn (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) T :=
  fun s _ => witnessedLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R choose s

theorem entails_iff_entails_relMap_of_witnessTotal_relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (R : TranslationRel Atom₁ Atom₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R)
    (T : Theory (StructuredSentence World Atom₁)) (s₁ : StructuredSentence World Atom₁) (s₂ : StructuredSentence World Atom₂)
    (hTotal : Theory.WitnessTotalOn (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) T)
    (hR : relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R s₁ s₂) :
    Entails (semantics (World := World) sem₁) T s₁ ↔
      Entails (semantics (World := World) sem₂) (Theory.relMap (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) T) s₂ := by
  simpa using
    (Foet.entails_iff_entails_relMap_of_witnessTotal
      (sem₁ := semantics (World := World) sem₁)
      (sem₂ := semantics (World := World) sem₂)
      (R := relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R)
      (T := T) (s₁ := s₁) (s₂ := s₂)
      (hSound := relSound_relLift (World := World) (sem₁ := sem₁) (sem₂ := sem₂) (R := R) hSound hComplete)
      (hComplete := relComplete_relLift (World := World) (sem₁ := sem₁) (sem₂ := sem₂) (R := R) hSound hComplete)
      (hTotal := hTotal)
      (hR := hR))

theorem entails_iff_entails_relMap_of_choose_relLift {World : Type u} {Atom₁ Atom₂ : Type (max u 1)} {M : Type v}
    (sem₁ : Semantics Atom₁ M) (sem₂ : Semantics Atom₂ M) (R : TranslationRel Atom₁ Atom₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R)
    (choose : ∀ a : Atom₁, Witnessed R a)
    (T : Theory (StructuredSentence World Atom₁)) (s₁ : StructuredSentence World Atom₁) (s₂ : StructuredSentence World Atom₂)
    (hR : relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R s₁ s₂) :
    Entails (semantics (World := World) sem₁) T s₁ ↔
      Entails (semantics (World := World) sem₂) (Theory.relMap (relLift (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R) T) s₂ := by
  exact entails_iff_entails_relMap_of_witnessTotal_relLift (World := World) (sem₁ := sem₁) (sem₂ := sem₂) (R := R)
    hSound hComplete (T := T) (s₁ := s₁) (s₂ := s₂)
    (hTotal := witnessTotalOn_relLift_of_choose (World := World) (Atom₁ := Atom₁) (Atom₂ := Atom₂) R choose T)
    (hR := hR)

end StructuredSentence

end Foet
