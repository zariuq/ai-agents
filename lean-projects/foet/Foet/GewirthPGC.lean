import Foet.EthicsCore

set_option autoImplicit false

namespace Foet

namespace Gewirth

universe u

abbrev Meaning (Ctx : Type u) (World : Type u) : Type u :=
  Ctx → Formula World

abbrev Property (Entity : Type u) (Ctx : Type u) (World : Type u) : Type u :=
  Entity → Meaning Ctx World

abbrev Subset {World : Type u} (X Y : Formula World) : Prop :=
  ∀ w, X w → Y w

abbrev Inter {World : Type u} (X Y : Formula World) : Formula World :=
  fun w => X w ∧ Y w

abbrev SetEq {World : Type u} (X Y : Formula World) : Prop :=
  ∀ w, X w ↔ Y w

abbrev Instantiated {World : Type u} (X : Formula World) : Prop :=
  ∃ w, X w

def ldTrueCtx {Ctx : Type u} {World : Type u} (worldOf : Ctx → World) (φ : Meaning Ctx World) (c : Ctx) : Prop :=
  φ c (worldOf c)

def ldValid {Ctx : Type u} {World : Type u} (worldOf : Ctx → World) (φ : Meaning Ctx World) : Prop :=
  ∀ c, ldTrueCtx (Ctx := Ctx) (World := World) worldOf φ c

def modValid {Ctx : Type u} {World : Type u} (φ : Meaning Ctx World) : Prop :=
  ∀ c w, φ c w

def boxD {Ctx : Type u} {World : Type u} (worldOf : Ctx → World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun _ _ => ldValid (Ctx := Ctx) (World := World) worldOf φ

def boxA {Ctx : Type u} {World : Type u} (av : World → Formula World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∀ v, av w v → φ c v

def diaA {Ctx : Type u} {World : Type u} (av : World → Formula World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∃ v, av w v ∧ φ c v

def boxP {Ctx : Type u} {World : Type u} (pv : World → Formula World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∀ v, pv w v → φ c v

def diaP {Ctx : Type u} {World : Type u} (pv : World → Formula World) (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w => ∃ v, pv w v ∧ φ c v

def Ocond {Ctx : Type u} {World : Type u} (ob : Formula World → Formula World → Prop)
    (φ σ : Meaning Ctx World) : Meaning Ctx World :=
  fun c _ => ob (σ c) (φ c)

def Oi {Ctx : Type u} {World : Type u} (ob : Formula World → Formula World → Prop) (pv : World → Formula World)
    (φ : Meaning Ctx World) : Meaning Ctx World :=
  fun c w =>
    ob (pv w) (φ c) ∧ ∃ v, pv w v ∧ ¬ φ c v

def PPA {Ctx : Type u} {World : Type u} {Entity : Type u}
    (ActsOnPurpose : Entity → Meaning Ctx World → Meaning Ctx World) (a : Entity) : Meaning Ctx World :=
  fun c w => ∃ E : Meaning Ctx World, ActsOnPurpose a E c w

def NonInterference {Ctx : Type u} {World : Type u} {Entity : Type u}
    (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World) (a : Entity) (P : Entity → Meaning Ctx World) :
    Meaning Ctx World :=
  fun c w => ∀ b : Entity, ¬ InterferesWith b (P a) c w

def RightTo {Ctx : Type u} {World : Type u} {Entity : Type u} (ob : Formula World → Formula World → Prop)
    (pv : World → Formula World) (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World) (a : Entity)
    (P : Entity → Meaning Ctx World) : Meaning Ctx World :=
  Oi (Ctx := Ctx) (World := World) ob pv (NonInterference (Ctx := Ctx) (World := World) InterferesWith a P)

/-!
## Reusable packaging of the Gewirth embedding

The core theorem `PGC_strong` is written in a semantic-embedding style, with all non-logical symbols
(`ob`, `pv`, `ActsOnPurpose`, …) and all explications/semantic conditions passed as explicit arguments.

To avoid copy/paste across downstream lemmas (bridges, theory packaging, etc.), we additionally provide:
  - `PGCInterpretation`: bundles the non-logical symbols,
  - `PGCStatementName`: names the assumptions and the goal,
  - `PGCStatement`: defines each named statement as a HOL proposition,
  - `PGCAssumptions`: bundles proofs of the named assumptions,
  - `PGC_strong_ofAssumptions`: a reuse-friendly wrapper around `PGC_strong`.
-/

structure PGCInterpretation : Type (u + 1) where
  Ctx : Type u
  World : Type u
  Entity : Type u
  worldOf : Ctx → World
  av : World → Formula World
  pv : World → Formula World
  ob : Formula World → Formula World → Prop
  ActsOnPurpose : Entity → Meaning Ctx World → Meaning Ctx World
  NeedsForPurpose :
    Entity → (Entity → Meaning Ctx World) → Meaning Ctx World → Meaning Ctx World
  Good : Entity → Meaning Ctx World → Meaning Ctx World
  FWB : Entity → Meaning Ctx World
  InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World

inductive PGCStatementName : Type
  | sem_5a
  | sem_5b
  | sem_5e
  | explicationGoodness1
  | explicationGoodness2
  | explicationGoodness3
  | explicationFWB1
  | explicationFWB2
  | explicationFWB3
  | OIOAC
  | explicationInterference
  | PGC_strong
  deriving DecidableEq, Repr

def PGCStatement (I : PGCInterpretation) : PGCStatementName → Prop
  | .sem_5a =>
      ∀ X : Formula I.World, ¬ I.ob X (fun _ => False)
  | .sem_5b =>
      ∀ X Y Z : Formula I.World,
        SetEq (Inter X Y) (Inter X Z) → (I.ob X Y ↔ I.ob X Z)
  | .sem_5e =>
      ∀ X Y Z : Formula I.World,
        Subset Y X → I.ob X Z → Instantiated (Inter Y Z) → I.ob Y Z
  | .explicationGoodness1 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ a P, I.ActsOnPurpose a P c w → I.Good a P c w)
  | .explicationGoodness2 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ (P : Meaning I.Ctx I.World) (M : I.Entity → Meaning I.Ctx I.World) (a : I.Entity),
          (I.Good a P c w ∧ I.NeedsForPurpose a M P c w) → I.Good a (M a) c w)
  | .explicationGoodness3 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ (φ : Meaning I.Ctx I.World) (a : I.Entity),
          diaP (Ctx := I.Ctx) (World := I.World) I.pv φ c w →
            Ocond (Ctx := I.Ctx) (World := I.World) I.ob φ
              (boxD (Ctx := I.Ctx) (World := I.World) I.worldOf (I.Good a φ)) c w)
  | .explicationFWB1 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ (P : Meaning I.Ctx I.World) (a : I.Entity), I.NeedsForPurpose a I.FWB P c w)
  | .explicationFWB2 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ a : I.Entity, diaP (Ctx := I.Ctx) (World := I.World) I.pv (I.FWB a) c w)
  | .explicationFWB3 =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ a : I.Entity,
          diaP (Ctx := I.Ctx) (World := I.World) I.pv (fun c' w' => ¬ I.FWB a c' w') c w)
  | .OIOAC =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ (φ : Meaning I.Ctx I.World),
          Oi (Ctx := I.Ctx) (World := I.World) I.ob I.pv φ c w →
            Oi (Ctx := I.Ctx) (World := I.World) I.ob I.pv
              (diaA (Ctx := I.Ctx) (World := I.World) I.av φ) c w)
  | .explicationInterference =>
      modValid (Ctx := I.Ctx) (World := I.World)
        (fun c w => ∀ (φ : Meaning I.Ctx I.World),
          (∃ b : I.Entity, I.InterferesWith b φ c w) ↔
            ¬ diaA (Ctx := I.Ctx) (World := I.World) I.av φ c w)
  | .PGC_strong =>
      ldValid (Ctx := I.Ctx) (World := I.World) I.worldOf
        (fun c w => ∀ x : I.Entity,
          PPA (Ctx := I.Ctx) (World := I.World) I.ActsOnPurpose x c w →
            RightTo (Ctx := I.Ctx) (World := I.World) (Entity := I.Entity)
              I.ob I.pv I.InterferesWith x I.FWB c w)

structure PGCAssumptions (I : PGCInterpretation) : Prop where
  sem_5a : PGCStatement I .sem_5a
  sem_5b : PGCStatement I .sem_5b
  sem_5e : PGCStatement I .sem_5e
  explicationGoodness1 : PGCStatement I .explicationGoodness1
  explicationGoodness2 : PGCStatement I .explicationGoodness2
  explicationGoodness3 : PGCStatement I .explicationGoodness3
  explicationFWB1 : PGCStatement I .explicationFWB1
  explicationFWB2 : PGCStatement I .explicationFWB2
  explicationFWB3 : PGCStatement I .explicationFWB3
  OIOAC : PGCStatement I .OIOAC
  explicationInterference : PGCStatement I .explicationInterference

theorem sem_5ab {World : Type u} {ob : Formula World → Formula World → Prop}
    (sem_5a : ∀ X, ¬ ob X (fun _ => False))
    (sem_5b : ∀ X Y Z, SetEq (Inter X Y) (Inter X Z) → (ob X Y ↔ ob X Z))
    {X Y : Formula World} :
    ob X Y → Instantiated (Inter X Y) := by
  classical
  intro hOb
  by_cases hInst : Instantiated (Inter X Y)
  · exact hInst
  ·
    have hEmpty : SetEq (Inter X Y) (Inter X (fun _ => False)) := by
      intro w
      constructor
      · intro hXY
        exfalso
        apply hInst
        exact ⟨w, hXY⟩
      · intro hXF
        cases hXF.2
    have hObFalse : ob X (fun _ => False) := by
      have hEq := (sem_5b X Y (fun _ => False) hEmpty).1 hOb
      simpa using hEq
    have : False :=
      (sem_5a X) hObFalse
    exact False.elim this

theorem CJ_14p {Ctx : Type u} {World : Type u} {ob : Formula World → Formula World → Prop} {pv : World → Formula World}
    (sem_5e : ∀ X Y Z, Subset Y X → ob X Z → Instantiated (Inter Y Z) → ob Y Z)
    (A B : Meaning Ctx World) :
    modValid (fun c w =>
      Ocond (Ctx := Ctx) (World := World) ob B A c w ∧
        boxP (Ctx := Ctx) (World := World) pv A c w ∧
          diaP (Ctx := Ctx) (World := World) pv B c w ∧
            diaP (Ctx := Ctx) (World := World) pv (fun c' w' => ¬ B c' w') c w →
              Oi (Ctx := Ctx) (World := World) ob pv B c w) := by
  intro c w
  intro h
  rcases h with ⟨hO, hBoxA, hDiaB, hDiaNotB⟩
  have hSubset : Subset (pv w) (A c) := by
    intro v hv
    exact hBoxA v hv
  have hInst : Instantiated (Inter (pv w) (B c)) := by
    rcases hDiaB with ⟨v, hv, hBv⟩
    exact ⟨v, hv, hBv⟩
  have hOb : ob (pv w) (B c) :=
    sem_5e (A c) (pv w) (B c) hSubset hO hInst
  refine ⟨hOb, ?_⟩
  rcases hDiaNotB with ⟨v, hv, hNotBv⟩
  exact ⟨v, hv, hNotBv⟩

theorem PGC_strong {Ctx : Type u} {World : Type u} {Entity : Type u}
    (worldOf : Ctx → World)
    (av pv : World → Formula World)
    (ob : Formula World → Formula World → Prop)
    (ActsOnPurpose : Entity → Meaning Ctx World → Meaning Ctx World)
    (NeedsForPurpose : Entity → (Entity → Meaning Ctx World) → Meaning Ctx World → Meaning Ctx World)
    (Good : Entity → Meaning Ctx World → Meaning Ctx World)
    (FWB : Entity → Meaning Ctx World)
    (InterferesWith : Entity → Meaning Ctx World → Meaning Ctx World)
    (sem_5a : ∀ X, ¬ ob X (fun _ => False))
    (sem_5b : ∀ X Y Z, SetEq (Inter X Y) (Inter X Z) → (ob X Y ↔ ob X Z))
    (sem_5e : ∀ X Y Z, Subset Y X → ob X Z → Instantiated (Inter Y Z) → ob Y Z)
    (explicationGoodness1 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ a P, ActsOnPurpose a P c w → Good a P c w))
    (explicationGoodness2 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ (P : Meaning Ctx World) (M : Entity → Meaning Ctx World) (a : Entity),
          (Good a P c w ∧ NeedsForPurpose a M P c w) → Good a (M a) c w))
    (explicationGoodness3 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ (φ : Meaning Ctx World) (a : Entity),
          diaP (Ctx := Ctx) (World := World) pv φ c w →
            Ocond (Ctx := Ctx) (World := World) ob φ (boxD (Ctx := Ctx) (World := World) worldOf (Good a φ)) c w))
    (explicationFWB1 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ (P : Meaning Ctx World) (a : Entity), NeedsForPurpose a FWB P c w))
    (explicationFWB2 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ a : Entity, diaP (Ctx := Ctx) (World := World) pv (FWB a) c w))
    (explicationFWB3 :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ a : Entity,
          diaP (Ctx := Ctx) (World := World) pv (fun c' w' => ¬ FWB a c' w') c w))
    (OIOAC :
      ldValid (Ctx := Ctx) (World := World) worldOf
        (fun c w => ∀ (φ : Meaning Ctx World),
          Oi (Ctx := Ctx) (World := World) ob pv φ c w →
            Oi (Ctx := Ctx) (World := World) ob pv (diaA (Ctx := Ctx) (World := World) av φ) c w))
    (explicationInterference :
      modValid (Ctx := Ctx) (World := World)
        (fun c w => ∀ (φ : Meaning Ctx World),
          (∃ b : Entity, InterferesWith b φ c w) ↔ ¬ diaA (Ctx := Ctx) (World := World) av φ c w)) :
    ldValid (Ctx := Ctx) (World := World) worldOf
      (fun c w => ∀ x : Entity, PPA (Ctx := Ctx) (World := World) ActsOnPurpose x c w →
        RightTo (Ctx := Ctx) (World := World) (Entity := Entity) ob pv InterferesWith x FWB c w) := by
  classical
  intro C
  intro x hxPPA
  rcases hxPPA with ⟨E, hActs⟩

  have _hGoodE : Good x E C (worldOf C) := by
    have hGood1 := explicationGoodness1 C
    exact hGood1 x E hActs

  have hNeedsAllPurposes : ldValid (Ctx := Ctx) (World := World) worldOf (fun c w => ∀ P : Meaning Ctx World,
        NeedsForPurpose x FWB P c w) := by
    intro c
    have hFWB1 := explicationFWB1 c
    intro P
    exact hFWB1 P x

  have hGoodFWBValid :
      ldValid (Ctx := Ctx) (World := World) worldOf (Good x (FWB x)) := by
    have hCondValid :
        ldValid (Ctx := Ctx) (World := World) worldOf
          (Ocond (Ctx := Ctx) (World := World) ob (FWB x)
            (boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x)))) := by
      intro c
      have hDia : diaP (Ctx := Ctx) (World := World) pv (FWB x) c (worldOf c) := by
        have hFWB2 := explicationFWB2 c
        exact hFWB2 x
      have hGood3 := explicationGoodness3 c
      exact hGood3 (FWB x) x hDia
    have hAtC : Ocond (Ctx := Ctx) (World := World) ob (FWB x)
        (boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) C (worldOf C) :=
      hCondValid C
    have hInst :
        Instantiated (Inter
          ((boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) C)
          ((FWB x) C)) :=
      sem_5ab (World := World) (ob := ob) sem_5a sem_5b (X := (boxD worldOf (Good x (FWB x)) C))
        (Y := (FWB x C)) hAtC
    rcases hInst with ⟨w, hBox, hFWB⟩
    have hGoodFWBFromBox : ldValid (Ctx := Ctx) (World := World) worldOf (Good x (FWB x)) := by
      simpa [boxD, ldValid, ldTrueCtx] using hBox
    have hNeedFWB : ldValid (Ctx := Ctx) (World := World) worldOf (NeedsForPurpose x FWB (FWB x)) := by
      intro c
      have hNeeds := hNeedsAllPurposes c
      exact hNeeds (FWB x)
    have hGoodAndNeed :
        ldValid (Ctx := Ctx) (World := World) worldOf (fun c w =>
          Good x (FWB x) c w ∧ NeedsForPurpose x FWB (FWB x) c w) := by
      intro c
      refine ⟨hGoodFWBFromBox c, hNeedFWB c⟩
    have hGood2 := explicationGoodness2
    -- Use Goodness2 with `P := FWB x` and `M := FWB` to re-derive `Good x (FWB x)` from the need.
    intro c
    have hG2 := hGood2 c
    have hAnd := hGoodAndNeed c
    exact hG2 (FWB x) FWB x hAnd

  have hBoxDGoodAtC :
      (boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) C (worldOf C) := by
    simpa [boxD] using hGoodFWBValid

  have hCondAtC :
      Ocond (Ctx := Ctx) (World := World) ob (FWB x)
          (boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) C (worldOf C) := by
    have hDia : diaP (Ctx := Ctx) (World := World) pv (FWB x) C (worldOf C) := by
      have hFWB2 := explicationFWB2 C
      exact hFWB2 x
    have hGood3 := explicationGoodness3 C
    exact hGood3 (FWB x) x hDia

  have hOiFWBAtC :
      Oi (Ctx := Ctx) (World := World) ob pv (FWB x) C (worldOf C) := by
    have hBoxP : boxP (Ctx := Ctx) (World := World) pv
        (boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) C (worldOf C) := by
      intro v hv
      simpa [boxD] using hBoxDGoodAtC
    have hDiaB : diaP (Ctx := Ctx) (World := World) pv (FWB x) C (worldOf C) := by
      have hFWB2 := explicationFWB2 C
      exact hFWB2 x
    have hDiaNotB : diaP (Ctx := Ctx) (World := World) pv (fun c' w' => ¬ FWB x c' w') C (worldOf C) := by
      have hFWB3 := explicationFWB3 C
      exact hFWB3 x
    have hCJ := CJ_14p (Ctx := Ctx) (World := World) (ob := ob) (pv := pv) sem_5e
      (A := boxD (Ctx := Ctx) (World := World) worldOf (Good x (FWB x))) (B := FWB x)
    exact hCJ C (worldOf C) ⟨hCondAtC, hBoxP, hDiaB, hDiaNotB⟩

  have hOiDiaAAtC :
      Oi (Ctx := Ctx) (World := World) ob pv (diaA (Ctx := Ctx) (World := World) av (FWB x)) C (worldOf C) := by
    have hOIOAC := OIOAC C
    exact hOIOAC (FWB x) hOiFWBAtC

  have hDiaA_iff_nonInterference :
      ∀ w, diaA (Ctx := Ctx) (World := World) av (FWB x) C w ↔
        NonInterference (Ctx := Ctx) (World := World) InterferesWith x FWB C w := by
    intro w
    have hInt := explicationInterference C w (FWB x)
    constructor
    · intro hDia
      intro b hInterf
      have : ∃ b' : Entity, InterferesWith b' (FWB x) C w :=
        ⟨b, hInterf⟩
      have : ¬ diaA (Ctx := Ctx) (World := World) av (FWB x) C w :=
        (hInt).1 this
      exact this hDia
    · intro hNoInterf
      by_cases hDia : diaA (Ctx := Ctx) (World := World) av (FWB x) C w
      · exact hDia
      ·
        have : ∃ b : Entity, InterferesWith b (FWB x) C w :=
          (hInt).2 hDia
        rcases this with ⟨b, hb⟩
        have : False :=
          hNoInterf b hb
        exact False.elim this

  have hRightToAtC :
      RightTo (Ctx := Ctx) (World := World) (Entity := Entity) ob pv InterferesWith x FWB C (worldOf C) := by
    -- `RightTo` is definitional: `Oi (NonInterference …)`.
    -- We transport `Oi` along logical equivalence using `sem_5b`.
    have hSetEq :
        SetEq
          (Inter (pv (worldOf C)) ((diaA (Ctx := Ctx) (World := World) av (FWB x)) C))
          (Inter (pv (worldOf C))
            (NonInterference (Ctx := Ctx) (World := World) InterferesWith x FWB C)) := by
      intro w
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        exact (hDiaA_iff_nonInterference w).1 h.2
      · intro h
        refine ⟨h.1, ?_⟩
        exact (hDiaA_iff_nonInterference w).2 h.2
    have hObPart :
        ob (pv (worldOf C)) ((diaA (Ctx := Ctx) (World := World) av (FWB x)) C) ↔
          ob (pv (worldOf C))
            (NonInterference (Ctx := Ctx) (World := World) InterferesWith x FWB C) := by
      exact sem_5b (pv (worldOf C)) ((diaA (Ctx := Ctx) (World := World) av (FWB x)) C)
        (NonInterference (Ctx := Ctx) (World := World) InterferesWith x FWB C) hSetEq
    rcases hOiDiaAAtC with ⟨hOb, hVio⟩
    refine ⟨(hObPart).1 hOb, ?_⟩
    rcases hVio with ⟨v, hv, hNotDia⟩
    refine ⟨v, hv, ?_⟩
    intro hNI
    exact hNotDia ((hDiaA_iff_nonInterference v).2 hNI)

  -- `RightTo` is an `Oi` fact, so the evaluation world only matters at `WorldOf C`.
  exact hRightToAtC

theorem PGC_strong_ofAssumptions (I : PGCInterpretation) (h : PGCAssumptions I) :
    PGCStatement I .PGC_strong := by
  -- This is just `PGC_strong` with all symbols and assumptions pulled from the bundled interpretation.
  exact
    PGC_strong (Ctx := I.Ctx) (World := I.World) (Entity := I.Entity)
      (worldOf := I.worldOf)
      (av := I.av) (pv := I.pv) (ob := I.ob)
      (ActsOnPurpose := I.ActsOnPurpose)
      (NeedsForPurpose := I.NeedsForPurpose)
      (Good := I.Good) (FWB := I.FWB) (InterferesWith := I.InterferesWith)
      (sem_5a := h.sem_5a)
      (sem_5b := h.sem_5b)
      (sem_5e := h.sem_5e)
      (explicationGoodness1 := h.explicationGoodness1)
      (explicationGoodness2 := h.explicationGoodness2)
      (explicationGoodness3 := h.explicationGoodness3)
      (explicationFWB1 := h.explicationFWB1)
      (explicationFWB2 := h.explicationFWB2)
      (explicationFWB3 := h.explicationFWB3)
      (OIOAC := h.OIOAC)
      (explicationInterference := h.explicationInterference)

end Gewirth

end Foet
