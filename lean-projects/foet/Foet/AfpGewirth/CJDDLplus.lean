set_option autoImplicit false

namespace Foet
namespace AFP
namespace Gewirth

/-!
This directory is a “clean port” of the AFP session `GewirthPGCProof`,
mirroring the Isabelle/HOL file structure:

1) `CJDDLplus`: core DDL semantic conditions + shallow semantic embedding primitives.
2) `ExtendedDDL`: Kaplan-style contexts + LD validity + `□ᴰ`.
3) `GewirthArgument`: Gewirth-specific explications + the PGC proofs.

This is intentionally separate from the FOET ethics ontology integration layer.

## Isabelle ↔ Lean identifier map (core)

- `w, e, c`  ↔  `w, e, c`
- `wo`       ↔  `wo := w -> Prop`
- `m`        ↔  `m := c -> w -> Prop`
- `av, pv, ob` ↔ `av, pv, ob`
- `\<lfloor>_\<rfloor>` / `modvalid` ↔ `modValid`
- `\<^bold>\<box>\<^sub>a`, `\<^bold>\<diamond>\<^sub>a` ↔ `boxa`, `diaa`
- `\<^bold>\<box>\<^sub>p`, `\<^bold>\<diamond>\<^sub>p` ↔ `boxp`, `diap`
- `\<^bold>O\<langle>_ | _\<rangle>` ↔ `Ocond`
- `\<^bold>O\<^sub>i` ↔ `Oi`

Note: we keep the *definitions* ASCII-stable, but we also provide Isabelle-style
Unicode notation (see below) for readability.
-/

/-! ### Types (Isabelle: typedecl w e c) -/

axiom w : Type -- possible worlds
axiom e : Type -- individuals/entities
axiom c : Type -- Kaplanian contexts

/-! ### Derived types (Isabelle: wo, cwo, m) -/

abbrev wo : Type := w -> Prop
abbrev m : Type := c -> w -> Prop

/-! ### Basic set operations on world propositions (type `wo`) -/

abbrev subset (X Y : wo) : Prop := ∀ w0 : w, X w0 -> Y w0
abbrev inter (X Y : wo) : wo := fun w0 : w => X w0 ∧ Y w0
abbrev union (X Y : wo) : wo := fun w0 : w => X w0 ∨ Y w0
abbrev compl (X : wo) : wo := fun w0 : w => ¬ X w0
abbrev instantiated (X : wo) : Prop := ∃ w0 : w, X w0
abbrev setEq (X Y : wo) : Prop := ∀ w0 : w, X w0 ↔ Y w0
abbrev univSet : wo := fun (_ : w) => True
abbrev emptySet : wo := fun (_ : w) => False

/-! ### DDL frame primitives and semantic conditions (Isabelle: consts av pv ob; axiomatization sem_*) -/

axiom av : w -> wo
axiom pv : w -> wo
axiom ob : wo -> wo -> Prop

axiom sem_3a : ∀ w0 : w, instantiated (av w0)
axiom sem_4a : ∀ w0 : w, subset (av w0) (pv w0)
axiom sem_4b : ∀ w0 : w, pv w0 w0
axiom sem_5a : ∀ X : wo, ¬ ob X emptySet
axiom sem_5b : ∀ X Y Z : wo, setEq (inter X Y) (inter X Z) → (ob X Y ↔ ob X Z)
axiom sem_5c : ∀ X Y Z : wo, instantiated (inter (inter X Y) Z) → ob X Y → ob X Z → ob X (inter Y Z)
axiom sem_5d : ∀ X Y Z : wo, subset Y X → ob X Y → subset X Z → ob Z (union (inter Z (compl X)) Y)
axiom sem_5e : ∀ X Y Z : wo, subset Y X → ob X Z → instantiated (inter Y Z) → ob Y Z

/-! ### Shallow semantic embedding primitives (enough for the Gewirth proof) -/

def boxa (A : m) : m :=
  fun ctx w0 => ∀ v, av w0 v -> A ctx v

def diaa (A : m) : m :=
  fun ctx w0 => ∃ v, av w0 v ∧ A ctx v

def boxp (A : m) : m :=
  fun ctx w0 => ∀ v, pv w0 v -> A ctx v

def diap (A : m) : m :=
  fun ctx w0 => ∃ v, pv w0 v ∧ A ctx v

def Ocond (φ σ : m) : m :=
  fun ctx _ => ob (σ ctx) (φ ctx)

def Oi (φ : m) : m :=
  fun ctx w0 => ob (pv w0) (φ ctx) ∧ ∃ v, pv w0 v ∧ ¬ φ ctx v

def modValid (A : m) : Prop :=
  ∀ ctx w0, A ctx w0

/-!
## Isabelle-style notation (optional)

These notations are purely cosmetic: all core definitions remain available under
their ASCII names (`boxa`, `diap`, `Ocond`, ...).  They are scoped to this
namespace, so importing this module does not globally redefine symbols.
-/

notation "□ₐ" => boxa
notation "◇ₐ" => diaa
notation "□ₚ" => boxp
notation "◇ₚ" => diap
notation "O⟨" φ " | " σ "⟩" => Ocond φ σ
notation "Oᵢ" => Oi
notation "⌊" A "⌋" => modValid A

/-! ### Lemmas used by the Gewirth proof -/

theorem sem_5ab {X Y : wo} : ob X Y → instantiated (inter X Y) := by
  classical
  intro hOb
  by_cases hInst : instantiated (inter X Y)
  · exact hInst
  ·
    have hEmpty : setEq (inter X Y) (inter X emptySet) := by
      intro w0
      constructor
      · intro hXY
        exfalso
        apply hInst
        exact ⟨w0, hXY⟩
      · intro hXF
        cases hXF.2
    have hObFalse : ob X emptySet := by
      have hEq := (sem_5b X Y emptySet hEmpty).1 hOb
      simpa using hEq
    exact False.elim ((sem_5a X) hObFalse)

/-!
Kant's Law (Carmo–Jones DDL): an ideal obligation implies metaphysical possibility.

AFP (Isabelle) counterpart (in `GewirthArgument.thy`):
`\<lfloor> O\<^sub>i\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sub>p\<phi> \<rfloor>` using `sem_5ab`.
-/
theorem KantLaw (φ : m) : ⌊fun ctx w0 => Oᵢ φ ctx w0 -> ◇ₚ φ ctx w0⌋ := by
  intro ctx w0 hOi
  have hOb : ob (pv w0) (φ ctx) := hOi.1
  rcases sem_5ab (X := pv w0) (Y := φ ctx) hOb with ⟨v, hv⟩
  exact ⟨v, hv.1, hv.2⟩

theorem CJ_14p (A B : m) :
    ⌊fun ctx w0 =>
      O⟨B | A⟩ ctx w0 ∧ □ₚ A ctx w0 ∧ ◇ₚ B ctx w0 ∧ ◇ₚ (fun ctx' w' => ¬ B ctx' w') ctx w0 ->
        Oᵢ B ctx w0⌋ := by
  intro ctx w0
  intro h
  rcases h with ⟨hO, hBoxA, hDiaB, hDiaNotB⟩
  have hSubset : subset (pv w0) (A ctx) := by
    intro v hv
    exact hBoxA v hv
  have hInst : instantiated (inter (pv w0) (B ctx)) := by
    rcases hDiaB with ⟨v, hv, hBv⟩
    exact ⟨v, hv, hBv⟩
  have hOb : ob (pv w0) (B ctx) :=
    sem_5e (A ctx) (pv w0) (B ctx) hSubset hO hInst
  refine ⟨hOb, ?_⟩
  rcases hDiaNotB with ⟨v, hv, hNotBv⟩
  exact ⟨v, hv, hNotBv⟩

end Gewirth
end AFP
end Foet
