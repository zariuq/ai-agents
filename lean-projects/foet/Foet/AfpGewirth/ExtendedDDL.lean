import Foet.AfpGewirth.CJDDLplus

set_option autoImplicit false

namespace Foet
namespace AFP
namespace Gewirth

universe v

/-!
`ExtendedDDL` (AFP session) extends the DDL embedding with:
- Kaplan-style context features (`Agent`, `World`)
- LD (indexical) validity `⟦_⟧^D` and the derived a-priori necessity `□ᴰ`
- Higher-order quantifiers at the object-language level (`mforall`, `mexists`)

This is a clean port intended to mirror `GewirthPGCProof/ExtendedDDL.thy`.

## Isabelle ↔ Lean identifier map (LD layer)

- `Agent :: c ⇒ e` ↔ `Agent : c → e`
- `World :: c ⇒ w` ↔ `World : c → w`
- `\<lfloor>φ\<rfloor>\<^sub>c` ↔ `ldtruectx φ c`
- `\<lfloor>φ\<rfloor>\<^sup>D` ↔ `ldvalid φ`
- `\<^bold>\<box>\<^sup>D φ` ↔ `boxD φ`

Note: as in the AFP sources, we use the same object-language type `m := c -> w -> Prop`
for both classical modal validity and Kaplan's indexical validity; only the *validity*
predicate changes.
-/

/-! ### Context features -/

axiom Agent : c → e
axiom World : c → w

/-! ### LD truth and validity -/

def ldtruectx (φ : m) (ctx : c) : Prop :=
  φ ctx (World ctx)

def ldvalid (φ : m) : Prop :=
  ∀ ctx, ldtruectx φ ctx

/-! ### A-priori (indexical) necessity operator `□ᴰ` -/

def boxD (φ : m) : m :=
  fun _ _ => ldvalid φ

/-! ### Object-language connectives and quantifiers -/

def mnot (A : m) : m :=
  fun ctx w0 => ¬ A ctx w0

def mand (A B : m) : m :=
  fun ctx w0 => A ctx w0 ∧ B ctx w0

def mor (A B : m) : m :=
  fun ctx w0 => A ctx w0 ∨ B ctx w0

def mimp (A B : m) : m :=
  fun ctx w0 => A ctx w0 → B ctx w0

def miff (A B : m) : m :=
  fun ctx w0 => A ctx w0 ↔ B ctx w0

def mforall {α : Type v} (Φ : α → m) : m :=
  fun ctx w0 => ∀ x, Φ x ctx w0

def mexists {α : Type v} (Φ : α → m) : m :=
  fun ctx w0 => ∃ x, Φ x ctx w0

/-!
## Isabelle-style notation (optional)

These are cosmetic and intended to make `GewirthArgument.lean` read closer to
the AFP Isabelle development.
-/

notation "⌊" φ "⌋ᴰ" => ldvalid φ
notation "⌊" φ "⌋₍" c "₎" => ldtruectx φ c
notation "□ᴰ" => boxD

prefix:75 "¬ₘ" => mnot
infixr:70 " ∧ₘ " => mand
infixr:65 " ∨ₘ " => mor
infixr:60 " →ₘ " => mimp
infixr:55 " ↔ₘ " => miff

notation "∀ₘ" => mforall
notation "∃ₘ" => mexists

/-! ### Basic relationships between modal and LD validity -/

theorem modValid_implies_ldvalid {A : m} : ⌊A⌋ → ⌊A⌋ᴰ := by
  intro h ctx
  exact h ctx (World ctx)

theorem NecLD {A : m} : ⌊A⌋ᴰ → ⌊□ᴰ A⌋ᴰ := by
  intro h ctx
  simpa [ldtruectx, boxD] using h

end Gewirth
end AFP
end Foet
