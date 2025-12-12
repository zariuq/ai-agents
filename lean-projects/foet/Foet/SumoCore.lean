import Foet.Theory

set_option autoImplicit false

namespace Foet

/-
Minimal “SUMO-like” upper-ontology kernel in Lean:

- A single universe of discourse `Entity`
- `Class` as a set of entities
- `instanceOf` and `subclass` as definitional set membership/subset

This is intentionally tiny: it’s usually better to back-trace and import only the
fragment you need, rather than port all of SUMO up front.
-/

universe u

abbrev Class (Entity : Type u) : Type u := Set Entity

abbrev instanceOf {Entity : Type u} (x : Entity) (C : Class Entity) : Prop :=
  C x

abbrev subclass {Entity : Type u} (C D : Class Entity) : Prop :=
  ∀ x, instanceOf x C → instanceOf x D

end Foet
