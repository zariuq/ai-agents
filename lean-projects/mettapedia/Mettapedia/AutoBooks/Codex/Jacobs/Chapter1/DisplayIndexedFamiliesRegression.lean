import Mettapedia.AutoBooks.Codex.Jacobs.Chapter1.DisplayIndexedFamilies

namespace Mettapedia.AutoBooks.Codex.Jacobs.Chapter1

namespace Regression

inductive Idx where
  | left
  | right
  deriving DecidableEq, Repr

inductive DemoCarrier where
  | a
  | b
  | c
  deriving DecidableEq, Repr

open Idx DemoCarrier
open DisplayFamily

def demoFamily : DisplayFamily Idx where
  Carrier := DemoCarrier
  proj
    | .a => .left
    | .b => .left
    | .c => .right

def u : Bool → Idx
  | true => .left
  | false => .right

def v : Unit → Bool := fun _ => true

example : fiber demoFamily .left := ⟨.a, rfl⟩

example : demoFamily.proj .c ≠ .left := by
  decide

example :
    (reindexIdEquiv demoFamily).toFun ⟨.left, ⟨.a, rfl⟩⟩ = .a := rfl

example :
    (reindexIdEquiv demoFamily).invFun .c = ⟨.right, ⟨.c, rfl⟩⟩ := rfl

example :
    (reindexCompEquiv v u demoFamily).toFun
      ⟨(), ⟨⟨true, ⟨.a, rfl⟩⟩, rfl⟩⟩ =
        ⟨(), ⟨.a, rfl⟩⟩ := rfl

example :
    (reindexCompEquiv v u demoFamily).invFun
      ⟨(), ⟨.b, rfl⟩⟩ =
        ⟨(), ⟨⟨true, ⟨.b, rfl⟩⟩, rfl⟩⟩ := rfl

end Regression

end Mettapedia.AutoBooks.Codex.Jacobs.Chapter1
