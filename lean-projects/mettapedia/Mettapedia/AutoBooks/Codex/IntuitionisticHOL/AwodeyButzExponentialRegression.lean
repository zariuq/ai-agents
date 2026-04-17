import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzExponential

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzExponentialRegression

open TopologicalSpace TopologicalSpace.Opens
open EtaleSpace

variable {X : Type*} [TopologicalSpace X]

example {F E G : EtaleSpace X}
    (g : C(G.Carrier, (exp F E).Carrier))
    (hg : (exp F E).proj ∘ g = G.proj)
    (x : G.Carrier) :
    curry (uncurry g hg) (uncurry_proj g hg) x = g x :=
  curry_uncurry g hg x

example {F E G : EtaleSpace X}
    (f : C((prod G F).Carrier, E.Carrier))
    (hf : E.proj ∘ f = (prod G F).proj)
    (p : (prod G F).Carrier) :
    uncurry (curry f hf) (curry_proj f hf) p = f p :=
  uncurry_curry f hf p

example (E F : EtaleSpace X) (U : Opens X) (s : (exp F E).SectionOn U) :
    expSectionOfLocalMorphism E F U (localMorphismOfExpSection E F U s) = s :=
  expSectionOfLocalMorphism_localMorphismOfExpSection E F U s

example (E F : EtaleSpace X) (U : Opens X) (f : LocalMorphism F E U) :
    localMorphismOfExpSection E F U (expSectionOfLocalMorphism E F U f) = f :=
  localMorphismOfExpSection_expSectionOfLocalMorphism E F U f

example (E F : EtaleSpace X) (U : Opens X) {f g : LocalMorphism F E U}
    (hfg : f ≠ g) :
    expSectionOfLocalMorphism E F U f ≠ expSectionOfLocalMorphism E F U g := by
  intro hEq
  apply hfg
  calc
    f = localMorphismOfExpSection E F U (expSectionOfLocalMorphism E F U f) := by
      simpa using (localMorphismOfExpSection_expSectionOfLocalMorphism E F U f).symm
    _ = localMorphismOfExpSection E F U (expSectionOfLocalMorphism E F U g) := by
      exact congrArg (localMorphismOfExpSection E F U) hEq
    _ = g := by
      simpa using localMorphismOfExpSection_expSectionOfLocalMorphism E F U g

example (E F : EtaleSpace X) (U : Opens X) {s t : (exp F E).SectionOn U}
    (hst : s ≠ t) :
    localMorphismOfExpSection E F U s ≠ localMorphismOfExpSection E F U t := by
  intro hEq
  apply hst
  calc
    s = expSectionOfLocalMorphism E F U (localMorphismOfExpSection E F U s) := by
      simpa using (expSectionOfLocalMorphism_localMorphismOfExpSection E F U s).symm
    _ = expSectionOfLocalMorphism E F U (localMorphismOfExpSection E F U t) := by
      exact congrArg (expSectionOfLocalMorphism E F U) hEq
    _ = t := by
      simpa using expSectionOfLocalMorphism_localMorphismOfExpSection E F U t

end AwodeyButzExponentialRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
