import Mettapedia.OSLF.MeTTaCore.Atom
import Mettapedia.OSLF.MeTTaCore.Bindings
import Mettapedia.OSLF.MeTTaCore.Atomspace
import Mettapedia.OSLF.MeTTaCore.State
import Mettapedia.OSLF.MeTTaCore.PatternMatch
import Mettapedia.OSLF.MeTTaCore.MinimalOps
import Mettapedia.OSLF.MeTTaCore.RewriteRules
import Mettapedia.OSLF.MeTTaCore.Types
import Mettapedia.OSLF.MeTTaCore.Bridge
import Mettapedia.OSLF.MeTTaCore.Properties

/-!
# MeTTaCore - MeTTa Interpreter Specification

Formalization of the MeTTa interpreter specification from Hyperon Experimental
and the Meta-MeTTa paper.

## Module Structure

* `Atom` - Core 4-constructor atom datatype and GroundedType typeclass
* `Bindings` - Variable bindings with transitive closure
* `Atomspace` - Queryable knowledge store with equations
* `State` - 4-register interpreter state ⟨i, k, w, o⟩
* `PatternMatch` - Bidirectional unification algorithm
* `MinimalOps` - Hyperon Experimental operations (eval, chain, unify, etc.)
* `RewriteRules` - Meta-MeTTa rewrite rules
* `Types` - MeTTa type system (meta-types, HasType judgment)
* `Bridge` - Integration with MeTTaIL language definitions
* `Properties` - Confluence, type preservation, progress

## References

* [Hyperon Experimental Spec](https://trueagi-io.github.io/hyperon-experimental/metta/)
* Meta-MeTTa paper (Meredith, Goertzel, Warrell, Vandervorst)
-/
