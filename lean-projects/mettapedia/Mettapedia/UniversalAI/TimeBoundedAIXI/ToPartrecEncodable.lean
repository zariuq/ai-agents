import Mathlib.Computability.TMConfig
import Mathlib.Tactic.DeriveEncodable

/-!
# Chapter 7: Encodable instance for `Turing.ToPartrec.Code`

We use `Encodable` so programs can be decoded from bitstrings via `Encodable.decode`.
This instance is shared by both the toy Chapter 7 development and the core-generic `CoreToPartrec`
bridge, so it lives in a small standalone module.
-/

deriving instance Encodable for _root_.Turing.ToPartrec.Code

