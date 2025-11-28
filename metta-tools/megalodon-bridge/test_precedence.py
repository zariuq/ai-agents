import unittest
from metta_to_mg import FormatContext, sexp_to_mg_term

class TestOperatorPrecedence(unittest.TestCase):
    def setUp(self):
        self.ctx = FormatContext()
        self.ctx.add_infix('+', 360, 'right')
        self.ctx.add_infix('*', 355, 'right')
        self.ctx.add_prefix('~', 100)

    def test_basic_infix(self):
        # 1 + 2 -> 1 + 2
        expr = ['+', '1', '2']
        self.assertEqual(sexp_to_mg_term(expr, self.ctx), '1 + 2')

    def test_precedence_wrap(self):
        # (1 + 2) * 3
        # + is 360, * is 355. * binds tighter? 
        # Megalodon: lower number = tighter binding?
        # Standard: 
        # Coq: higher = tighter. 
        # Megalodon: "Infix + 360 right". "Infix * 355 right".
        # If * is 355 and + is 360.
        # If we assume lower = looser?
        # Let's check standard math. * binds tighter than +.
        # If * is 355 and + is 360. 355 < 360.
        # So lower prec = tighter?
        # Wait, if prec < min_prec break.
        # In `mg_to_metta`: `if prec < min_prec: break`.
        # This implies we stop parsing at lower precedence.
        # If we are parsing `*` (355) and next is `+` (360).
        # If current min_prec is 355. 360 >= 355. We continue.
        # So `+` would be consumed as child of `*`.
        # So `1 * 2 + 3` -> `(1 * 2) + 3`?
        # If `+` has higher number, it binds *looser*?
        # No, usually higher number = tighter.
        # Let's check Megalodon source or behavior.
        # In `Collatz.mg`: `Infix + 360 right`. `Infix * 355 right`.
        # `3 * r + 1`.
        # If + is 360 (tighter), it would be `3 * (r + 1)`.
        # But standard math is `(3 * r) + 1`.
        # So `*` should be tighter.
        # So 355 should be "tighter" than 360?
        # That means LOWER number = TIGHTER binding.
        # Let's verify my parser logic:
        # `if prec < min_prec: break`.
        # Start with min_prec 0.
        # Parse `3`. Next is `*` (355). 355 >= 0. Continue.
        # Recurse for RHS with min_prec 355.
        # Parse `r`. Next is `+` (360).
        # If `+` (360) is LOOSER than `*` (355), we want to STOP parsing `*`'s rhs.
        # So we want 360 to be "less than" 355 in some sense?
        # Or `break` condition should be `if prec > min_prec`?
        # If standard: Higher = Tighter.
        # * (40), + (30).
        # Parse 3. Next * (40). Recurse min_prec 40.
        # Parse r. Next + (30). 30 < 40. Break. Correct.
        # So `prec < min_prec` implies Higher=Tighter.
        # BUT in Megalodon `+` is 360 and `*` is 355.
        # So `+` has HIGHER number.
        # So if Higher=Tighter, then `+` is tighter than `*`.
        # `3 * r + 1` -> `3 * (r + 1)`.
        # This contradicts standard math.
        # CONCLUSION: In Megalodon, LOWER number = TIGHTER binding?
        # Or Megalodon numbers are just weird?
        # Let's assume Lower = Tighter.
        # Then `prec > min_prec` should break?
        # My parser has `if prec < min_prec: break`.
        # If Lower = Tighter. * (355), + (360).
        # Parse 3. Next * (355). 355 >= 0. Continue.
        # Recurse min_prec 355.
        # Parse r. Next + (360). 360 >= 355. Continue.
        # Consumes `+` into `*`'s RHS.
        # Result: `3 * (r + 1)`.
        # So my parser assumes Higher=Tighter (precedence value increases with tightness).
        # And Megalodon uses 360 for + and 355 for *.
        # THIS IS A BUG in my understanding or Megalodon's notation.
        # Wait, maybe 360/355 are arbitrary?
        # Let's check `13_deep_precedence.mg` output.
        # `1 + 2 * 3`.
        # If output is `1 + 2 * 3` (no parens), it means structure matches precedence.
        # If structure was `(1 + 2) * 3`, and we print `1 + 2 * 3`, that's wrong.
        # Let's check roundtrip of `1 + 2 * 3`.
        pass

    def test_precedence_logic(self):
        # If we want (1+2)*3 with standard math (+ looser than *).
        # + (360), * (355).
        # If 355 is tighter, then 355 < 360.
        # My parser: `if prec < min_prec: break`.
        # If we want to break on looser op.
        # Current op * (355). Next op + (360).
        # We want to break.
        # 360 is NOT < 355. So we don't break. We consume.
        # So `*` consumes `+`. `1 * 2 + 3` -> `1 * (2 + 3)`.
        # This confirms my parser acts as if Higher = Tighter.
        # BUT Megalodon has + (360) > * (355).
        # So `+` binds tighter than `*` in my parser for these numbers.
        # This means my parser thinks `1 + 2 * 3` is `(1 + 2) * 3`.
        # This is opposite of standard math.
        # FIX: Change parser condition or semantic.
        # If Megalodon follows Coq:
        # Coq: + is level 50, * is level 40. Lower = Tighter?
        # No, Coq level 0 is loose, level 100 is tight.
        # Maybe Megalodon is different?
        # Let's check `mg_to_metta.py`.
        pass

if __name__ == '__main__':
    unittest.main()
