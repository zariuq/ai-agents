Infix + 360 right := add.
Infix * 355 right := mul.
Infix ^ 350 right := pow.
Prefix ~ 100 := neg.

Definition expr1 : set := 1 + 2 * 3. (* 1 + (2 * 3) *)
Definition expr2 : set := (1 + 2) * 3.
Definition expr3 : set := ~ 1 + 2. (* (~ 1) + 2 *)
Definition expr4 : set := ~ (1 + 2).
Definition expr5 : set := 1 + 2 * 3 ^ 4. (* 1 + (2 * (3 ^ 4)) *)
