;; TPTP S-Expression Export

;; Metadata
;; file: PUZ001+1 : TPTP v9.2.1. Released v2.0.0.
;; domain: Puzzles
;; problem: Dreadbury Mansion
;; version: Especial.
;; english: Someone who lives in Dreadbury Mansion killed Aunt Agatha.
;; refs: [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
;; source: [Hah94]
;; names: Pelletier 55 [Pel86]
;; status: Theorem
;; rating: 0.09 v9.1.0, 0.06 v9.0.0, 0.08 v8.1.0, 0.06 v7.4.0, 0.07 v7.2.0, 0.03 v7.1.0, 0.04 v7.0.0, 0.07 v6.4.0, 0.12 v6.3.0, 0.04 v6.2.0, 0.12 v6.1.0, 0.20 v6.0.0, 0.26 v5.5.0, 0.07 v5.3.0, 0.19 v5.2.0, 0.00 v5.0.0, 0.08 v4.1.0, 0.13 v4.0.0, 0.12 v3.7.0, 0.14 v3.5.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.11 v3.2.0, 0.22 v3.1.0, 0.17 v2.7.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
;; syntax: Number of formulae    :   14 (   6 unt;   0 def)
;; spc: FOF_THM_RFO_SEQ
;; comments: Modified by Geoff Sutcliffe.

;; Formulas

;; pel55_1 (axiom)
(fof
  pel55_1
  axiom
  (exists
    (X)
    (and
      (lives
        (var X)
      )
      (killed
        (var X)
        (const agatha)
      )
    )
  )
)

;; pel55_2_1 (axiom)
(fof
  pel55_2_1
  axiom
  (lives
    (const agatha)
  )
)

;; pel55_2_2 (axiom)
(fof
  pel55_2_2
  axiom
  (lives
    (const butler)
  )
)

;; pel55_2_3 (axiom)
(fof
  pel55_2_3
  axiom
  (lives
    (const charles)
  )
)

;; pel55_3 (axiom)
(fof
  pel55_3
  axiom
  (forall
    (X)
    (implies
      (lives
        (var X)
      )
      (or
        (=
          (var X)
          (const agatha)
        )
        (or
          (=
            (var X)
            (const butler)
          )
          (=
            (var X)
            (const charles)
          )
        )
      )
    )
  )
)

;; pel55_4 (axiom)
(fof
  pel55_4
  axiom
  (forall
    (X Y)
    (implies
      (killed
        (var X)
        (var Y)
      )
      (hates
        (var X)
        (var Y)
      )
    )
  )
)

;; pel55_5 (axiom)
(fof
  pel55_5
  axiom
  (forall
    (X Y)
    (implies
      (killed
        (var X)
        (var Y)
      )
      (not
        (richer
          (var X)
          (var Y)
        )
      )
    )
  )
)

;; pel55_6 (axiom)
(fof
  pel55_6
  axiom
  (forall
    (X)
    (implies
      (hates
        (const agatha)
        (var X)
      )
      (not
        (hates
          (const charles)
          (var X)
        )
      )
    )
  )
)

;; pel55_7 (axiom)
(fof
  pel55_7
  axiom
  (forall
    (X)
    (implies
      (not
        (=
          (var X)
          (const butler)
        )
      )
      (hates
        (const agatha)
        (var X)
      )
    )
  )
)

;; pel55_8 (axiom)
(fof
  pel55_8
  axiom
  (forall
    (X)
    (implies
      (not
        (richer
          (var X)
          (const agatha)
        )
      )
      (hates
        (const butler)
        (var X)
      )
    )
  )
)

;; pel55_9 (axiom)
(fof
  pel55_9
  axiom
  (forall
    (X)
    (implies
      (hates
        (const agatha)
        (var X)
      )
      (hates
        (const butler)
        (var X)
      )
    )
  )
)

;; pel55_10 (axiom)
(fof
  pel55_10
  axiom
  (forall
    (X)
    (exists
      (Y)
      (not
        (hates
          (var X)
          (var Y)
        )
      )
    )
  )
)

;; pel55_11 (axiom)
(fof
  pel55_11
  axiom
  (not
    (=
      (const agatha)
      (const butler)
    )
  )
)

;; pel55 (conjecture)
(fof
  pel55
  conjecture
  (killed
    (const agatha)
    (const agatha)
  )
)
