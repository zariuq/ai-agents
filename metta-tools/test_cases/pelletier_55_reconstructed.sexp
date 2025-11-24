;; TPTP S-Expression Export

;; Metadata
;; file: PUZ001+1 : TPTP v9.2.1. Released v2.0.0.
;; domain: Puzzles
;; problem: Dreadbury Mansion
;; english: Someone who lives in Dreadbury Mansion killed Aunt Agatha.

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
