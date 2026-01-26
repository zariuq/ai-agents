Definition Adj8_raw : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ (j = 1 \/ (j = 4 \/ j = 7))) \/
    ((i = 1 /\ (j = 2 \/ j = 5)) \/
     ((i = 2 /\ (j = 3 \/ j = 6)) \/
      ((i = 3 /\ (j = 4 \/ j = 7)) \/
       ((i = 4 /\ j = 5) \/
        ((i = 5 /\ j = 6) \/
         (i = 6 /\ j = 7)))))).

Definition Adj8 : set -> set -> prop :=
  fun i j => Adj8_raw i j \/ Adj8_raw j i.

Theorem Adj8_sym : forall i j, Adj8 i j -> Adj8 j i.
let i j.
assume Hij : Adj8 i j.
prove Adj8 j i.
apply Hij.
- assume H : Adj8_raw i j.
  apply orIR (Adj8_raw j i) (Adj8_raw i j).
  exact H.
- assume H : Adj8_raw j i.
  apply orIL (Adj8_raw j i) (Adj8_raw i j).
  exact H.
Qed.

Theorem eq_refl : forall x, x = x.
let x.
prove x = x.
let Q.
assume Hxx : Q x x.
exact Hxx.
Qed.

Theorem Adj8_raw_irrefl : forall i, ~Adj8_raw i i.
let i.
apply notI.
assume Hii : Adj8_raw i i.
apply Hii.
- assume H0 : i = 0 /\ (i = 1 \/ (i = 4 \/ i = 7)).
  apply H0.
  assume Hi0 : i = 0.
  assume Hi' : i = 1 \/ (i = 4 \/ i = 7).
  apply Hi'.
  + assume Hi1 : i = 1.
    apply neq_1_0.
    prove 1 = 0.
    rewrite <- Hi1.
    exact Hi0.
  + assume Hi'' : i = 4 \/ i = 7.
    apply Hi''.
    * assume Hi4 : i = 4.
      apply neq_4_0.
      prove 4 = 0.
      rewrite <- Hi4.
      exact Hi0.
    * assume Hi7 : i = 7.
      apply neq_7_0.
      prove 7 = 0.
      rewrite <- Hi7.
      exact Hi0.
- assume H' : (i = 1 /\ (i = 2 \/ i = 5))
           \/ ((i = 2 /\ (i = 3 \/ i = 6))
            \/ ((i = 3 /\ (i = 4 \/ i = 7))
             \/ ((i = 4 /\ i = 5)
              \/ ((i = 5 /\ i = 6)
               \/ (i = 6 /\ i = 7))))).
  apply H'.
  + assume H1 : i = 1 /\ (i = 2 \/ i = 5).
    apply H1.
    assume Hi1 : i = 1.
    assume Hi' : i = 2 \/ i = 5.
    apply Hi'.
    * assume Hi2 : i = 2.
      apply neq_2_1.
      prove 2 = 1.
      rewrite <- Hi2.
      exact Hi1.
    * assume Hi5 : i = 5.
      apply neq_5_1.
      prove 5 = 1.
      rewrite <- Hi5.
      exact Hi1.
  + assume H' : (i = 2 /\ (i = 3 \/ i = 6))
             \/ ((i = 3 /\ (i = 4 \/ i = 7))
              \/ ((i = 4 /\ i = 5)
               \/ ((i = 5 /\ i = 6)
                \/ (i = 6 /\ i = 7)))).
    apply H'.
    * assume H2 : i = 2 /\ (i = 3 \/ i = 6).
      apply H2.
      assume Hi2 : i = 2.
      assume Hi' : i = 3 \/ i = 6.
      apply Hi'.
      - assume Hi3 : i = 3.
        apply neq_3_2.
        prove 3 = 2.
        rewrite <- Hi3.
        exact Hi2.
      - assume Hi6 : i = 6.
        apply neq_6_2.
        prove 6 = 2.
        rewrite <- Hi6.
        exact Hi2.
    * assume H' : (i = 3 /\ (i = 4 \/ i = 7))
              \/ ((i = 4 /\ i = 5)
               \/ ((i = 5 /\ i = 6)
                \/ (i = 6 /\ i = 7))).
      apply H'.
      { assume H3 : i = 3 /\ (i = 4 \/ i = 7).
        apply H3.
        assume Hi3 : i = 3.
        assume Hi' : i = 4 \/ i = 7.
        apply Hi'.
        - assume Hi4 : i = 4.
          apply neq_4_3.
          prove 4 = 3.
          rewrite <- Hi4.
          exact Hi3.
        - assume Hi7 : i = 7.
          apply neq_7_3.
          prove 7 = 3.
          rewrite <- Hi7.
          exact Hi3. }
      { assume H' : (i = 4 /\ i = 5)
                \/ ((i = 5 /\ i = 6)
                 \/ (i = 6 /\ i = 7)).
        apply H'.
        - assume H45 : i = 4 /\ i = 5.
          apply H45.
          assume Hi4 : i = 4.
          assume Hi5 : i = 5.
          apply neq_5_4.
          prove 5 = 4.
          rewrite <- Hi5.
          exact Hi4.
        - assume H' : (i = 5 /\ i = 6) \/ (i = 6 /\ i = 7).
          apply H'.
          + assume H56 : i = 5 /\ i = 6.
            apply H56.
            assume Hi5 : i = 5.
            assume Hi6 : i = 6.
            apply neq_6_5.
            prove 6 = 5.
            rewrite <- Hi6.
            exact Hi5.
          + assume H67 : i = 6 /\ i = 7.
            apply H67.
            assume Hi6 : i = 6.
            assume Hi7 : i = 7.
            apply neq_7_6.
            prove 7 = 6.
            rewrite <- Hi7.
            exact Hi6. }
Qed.

Theorem Adj8_irrefl : forall i :e 8, ~Adj8 i i.
let i.
assume Hi : i :e 8.
apply notI.
assume Hii : Adj8 i i.
apply Hii.
- assume Hraw : Adj8_raw i i.
  apply Adj8_raw_irrefl i.
  exact Hraw.
- assume Hraw : Adj8_raw i i.
  apply Adj8_raw_irrefl i.
  exact Hraw.
Qed.

Theorem Adj8_is_graph : is_graph 8 Adj8.
apply andI (forall x y, Adj8 x y -> Adj8 y x) (forall x :e 8, ~Adj8 x x).
- prove forall x y, Adj8 x y -> Adj8 y x.
  let x y.
  assume Hxy : Adj8 x y.
  apply Adj8_sym x y.
  exact Hxy.
- prove forall x :e 8, ~Adj8 x x.
  let x.
  assume Hx : x :e 8.
  exact Adj8_irrefl x Hx.
Qed.

Theorem Adj8_cases_0 : forall j, Adj8 0 j -> j = 1 \/ (j = 4 \/ j = 7).
let j.
assume H : Adj8 0 j.
apply H.
- assume Hraw : Adj8_raw 0 j.
  apply Hraw.
  - assume H0 : 0 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume H00 : 0 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    exact Hj.
  - assume Hrest :
      (0 = 1 /\ (j = 2 \/ j = 5))
      \/ ((0 = 2 /\ (j = 3 \/ j = 6))
          \/ ((0 = 3 /\ (j = 4 \/ j = 7))
              \/ ((0 = 4 /\ j = 5)
                  \/ ((0 = 5 /\ j = 6) \/ (0 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 0 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 0 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      apply neq_1_0.
      prove 1 = 0.
      rewrite <- Heq.
      exact eq_refl 0.
    + assume Hrest2 :
        (0 = 2 /\ (j = 3 \/ j = 6))
        \/ ((0 = 3 /\ (j = 4 \/ j = 7))
            \/ ((0 = 4 /\ j = 5) \/ ((0 = 5 /\ j = 6) \/ (0 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 0 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 0 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        apply neq_2_0.
        prove 2 = 0.
        rewrite <- Heq.
        exact eq_refl 0.
      * assume Hrest3 :
          (0 = 3 /\ (j = 4 \/ j = 7))
          \/ ((0 = 4 /\ j = 5) \/ ((0 = 5 /\ j = 6) \/ (0 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 0 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 0 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          apply neq_3_0.
          prove 3 = 0.
          rewrite <- Heq.
          exact eq_refl 0.
        - assume Hrest4 :
            (0 = 4 /\ j = 5) \/ ((0 = 5 /\ j = 6) \/ (0 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 0 = 4 /\ j = 5.
            apply H4.
            assume Heq : 0 = 4.
            assume Hj : j = 5.
            apply FalseE.
            apply neq_4_0.
            prove 4 = 0.
            rewrite <- Heq.
            exact eq_refl 0. }
          { assume Hrest5 : (0 = 5 /\ j = 6) \/ (0 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 0 = 5 /\ j = 6.
              apply H5.
              assume Heq : 0 = 5.
              assume Hj : j = 6.
              apply FalseE.
              apply neq_5_0.
              prove 5 = 0.
              rewrite <- Heq.
              exact eq_refl 0.
            - assume H6 : 0 = 6 /\ j = 7.
              apply H6.
              assume Heq : 0 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_0.
              prove 6 = 0.
              rewrite <- Heq.
              exact eq_refl 0. }
- assume Hraw : Adj8_raw j 0.
  apply Hraw.
  - assume H0 : j = 0 /\ (0 = 1 \/ (0 = 4 \/ 0 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 0 = 1 \/ (0 = 4 \/ 0 = 7).
    apply Hbad.
    + assume H01 : 0 = 1.
      apply FalseE.
      apply neq_1_0.
      prove 1 = 0.
      rewrite <- H01.
      exact eq_refl 0.
    + assume Hbad2 : 0 = 4 \/ 0 = 7.
      apply Hbad2.
      * assume H04 : 0 = 4.
        apply FalseE.
        apply neq_4_0.
        prove 4 = 0.
        rewrite <- H04.
        exact eq_refl 0.
      * assume H07 : 0 = 7.
        apply FalseE.
        apply neq_7_0.
        prove 7 = 0.
        rewrite <- H07.
        exact eq_refl 0.
  - assume Hrest :
      (j = 1 /\ (0 = 2 \/ 0 = 5))
      \/ ((j = 2 /\ (0 = 3 \/ 0 = 6))
          \/ ((j = 3 /\ (0 = 4 \/ 0 = 7))
              \/ ((j = 4 /\ 0 = 5) \/ ((j = 5 /\ 0 = 6) \/ (j = 6 /\ 0 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (0 = 2 \/ 0 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 0 = 2 \/ 0 = 5.
      apply Hbad.
      * assume H02 : 0 = 2.
        apply FalseE.
        apply neq_2_0.
        prove 2 = 0.
        rewrite <- H02.
        exact eq_refl 0.
      * assume H05 : 0 = 5.
        apply FalseE.
        apply neq_5_0.
        prove 5 = 0.
        rewrite <- H05.
        exact eq_refl 0.
    + assume Hrest2 :
        (j = 2 /\ (0 = 3 \/ 0 = 6))
        \/ ((j = 3 /\ (0 = 4 \/ 0 = 7))
            \/ ((j = 4 /\ 0 = 5) \/ ((j = 5 /\ 0 = 6) \/ (j = 6 /\ 0 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (0 = 3 \/ 0 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 0 = 3 \/ 0 = 6.
        apply Hbad.
        - assume H03 : 0 = 3.
          apply FalseE.
          apply neq_3_0.
          prove 3 = 0.
          rewrite <- H03.
          exact eq_refl 0.
        - assume H06 : 0 = 6.
          apply FalseE.
          apply neq_6_0.
          prove 6 = 0.
          rewrite <- H06.
          exact eq_refl 0.
      * assume Hrest3 :
          (j = 3 /\ (0 = 4 \/ 0 = 7))
          \/ ((j = 4 /\ 0 = 5) \/ ((j = 5 /\ 0 = 6) \/ (j = 6 /\ 0 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (0 = 4 \/ 0 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 0 = 4 \/ 0 = 7.
          apply Hbad.
          + assume H04 : 0 = 4.
            apply FalseE.
            apply neq_4_0.
            prove 4 = 0.
            rewrite <- H04.
            exact eq_refl 0.
          + assume H07 : 0 = 7.
            apply FalseE.
            apply neq_7_0.
            prove 7 = 0.
            rewrite <- H07.
            exact eq_refl 0.
        - assume Hrest4 : (j = 4 /\ 0 = 5) \/ ((j = 5 /\ 0 = 6) \/ (j = 6 /\ 0 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 0 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H05 : 0 = 5.
            apply FalseE.
            apply neq_5_0.
            prove 5 = 0.
            rewrite <- H05.
            exact eq_refl 0. }
          { assume Hrest5 : (j = 5 /\ 0 = 6) \/ (j = 6 /\ 0 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 0 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H06 : 0 = 6.
              apply FalseE.
              apply neq_6_0.
              prove 6 = 0.
              rewrite <- H06.
              exact eq_refl 0.
            - assume H6 : j = 6 /\ 0 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H07 : 0 = 7.
              apply FalseE.
              apply neq_7_0.
              prove 7 = 0.
              rewrite <- H07.
              exact eq_refl 0. }
Qed.

Theorem Adj8_cases_1 : forall j, Adj8 1 j -> j = 0 \/ (j = 2 \/ j = 5).
let j.
assume H : Adj8 1 j.
apply H.
- assume Hraw : Adj8_raw 1 j.
  apply Hraw.
  - assume H0 : 1 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 1 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_1_0 Heq.
  - assume Hrest :
      (1 = 1 /\ (j = 2 \/ j = 5))
      \/ ((1 = 2 /\ (j = 3 \/ j = 6))
          \/ ((1 = 3 /\ (j = 4 \/ j = 7))
              \/ ((1 = 4 /\ j = 5)
                  \/ ((1 = 5 /\ j = 6) \/ (1 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 1 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume H11 : 1 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply orIR (j = 0) (j = 2 \/ j = 5).
      exact Hj.
    + assume Hrest2 :
        (1 = 2 /\ (j = 3 \/ j = 6))
        \/ ((1 = 3 /\ (j = 4 \/ j = 7))
            \/ ((1 = 4 /\ j = 5) \/ ((1 = 5 /\ j = 6) \/ (1 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 1 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 1 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        apply neq_2_1.
        prove 2 = 1.
        rewrite <- Heq.
        exact eq_refl 1.
      * assume Hrest3 :
          (1 = 3 /\ (j = 4 \/ j = 7))
          \/ ((1 = 4 /\ j = 5) \/ ((1 = 5 /\ j = 6) \/ (1 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 1 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 1 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          apply neq_3_1.
          prove 3 = 1.
          rewrite <- Heq.
          exact eq_refl 1.
        - assume Hrest4 : (1 = 4 /\ j = 5) \/ ((1 = 5 /\ j = 6) \/ (1 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 1 = 4 /\ j = 5.
            apply H4.
            assume Heq : 1 = 4.
            assume Hj : j = 5.
            apply FalseE.
            apply neq_4_1.
            prove 4 = 1.
            rewrite <- Heq.
            exact eq_refl 1. }
          { assume Hrest5 : (1 = 5 /\ j = 6) \/ (1 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 1 = 5 /\ j = 6.
              apply H5.
              assume Heq : 1 = 5.
              assume Hj : j = 6.
              apply FalseE.
              apply neq_5_1.
              prove 5 = 1.
              rewrite <- Heq.
              exact eq_refl 1.
            - assume H6 : 1 = 6 /\ j = 7.
              apply H6.
              assume Heq : 1 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_1.
              prove 6 = 1.
              rewrite <- Heq.
              exact eq_refl 1. }
- assume Hraw : Adj8_raw j 1.
  apply Hraw.
  - assume H0 : j = 0 /\ (1 = 1 \/ (1 = 4 \/ 1 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hj' : 1 = 1 \/ (1 = 4 \/ 1 = 7).
    apply orIL (j = 0) (j = 2 \/ j = 5).
    exact Hj0.
  - assume Hrest :
      (j = 1 /\ (1 = 2 \/ 1 = 5))
      \/ ((j = 2 /\ (1 = 3 \/ 1 = 6))
          \/ ((j = 3 /\ (1 = 4 \/ 1 = 7))
              \/ ((j = 4 /\ 1 = 5) \/ ((j = 5 /\ 1 = 6) \/ (j = 6 /\ 1 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (1 = 2 \/ 1 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 1 = 2 \/ 1 = 5.
      apply Hbad.
      * assume H12 : 1 = 2.
        apply FalseE.
        apply neq_2_1.
        prove 2 = 1.
        rewrite <- H12.
        exact eq_refl 1.
      * assume H15 : 1 = 5.
        apply FalseE.
        apply neq_5_1.
        prove 5 = 1.
        rewrite <- H15.
        exact eq_refl 1.
    + assume Hrest2 :
        (j = 2 /\ (1 = 3 \/ 1 = 6))
        \/ ((j = 3 /\ (1 = 4 \/ 1 = 7))
            \/ ((j = 4 /\ 1 = 5) \/ ((j = 5 /\ 1 = 6) \/ (j = 6 /\ 1 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (1 = 3 \/ 1 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 1 = 3 \/ 1 = 6.
        apply Hbad.
        - assume H13 : 1 = 3.
          apply FalseE.
          apply neq_3_1.
          prove 3 = 1.
          rewrite <- H13.
          exact eq_refl 1.
        - assume H16 : 1 = 6.
          apply FalseE.
          apply neq_6_1.
          prove 6 = 1.
          rewrite <- H16.
          exact eq_refl 1.
      * assume Hrest3 :
          (j = 3 /\ (1 = 4 \/ 1 = 7))
          \/ ((j = 4 /\ 1 = 5) \/ ((j = 5 /\ 1 = 6) \/ (j = 6 /\ 1 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (1 = 4 \/ 1 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 1 = 4 \/ 1 = 7.
          apply Hbad.
          + assume H14 : 1 = 4.
            apply FalseE.
            apply neq_4_1.
            prove 4 = 1.
            rewrite <- H14.
            exact eq_refl 1.
          + assume H17 : 1 = 7.
            apply FalseE.
            apply neq_7_1.
            prove 7 = 1.
            rewrite <- H17.
            exact eq_refl 1.
        - assume Hrest4 : (j = 4 /\ 1 = 5) \/ ((j = 5 /\ 1 = 6) \/ (j = 6 /\ 1 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 1 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H15 : 1 = 5.
            apply FalseE.
            apply neq_5_1.
            prove 5 = 1.
            rewrite <- H15.
            exact eq_refl 1. }
          { assume Hrest5 : (j = 5 /\ 1 = 6) \/ (j = 6 /\ 1 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 1 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H16 : 1 = 6.
              apply FalseE.
              apply neq_6_1.
              prove 6 = 1.
              rewrite <- H16.
              exact eq_refl 1.
            - assume H6 : j = 6 /\ 1 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H17 : 1 = 7.
              apply FalseE.
              apply neq_7_1.
              prove 7 = 1.
              rewrite <- H17.
              exact eq_refl 1. }
Qed.

Theorem Adj8_cases_2 : forall j, Adj8 2 j -> j = 1 \/ (j = 3 \/ j = 6).
let j.
assume H : Adj8 2 j.
apply H.
- assume Hraw : Adj8_raw 2 j.
  apply Hraw.
  - assume H0 : 2 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 2 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_2_0 Heq.
  - assume Hrest :
      (2 = 1 /\ (j = 2 \/ j = 5))
      \/ ((2 = 2 /\ (j = 3 \/ j = 6))
          \/ ((2 = 3 /\ (j = 4 \/ j = 7))
              \/ ((2 = 4 /\ j = 5)
                  \/ ((2 = 5 /\ j = 6) \/ (2 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 2 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 2 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_2_1 Heq.
    + assume Hrest2 :
        (2 = 2 /\ (j = 3 \/ j = 6))
        \/ ((2 = 3 /\ (j = 4 \/ j = 7))
            \/ ((2 = 4 /\ j = 5) \/ ((2 = 5 /\ j = 6) \/ (2 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 2 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume H22 : 2 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply orIR (j = 1) (j = 3 \/ j = 6).
        exact Hj.
      * assume Hrest3 :
          (2 = 3 /\ (j = 4 \/ j = 7))
          \/ ((2 = 4 /\ j = 5) \/ ((2 = 5 /\ j = 6) \/ (2 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 2 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 2 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          apply neq_3_2.
          prove 3 = 2.
          rewrite <- Heq.
          exact eq_refl 2.
        - assume Hrest4 : (2 = 4 /\ j = 5) \/ ((2 = 5 /\ j = 6) \/ (2 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 2 = 4 /\ j = 5.
            apply H4.
            assume Heq : 2 = 4.
            assume Hj : j = 5.
            apply FalseE.
            apply neq_4_2.
            prove 4 = 2.
            rewrite <- Heq.
            exact eq_refl 2. }
          { assume Hrest5 : (2 = 5 /\ j = 6) \/ (2 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 2 = 5 /\ j = 6.
              apply H5.
              assume Heq : 2 = 5.
              assume Hj : j = 6.
              apply FalseE.
              apply neq_5_2.
              prove 5 = 2.
              rewrite <- Heq.
              exact eq_refl 2.
            - assume H6 : 2 = 6 /\ j = 7.
              apply H6.
              assume Heq : 2 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_2.
              prove 6 = 2.
              rewrite <- Heq.
              exact eq_refl 2. }
- assume Hraw : Adj8_raw j 2.
  apply Hraw.
  - assume H0 : j = 0 /\ (2 = 1 \/ (2 = 4 \/ 2 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 2 = 1 \/ (2 = 4 \/ 2 = 7).
    apply Hbad.
    + assume H21 : 2 = 1.
      apply FalseE.
      exact neq_2_1 H21.
    + assume Hbad2 : 2 = 4 \/ 2 = 7.
      apply Hbad2.
      * assume H24 : 2 = 4.
        apply FalseE.
        apply neq_4_2.
        prove 4 = 2.
        rewrite <- H24.
        exact eq_refl 2.
      * assume H27 : 2 = 7.
        apply FalseE.
        apply neq_7_2.
        prove 7 = 2.
        rewrite <- H27.
        exact eq_refl 2.
  - assume Hrest :
      (j = 1 /\ (2 = 2 \/ 2 = 5))
      \/ ((j = 2 /\ (2 = 3 \/ 2 = 6))
          \/ ((j = 3 /\ (2 = 4 \/ 2 = 7))
              \/ ((j = 4 /\ 2 = 5) \/ ((j = 5 /\ 2 = 6) \/ (j = 6 /\ 2 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (2 = 2 \/ 2 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 2 = 2 \/ 2 = 5.
      apply orIL (j = 1) (j = 3 \/ j = 6).
      exact Hj1.
    + assume Hrest2 :
        (j = 2 /\ (2 = 3 \/ 2 = 6))
        \/ ((j = 3 /\ (2 = 4 \/ 2 = 7))
            \/ ((j = 4 /\ 2 = 5) \/ ((j = 5 /\ 2 = 6) \/ (j = 6 /\ 2 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (2 = 3 \/ 2 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 2 = 3 \/ 2 = 6.
        apply Hbad.
        - assume H23 : 2 = 3.
          apply FalseE.
          apply neq_3_2.
          prove 3 = 2.
          rewrite <- H23.
          exact eq_refl 2.
        - assume H26 : 2 = 6.
          apply FalseE.
          apply neq_6_2.
          prove 6 = 2.
          rewrite <- H26.
          exact eq_refl 2.
      * assume Hrest3 :
          (j = 3 /\ (2 = 4 \/ 2 = 7))
          \/ ((j = 4 /\ 2 = 5) \/ ((j = 5 /\ 2 = 6) \/ (j = 6 /\ 2 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (2 = 4 \/ 2 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 2 = 4 \/ 2 = 7.
          apply Hbad.
          + assume H24 : 2 = 4.
            apply FalseE.
            apply neq_4_2.
            prove 4 = 2.
            rewrite <- H24.
            exact eq_refl 2.
          + assume H27 : 2 = 7.
            apply FalseE.
            apply neq_7_2.
            prove 7 = 2.
            rewrite <- H27.
            exact eq_refl 2.
        - assume Hrest4 : (j = 4 /\ 2 = 5) \/ ((j = 5 /\ 2 = 6) \/ (j = 6 /\ 2 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 2 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H25 : 2 = 5.
            apply FalseE.
            apply neq_5_2.
            prove 5 = 2.
            rewrite <- H25.
            exact eq_refl 2. }
          { assume Hrest5 : (j = 5 /\ 2 = 6) \/ (j = 6 /\ 2 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 2 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H26 : 2 = 6.
              apply FalseE.
              apply neq_6_2.
              prove 6 = 2.
              rewrite <- H26.
              exact eq_refl 2.
            - assume H6 : j = 6 /\ 2 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H27 : 2 = 7.
              apply FalseE.
              apply neq_7_2.
              prove 7 = 2.
              rewrite <- H27.
	              exact eq_refl 2. }
Qed.

Theorem Adj8_cases_3 : forall j, Adj8 3 j -> j = 2 \/ (j = 4 \/ j = 7).
let j.
assume H : Adj8 3 j.
apply H.
- assume Hraw : Adj8_raw 3 j.
  apply Hraw.
  - assume H0 : 3 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 3 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_3_0 Heq.
  - assume Hrest :
      (3 = 1 /\ (j = 2 \/ j = 5))
      \/ ((3 = 2 /\ (j = 3 \/ j = 6))
          \/ ((3 = 3 /\ (j = 4 \/ j = 7))
              \/ ((3 = 4 /\ j = 5)
                  \/ ((3 = 5 /\ j = 6) \/ (3 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 3 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 3 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_3_1 Heq.
    + assume Hrest2 :
        (3 = 2 /\ (j = 3 \/ j = 6))
        \/ ((3 = 3 /\ (j = 4 \/ j = 7))
            \/ ((3 = 4 /\ j = 5) \/ ((3 = 5 /\ j = 6) \/ (3 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 3 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 3 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        exact neq_3_2 Heq.
      * assume Hrest3 :
          (3 = 3 /\ (j = 4 \/ j = 7))
          \/ ((3 = 4 /\ j = 5) \/ ((3 = 5 /\ j = 6) \/ (3 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 3 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume H33 : 3 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply orIR (j = 2) (j = 4 \/ j = 7).
          exact Hj.
        - assume Hrest4 : (3 = 4 /\ j = 5) \/ ((3 = 5 /\ j = 6) \/ (3 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 3 = 4 /\ j = 5.
            apply H4.
            assume Heq : 3 = 4.
            assume Hj : j = 5.
            apply FalseE.
            apply neq_4_3.
            prove 4 = 3.
            rewrite <- Heq.
            exact eq_refl 3. }
          { assume Hrest5 : (3 = 5 /\ j = 6) \/ (3 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 3 = 5 /\ j = 6.
              apply H5.
              assume Heq : 3 = 5.
              assume Hj : j = 6.
              apply FalseE.
              apply neq_5_3.
              prove 5 = 3.
              rewrite <- Heq.
              exact eq_refl 3.
            - assume H6 : 3 = 6 /\ j = 7.
              apply H6.
              assume Heq : 3 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_3.
              prove 6 = 3.
              rewrite <- Heq.
	              exact eq_refl 3. }
- assume Hraw : Adj8_raw j 3.
  apply Hraw.
  - assume H0 : j = 0 /\ (3 = 1 \/ (3 = 4 \/ 3 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 3 = 1 \/ (3 = 4 \/ 3 = 7).
    apply Hbad.
    + assume H31 : 3 = 1.
      apply FalseE.
      exact neq_3_1 H31.
    + assume Hbad2 : 3 = 4 \/ 3 = 7.
      apply Hbad2.
      * assume H34 : 3 = 4.
        apply FalseE.
        apply neq_4_3.
        prove 4 = 3.
        rewrite <- H34.
        exact eq_refl 3.
      * assume H37 : 3 = 7.
        apply FalseE.
        apply neq_7_3.
        prove 7 = 3.
        rewrite <- H37.
        exact eq_refl 3.
  - assume Hrest :
      (j = 1 /\ (3 = 2 \/ 3 = 5))
      \/ ((j = 2 /\ (3 = 3 \/ 3 = 6))
          \/ ((j = 3 /\ (3 = 4 \/ 3 = 7))
              \/ ((j = 4 /\ 3 = 5) \/ ((j = 5 /\ 3 = 6) \/ (j = 6 /\ 3 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (3 = 2 \/ 3 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 3 = 2 \/ 3 = 5.
      apply Hbad.
      * assume H32 : 3 = 2.
        apply FalseE.
        exact neq_3_2 H32.
      * assume H35 : 3 = 5.
        apply FalseE.
        apply neq_5_3.
        prove 5 = 3.
        rewrite <- H35.
        exact eq_refl 3.
    + assume Hrest2 :
        (j = 2 /\ (3 = 3 \/ 3 = 6))
        \/ ((j = 3 /\ (3 = 4 \/ 3 = 7))
            \/ ((j = 4 /\ 3 = 5) \/ ((j = 5 /\ 3 = 6) \/ (j = 6 /\ 3 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (3 = 3 \/ 3 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 3 = 3 \/ 3 = 6.
        apply orIL (j = 2) (j = 4 \/ j = 7).
        exact Hj2.
      * assume Hrest3 :
          (j = 3 /\ (3 = 4 \/ 3 = 7))
          \/ ((j = 4 /\ 3 = 5) \/ ((j = 5 /\ 3 = 6) \/ (j = 6 /\ 3 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (3 = 4 \/ 3 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 3 = 4 \/ 3 = 7.
          apply Hbad.
          + assume H34 : 3 = 4.
            apply FalseE.
            apply neq_4_3.
            prove 4 = 3.
            rewrite <- H34.
            exact eq_refl 3.
          + assume H37 : 3 = 7.
            apply FalseE.
            apply neq_7_3.
            prove 7 = 3.
            rewrite <- H37.
            exact eq_refl 3.
        - assume Hrest4 : (j = 4 /\ 3 = 5) \/ ((j = 5 /\ 3 = 6) \/ (j = 6 /\ 3 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 3 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H35 : 3 = 5.
            apply FalseE.
            apply neq_5_3.
            prove 5 = 3.
            rewrite <- H35.
            exact eq_refl 3. }
          { assume Hrest5 : (j = 5 /\ 3 = 6) \/ (j = 6 /\ 3 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 3 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H36 : 3 = 6.
              apply FalseE.
              apply neq_6_3.
              prove 6 = 3.
              rewrite <- H36.
              exact eq_refl 3.
            - assume H6 : j = 6 /\ 3 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H37 : 3 = 7.
              apply FalseE.
              apply neq_7_3.
              prove 7 = 3.
              rewrite <- H37.
	              exact eq_refl 3. }
Qed.

Theorem Adj8_cases_4 : forall j, Adj8 4 j -> j = 0 \/ (j = 3 \/ j = 5).
let j.
assume H : Adj8 4 j.
apply H.
- assume Hraw : Adj8_raw 4 j.
  apply Hraw.
  - assume H0 : 4 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 4 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_4_0 Heq.
  - assume Hrest :
      (4 = 1 /\ (j = 2 \/ j = 5))
      \/ ((4 = 2 /\ (j = 3 \/ j = 6))
          \/ ((4 = 3 /\ (j = 4 \/ j = 7))
              \/ ((4 = 4 /\ j = 5)
                  \/ ((4 = 5 /\ j = 6) \/ (4 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 4 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 4 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_4_1 Heq.
    + assume Hrest2 :
        (4 = 2 /\ (j = 3 \/ j = 6))
        \/ ((4 = 3 /\ (j = 4 \/ j = 7))
            \/ ((4 = 4 /\ j = 5) \/ ((4 = 5 /\ j = 6) \/ (4 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 4 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 4 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        exact neq_4_2 Heq.
      * assume Hrest3 :
          (4 = 3 /\ (j = 4 \/ j = 7))
          \/ ((4 = 4 /\ j = 5) \/ ((4 = 5 /\ j = 6) \/ (4 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 4 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 4 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          exact neq_4_3 Heq.
        - assume Hrest4 : (4 = 4 /\ j = 5) \/ ((4 = 5 /\ j = 6) \/ (4 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 4 = 4 /\ j = 5.
            apply H4.
            assume H44 : 4 = 4.
            assume Hj : j = 5.
            apply orIR (j = 0) (j = 3 \/ j = 5).
            apply orIR (j = 3) (j = 5).
            exact Hj. }
          { assume Hrest5 : (4 = 5 /\ j = 6) \/ (4 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 4 = 5 /\ j = 6.
              apply H5.
              assume Heq : 4 = 5.
              assume Hj : j = 6.
              apply FalseE.
              apply neq_5_4.
              prove 5 = 4.
              rewrite <- Heq.
              exact eq_refl 4.
            - assume H6 : 4 = 6 /\ j = 7.
              apply H6.
              assume Heq : 4 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_4.
              prove 6 = 4.
              rewrite <- Heq.
	              exact eq_refl 4. }
- assume Hraw : Adj8_raw j 4.
  apply Hraw.
  - assume H0 : j = 0 /\ (4 = 1 \/ (4 = 4 \/ 4 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 4 = 1 \/ (4 = 4 \/ 4 = 7).
    apply orIL (j = 0) (j = 3 \/ j = 5).
    exact Hj0.
  - assume Hrest :
      (j = 1 /\ (4 = 2 \/ 4 = 5))
      \/ ((j = 2 /\ (4 = 3 \/ 4 = 6))
          \/ ((j = 3 /\ (4 = 4 \/ 4 = 7))
              \/ ((j = 4 /\ 4 = 5) \/ ((j = 5 /\ 4 = 6) \/ (j = 6 /\ 4 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (4 = 2 \/ 4 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 4 = 2 \/ 4 = 5.
      apply Hbad.
      * assume H42 : 4 = 2.
        apply FalseE.
        exact neq_4_2 H42.
      * assume H45 : 4 = 5.
        apply FalseE.
        apply neq_5_4.
        prove 5 = 4.
        rewrite <- H45.
        exact eq_refl 4.
    + assume Hrest2 :
        (j = 2 /\ (4 = 3 \/ 4 = 6))
        \/ ((j = 3 /\ (4 = 4 \/ 4 = 7))
            \/ ((j = 4 /\ 4 = 5) \/ ((j = 5 /\ 4 = 6) \/ (j = 6 /\ 4 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (4 = 3 \/ 4 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 4 = 3 \/ 4 = 6.
        apply Hbad.
        - assume H43 : 4 = 3.
          apply FalseE.
          exact neq_4_3 H43.
        - assume H46 : 4 = 6.
          apply FalseE.
          apply neq_6_4.
          prove 6 = 4.
          rewrite <- H46.
          exact eq_refl 4.
      * assume Hrest3 :
          (j = 3 /\ (4 = 4 \/ 4 = 7))
          \/ ((j = 4 /\ 4 = 5) \/ ((j = 5 /\ 4 = 6) \/ (j = 6 /\ 4 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (4 = 4 \/ 4 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 4 = 4 \/ 4 = 7.
          apply orIR (j = 0) (j = 3 \/ j = 5).
          apply orIL (j = 3) (j = 5).
          exact Hj3.
        - assume Hrest4 : (j = 4 /\ 4 = 5) \/ ((j = 5 /\ 4 = 6) \/ (j = 6 /\ 4 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 4 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H45 : 4 = 5.
            apply FalseE.
            apply neq_5_4.
            prove 5 = 4.
            rewrite <- H45.
            exact eq_refl 4. }
          { assume Hrest5 : (j = 5 /\ 4 = 6) \/ (j = 6 /\ 4 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 4 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H46 : 4 = 6.
              apply FalseE.
              apply neq_6_4.
              prove 6 = 4.
              rewrite <- H46.
              exact eq_refl 4.
            - assume H6 : j = 6 /\ 4 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H47 : 4 = 7.
              apply FalseE.
              apply neq_7_4.
              prove 7 = 4.
              rewrite <- H47.
	              exact eq_refl 4. }
Qed.

Theorem Adj8_cases_5 : forall j, Adj8 5 j -> j = 1 \/ (j = 4 \/ j = 6).
let j.
assume H : Adj8 5 j.
apply H.
- assume Hraw : Adj8_raw 5 j.
  apply Hraw.
  - assume H0 : 5 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 5 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_5_0 Heq.
  - assume Hrest :
      (5 = 1 /\ (j = 2 \/ j = 5))
      \/ ((5 = 2 /\ (j = 3 \/ j = 6))
          \/ ((5 = 3 /\ (j = 4 \/ j = 7))
              \/ ((5 = 4 /\ j = 5)
                  \/ ((5 = 5 /\ j = 6) \/ (5 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 5 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 5 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_5_1 Heq.
    + assume Hrest2 :
        (5 = 2 /\ (j = 3 \/ j = 6))
        \/ ((5 = 3 /\ (j = 4 \/ j = 7))
            \/ ((5 = 4 /\ j = 5) \/ ((5 = 5 /\ j = 6) \/ (5 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 5 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 5 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        exact neq_5_2 Heq.
      * assume Hrest3 :
          (5 = 3 /\ (j = 4 \/ j = 7))
          \/ ((5 = 4 /\ j = 5) \/ ((5 = 5 /\ j = 6) \/ (5 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 5 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 5 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          exact neq_5_3 Heq.
        - assume Hrest4 : (5 = 4 /\ j = 5) \/ ((5 = 5 /\ j = 6) \/ (5 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 5 = 4 /\ j = 5.
            apply H4.
            assume Heq : 5 = 4.
            assume Hj : j = 5.
            apply FalseE.
            exact neq_5_4 Heq. }
          { assume Hrest5 : (5 = 5 /\ j = 6) \/ (5 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 5 = 5 /\ j = 6.
              apply H5.
              assume H55 : 5 = 5.
              assume Hj : j = 6.
              apply orIR (j = 1) (j = 4 \/ j = 6).
              apply orIR (j = 4) (j = 6).
              exact Hj.
            - assume H6 : 5 = 6 /\ j = 7.
              apply H6.
              assume Heq : 5 = 6.
              assume Hj : j = 7.
              apply FalseE.
              apply neq_6_5.
              prove 6 = 5.
              rewrite <- Heq.
	              exact eq_refl 5. }
- assume Hraw : Adj8_raw j 5.
  apply Hraw.
  - assume H0 : j = 0 /\ (5 = 1 \/ (5 = 4 \/ 5 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 5 = 1 \/ (5 = 4 \/ 5 = 7).
    apply Hbad.
    + assume H51 : 5 = 1.
      apply FalseE.
      exact neq_5_1 H51.
    + assume Hbad2 : 5 = 4 \/ 5 = 7.
      apply Hbad2.
      * assume H54 : 5 = 4.
        apply FalseE.
        exact neq_5_4 H54.
      * assume H57 : 5 = 7.
        apply FalseE.
        apply neq_7_5.
        prove 7 = 5.
        rewrite <- H57.
        exact eq_refl 5.
  - assume Hrest :
      (j = 1 /\ (5 = 2 \/ 5 = 5))
      \/ ((j = 2 /\ (5 = 3 \/ 5 = 6))
          \/ ((j = 3 /\ (5 = 4 \/ 5 = 7))
              \/ ((j = 4 /\ 5 = 5) \/ ((j = 5 /\ 5 = 6) \/ (j = 6 /\ 5 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (5 = 2 \/ 5 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 5 = 2 \/ 5 = 5.
      apply orIL (j = 1) (j = 4 \/ j = 6).
      exact Hj1.
    + assume Hrest2 :
        (j = 2 /\ (5 = 3 \/ 5 = 6))
        \/ ((j = 3 /\ (5 = 4 \/ 5 = 7))
            \/ ((j = 4 /\ 5 = 5) \/ ((j = 5 /\ 5 = 6) \/ (j = 6 /\ 5 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (5 = 3 \/ 5 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 5 = 3 \/ 5 = 6.
        apply Hbad.
        - assume H53 : 5 = 3.
          apply FalseE.
          exact neq_5_3 H53.
        - assume H56 : 5 = 6.
          apply FalseE.
          apply neq_6_5.
          prove 6 = 5.
          rewrite <- H56.
          exact eq_refl 5.
      * assume Hrest3 :
          (j = 3 /\ (5 = 4 \/ 5 = 7))
          \/ ((j = 4 /\ 5 = 5) \/ ((j = 5 /\ 5 = 6) \/ (j = 6 /\ 5 = 7))).
        apply Hrest3.
	        - assume H3 : j = 3 /\ (5 = 4 \/ 5 = 7).
	          apply H3.
	          assume Hj3 : j = 3.
	          assume Hbad : 5 = 4 \/ 5 = 7.
	          apply Hbad.
	          + assume H54 : 5 = 4.
	            apply FalseE.
	            exact neq_5_4 H54.
	          + assume H57 : 5 = 7.
	            apply FalseE.
	            apply neq_7_5.
	            prove 7 = 5.
            rewrite <- H57.
            exact eq_refl 5.
        - assume Hrest4 : (j = 4 /\ 5 = 5) \/ ((j = 5 /\ 5 = 6) \/ (j = 6 /\ 5 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 5 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H55 : 5 = 5.
            apply orIR (j = 1) (j = 4 \/ j = 6).
            apply orIL (j = 4) (j = 6).
            exact Hj4. }
          { assume Hrest5 : (j = 5 /\ 5 = 6) \/ (j = 6 /\ 5 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 5 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H56 : 5 = 6.
              apply FalseE.
              apply neq_6_5.
              prove 6 = 5.
              rewrite <- H56.
              exact eq_refl 5.
            - assume H6 : j = 6 /\ 5 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H57 : 5 = 7.
              apply FalseE.
              apply neq_7_5.
              prove 7 = 5.
              rewrite <- H57.
	              exact eq_refl 5. }
Qed.

Theorem Adj8_cases_6 : forall j, Adj8 6 j -> j = 2 \/ (j = 5 \/ j = 7).
let j.
assume H : Adj8 6 j.
apply H.
- assume Hraw : Adj8_raw 6 j.
  apply Hraw.
  - assume H0 : 6 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 6 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_6_0 Heq.
  - assume Hrest :
      (6 = 1 /\ (j = 2 \/ j = 5))
      \/ ((6 = 2 /\ (j = 3 \/ j = 6))
          \/ ((6 = 3 /\ (j = 4 \/ j = 7))
              \/ ((6 = 4 /\ j = 5)
                  \/ ((6 = 5 /\ j = 6) \/ (6 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 6 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 6 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_6_1 Heq.
    + assume Hrest2 :
        (6 = 2 /\ (j = 3 \/ j = 6))
        \/ ((6 = 3 /\ (j = 4 \/ j = 7))
            \/ ((6 = 4 /\ j = 5) \/ ((6 = 5 /\ j = 6) \/ (6 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 6 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 6 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        exact neq_6_2 Heq.
      * assume Hrest3 :
          (6 = 3 /\ (j = 4 \/ j = 7))
          \/ ((6 = 4 /\ j = 5) \/ ((6 = 5 /\ j = 6) \/ (6 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 6 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 6 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          exact neq_6_3 Heq.
        - assume Hrest4 : (6 = 4 /\ j = 5) \/ ((6 = 5 /\ j = 6) \/ (6 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 6 = 4 /\ j = 5.
            apply H4.
            assume Heq : 6 = 4.
            assume Hj : j = 5.
            apply FalseE.
            exact neq_6_4 Heq. }
          { assume Hrest5 : (6 = 5 /\ j = 6) \/ (6 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 6 = 5 /\ j = 6.
              apply H5.
              assume Heq : 6 = 5.
              assume Hj : j = 6.
              apply FalseE.
              exact neq_6_5 Heq.
            - assume H6 : 6 = 6 /\ j = 7.
              apply H6.
              assume H66 : 6 = 6.
              assume Hj : j = 7.
              apply orIR (j = 2) (j = 5 \/ j = 7).
              apply orIR (j = 5) (j = 7).
	              exact Hj. }
- assume Hraw : Adj8_raw j 6.
  apply Hraw.
  - assume H0 : j = 0 /\ (6 = 1 \/ (6 = 4 \/ 6 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hbad : 6 = 1 \/ (6 = 4 \/ 6 = 7).
    apply Hbad.
    + assume H61 : 6 = 1.
      apply FalseE.
      exact neq_6_1 H61.
    + assume Hbad2 : 6 = 4 \/ 6 = 7.
      apply Hbad2.
      * assume H64 : 6 = 4.
        apply FalseE.
        exact neq_6_4 H64.
      * assume H67 : 6 = 7.
        apply FalseE.
        apply neq_7_6.
        prove 7 = 6.
        rewrite <- H67.
        exact eq_refl 6.
  - assume Hrest :
      (j = 1 /\ (6 = 2 \/ 6 = 5))
      \/ ((j = 2 /\ (6 = 3 \/ 6 = 6))
          \/ ((j = 3 /\ (6 = 4 \/ 6 = 7))
              \/ ((j = 4 /\ 6 = 5) \/ ((j = 5 /\ 6 = 6) \/ (j = 6 /\ 6 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (6 = 2 \/ 6 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 6 = 2 \/ 6 = 5.
      apply Hbad.
      * assume H62 : 6 = 2.
        apply FalseE.
        exact neq_6_2 H62.
      * assume H65 : 6 = 5.
        apply FalseE.
        exact neq_6_5 H65.
    + assume Hrest2 :
        (j = 2 /\ (6 = 3 \/ 6 = 6))
        \/ ((j = 3 /\ (6 = 4 \/ 6 = 7))
            \/ ((j = 4 /\ 6 = 5) \/ ((j = 5 /\ 6 = 6) \/ (j = 6 /\ 6 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (6 = 3 \/ 6 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 6 = 3 \/ 6 = 6.
        apply orIL (j = 2) (j = 5 \/ j = 7).
        exact Hj2.
      * assume Hrest3 :
          (j = 3 /\ (6 = 4 \/ 6 = 7))
          \/ ((j = 4 /\ 6 = 5) \/ ((j = 5 /\ 6 = 6) \/ (j = 6 /\ 6 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (6 = 4 \/ 6 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 6 = 4 \/ 6 = 7.
          apply Hbad.
          + assume H64 : 6 = 4.
            apply FalseE.
            exact neq_6_4 H64.
          + assume H67 : 6 = 7.
            apply FalseE.
            apply neq_7_6.
            prove 7 = 6.
            rewrite <- H67.
            exact eq_refl 6.
        - assume Hrest4 : (j = 4 /\ 6 = 5) \/ ((j = 5 /\ 6 = 6) \/ (j = 6 /\ 6 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 6 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H65 : 6 = 5.
            apply FalseE.
            exact neq_6_5 H65. }
          { assume Hrest5 : (j = 5 /\ 6 = 6) \/ (j = 6 /\ 6 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 6 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H66 : 6 = 6.
              apply orIR (j = 2) (j = 5 \/ j = 7).
              apply orIL (j = 5) (j = 7).
              exact Hj5.
            - assume H6 : j = 6 /\ 6 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H67 : 6 = 7.
              apply FalseE.
              apply neq_7_6.
              prove 7 = 6.
              rewrite <- H67.
	              exact eq_refl 6. }
Qed.

Theorem Adj8_cases_7 : forall j, Adj8 7 j -> j = 0 \/ (j = 3 \/ j = 6).
let j.
assume H : Adj8 7 j.
apply H.
- assume Hraw : Adj8_raw 7 j.
  apply Hraw.
  - assume H0 : 7 = 0 /\ (j = 1 \/ (j = 4 \/ j = 7)).
    apply H0.
    assume Heq : 7 = 0.
    assume Hj : j = 1 \/ (j = 4 \/ j = 7).
    apply FalseE.
    exact neq_7_0 Heq.
  - assume Hrest :
      (7 = 1 /\ (j = 2 \/ j = 5))
      \/ ((7 = 2 /\ (j = 3 \/ j = 6))
          \/ ((7 = 3 /\ (j = 4 \/ j = 7))
              \/ ((7 = 4 /\ j = 5)
                  \/ ((7 = 5 /\ j = 6) \/ (7 = 6 /\ j = 7))))).
    apply Hrest.
    + assume H1 : 7 = 1 /\ (j = 2 \/ j = 5).
      apply H1.
      assume Heq : 7 = 1.
      assume Hj : j = 2 \/ j = 5.
      apply FalseE.
      exact neq_7_1 Heq.
    + assume Hrest2 :
        (7 = 2 /\ (j = 3 \/ j = 6))
        \/ ((7 = 3 /\ (j = 4 \/ j = 7))
            \/ ((7 = 4 /\ j = 5) \/ ((7 = 5 /\ j = 6) \/ (7 = 6 /\ j = 7)))).
      apply Hrest2.
      * assume H2 : 7 = 2 /\ (j = 3 \/ j = 6).
        apply H2.
        assume Heq : 7 = 2.
        assume Hj : j = 3 \/ j = 6.
        apply FalseE.
        exact neq_7_2 Heq.
      * assume Hrest3 :
          (7 = 3 /\ (j = 4 \/ j = 7))
          \/ ((7 = 4 /\ j = 5) \/ ((7 = 5 /\ j = 6) \/ (7 = 6 /\ j = 7))).
        apply Hrest3.
        - assume H3 : 7 = 3 /\ (j = 4 \/ j = 7).
          apply H3.
          assume Heq : 7 = 3.
          assume Hj : j = 4 \/ j = 7.
          apply FalseE.
          exact neq_7_3 Heq.
        - assume Hrest4 : (7 = 4 /\ j = 5) \/ ((7 = 5 /\ j = 6) \/ (7 = 6 /\ j = 7)).
          apply Hrest4.
          { assume H4 : 7 = 4 /\ j = 5.
            apply H4.
            assume Heq : 7 = 4.
            assume Hj : j = 5.
            apply FalseE.
            exact neq_7_4 Heq. }
          { assume Hrest5 : (7 = 5 /\ j = 6) \/ (7 = 6 /\ j = 7).
            apply Hrest5.
            - assume H5 : 7 = 5 /\ j = 6.
              apply H5.
              assume Heq : 7 = 5.
              assume Hj : j = 6.
              apply FalseE.
              exact neq_7_5 Heq.
            - assume H6 : 7 = 6 /\ j = 7.
              apply H6.
              assume Heq : 7 = 6.
              assume Hj : j = 7.
              apply FalseE.
	              exact neq_7_6 Heq. }
- assume Hraw : Adj8_raw j 7.
  apply Hraw.
  - assume H0 : j = 0 /\ (7 = 1 \/ (7 = 4 \/ 7 = 7)).
    apply H0.
    assume Hj0 : j = 0.
    assume Hj' : 7 = 1 \/ (7 = 4 \/ 7 = 7).
    apply orIL (j = 0) (j = 3 \/ j = 6).
    exact Hj0.
  - assume Hrest :
      (j = 1 /\ (7 = 2 \/ 7 = 5))
      \/ ((j = 2 /\ (7 = 3 \/ 7 = 6))
          \/ ((j = 3 /\ (7 = 4 \/ 7 = 7))
              \/ ((j = 4 /\ 7 = 5) \/ ((j = 5 /\ 7 = 6) \/ (j = 6 /\ 7 = 7))))).
    apply Hrest.
    + assume H1 : j = 1 /\ (7 = 2 \/ 7 = 5).
      apply H1.
      assume Hj1 : j = 1.
      assume Hbad : 7 = 2 \/ 7 = 5.
      apply Hbad.
      * assume H72 : 7 = 2.
        apply FalseE.
        exact neq_7_2 H72.
      * assume H75 : 7 = 5.
        apply FalseE.
        exact neq_7_5 H75.
    + assume Hrest2 :
        (j = 2 /\ (7 = 3 \/ 7 = 6))
        \/ ((j = 3 /\ (7 = 4 \/ 7 = 7))
            \/ ((j = 4 /\ 7 = 5) \/ ((j = 5 /\ 7 = 6) \/ (j = 6 /\ 7 = 7)))).
      apply Hrest2.
      * assume H2 : j = 2 /\ (7 = 3 \/ 7 = 6).
        apply H2.
        assume Hj2 : j = 2.
        assume Hbad : 7 = 3 \/ 7 = 6.
        apply Hbad.
        - assume H73 : 7 = 3.
          apply FalseE.
          exact neq_7_3 H73.
        - assume H76 : 7 = 6.
          apply FalseE.
          exact neq_7_6 H76.
      * assume Hrest3 :
          (j = 3 /\ (7 = 4 \/ 7 = 7))
          \/ ((j = 4 /\ 7 = 5) \/ ((j = 5 /\ 7 = 6) \/ (j = 6 /\ 7 = 7))).
        apply Hrest3.
        - assume H3 : j = 3 /\ (7 = 4 \/ 7 = 7).
          apply H3.
          assume Hj3 : j = 3.
          assume Hbad : 7 = 4 \/ 7 = 7.
          apply orIR (j = 0) (j = 3 \/ j = 6).
          apply orIL (j = 3) (j = 6).
          exact Hj3.
        - assume Hrest4 : (j = 4 /\ 7 = 5) \/ ((j = 5 /\ 7 = 6) \/ (j = 6 /\ 7 = 7)).
          apply Hrest4.
          { assume H4 : j = 4 /\ 7 = 5.
            apply H4.
            assume Hj4 : j = 4.
            assume H75 : 7 = 5.
            apply FalseE.
            exact neq_7_5 H75. }
          { assume Hrest5 : (j = 5 /\ 7 = 6) \/ (j = 6 /\ 7 = 7).
            apply Hrest5.
            - assume H5 : j = 5 /\ 7 = 6.
              apply H5.
              assume Hj5 : j = 5.
              assume H76 : 7 = 6.
              apply FalseE.
              exact neq_7_6 H76.
            - assume H6 : j = 6 /\ 7 = 7.
              apply H6.
              assume Hj6 : j = 6.
              assume H77 : 7 = 7.
              apply orIR (j = 0) (j = 3 \/ j = 6).
              apply orIR (j = 3) (j = 6).
	              exact Hj6. }
Qed.

Theorem Adj8_not_0_2 : ~Adj8 0 2.
apply notI.
assume H02 : Adj8 0 2.
apply (Adj8_cases_0 2 H02).
- assume H21 : 2 = 1.
  apply FalseE.
  exact neq_2_1 H21.
- assume Hrest : 2 = 4 \/ 2 = 7.
  apply Hrest.
  + assume H24 : 2 = 4.
    apply FalseE.
    apply neq_4_2.
    prove 4 = 2.
    rewrite <- H24.
    exact eq_refl 2.
  + assume H27 : 2 = 7.
    apply FalseE.
    apply neq_7_2.
    prove 7 = 2.
    rewrite <- H27.
    exact eq_refl 2.
Qed.

Theorem Adj8_not_0_3 : ~Adj8 0 3.
apply notI.
assume H03 : Adj8 0 3.
apply (Adj8_cases_0 3 H03).
- assume H31 : 3 = 1.
  apply FalseE.
  exact neq_3_1 H31.
- assume Hrest : 3 = 4 \/ 3 = 7.
  apply Hrest.
  + assume H34 : 3 = 4.
    apply FalseE.
    apply neq_4_3.
    prove 4 = 3.
    rewrite <- H34.
    exact eq_refl 3.
  + assume H37 : 3 = 7.
    apply FalseE.
    apply neq_7_3.
    prove 7 = 3.
    rewrite <- H37.
    exact eq_refl 3.
Qed.

Theorem Adj8_not_0_5 : ~Adj8 0 5.
apply notI.
assume H05 : Adj8 0 5.
apply (Adj8_cases_0 5 H05).
- assume H51 : 5 = 1.
  apply FalseE.
  exact neq_5_1 H51.
- assume Hrest : 5 = 4 \/ 5 = 7.
  apply Hrest.
  + assume H54 : 5 = 4.
    apply FalseE.
    exact neq_5_4 H54.
  + assume H57 : 5 = 7.
    apply FalseE.
    apply neq_7_5.
    prove 7 = 5.
    rewrite <- H57.
    exact eq_refl 5.
Qed.

Theorem Adj8_not_0_6 : ~Adj8 0 6.
apply notI.
assume H06 : Adj8 0 6.
apply (Adj8_cases_0 6 H06).
- assume H61 : 6 = 1.
  apply FalseE.
  exact neq_6_1 H61.
- assume Hrest : 6 = 4 \/ 6 = 7.
  apply Hrest.
  + assume H64 : 6 = 4.
    apply FalseE.
    exact neq_6_4 H64.
  + assume H67 : 6 = 7.
    apply FalseE.
    apply neq_7_6.
    prove 7 = 6.
    rewrite <- H67.
    exact eq_refl 6.
Qed.

Theorem Adj8_not_1_3 : ~Adj8 1 3.
apply notI.
assume H13 : Adj8 1 3.
apply (Adj8_cases_1 3 H13).
- assume H30 : 3 = 0.
  apply FalseE.
  exact neq_3_0 H30.
- assume Hrest : 3 = 2 \/ 3 = 5.
  apply Hrest.
  + assume H32 : 3 = 2.
    apply FalseE.
    exact neq_3_2 H32.
  + assume H35 : 3 = 5.
    apply FalseE.
    apply neq_5_3.
    prove 5 = 3.
    rewrite <- H35.
    exact eq_refl 3.
Qed.

Theorem Adj8_not_1_4 : ~Adj8 1 4.
apply notI.
assume H14 : Adj8 1 4.
apply (Adj8_cases_1 4 H14).
- assume H40 : 4 = 0.
  apply FalseE.
  exact neq_4_0 H40.
- assume Hrest : 4 = 2 \/ 4 = 5.
  apply Hrest.
  + assume H42 : 4 = 2.
    apply FalseE.
    exact neq_4_2 H42.
  + assume H45 : 4 = 5.
    apply FalseE.
    apply neq_5_4.
    prove 5 = 4.
    rewrite <- H45.
    exact eq_refl 4.
Qed.

Theorem Adj8_not_1_6 : ~Adj8 1 6.
apply notI.
assume H16 : Adj8 1 6.
apply (Adj8_cases_1 6 H16).
- assume H60 : 6 = 0.
  apply FalseE.
  exact neq_6_0 H60.
- assume Hrest : 6 = 2 \/ 6 = 5.
  apply Hrest.
  + assume H62 : 6 = 2.
    apply FalseE.
    exact neq_6_2 H62.
  + assume H65 : 6 = 5.
    apply FalseE.
    exact neq_6_5 H65.
Qed.

Theorem Adj8_not_1_7 : ~Adj8 1 7.
apply notI.
assume H17 : Adj8 1 7.
apply (Adj8_cases_1 7 H17).
- assume H70 : 7 = 0.
  apply FalseE.
  exact neq_7_0 H70.
- assume Hrest : 7 = 2 \/ 7 = 5.
  apply Hrest.
  + assume H72 : 7 = 2.
    apply FalseE.
    exact neq_7_2 H72.
  + assume H75 : 7 = 5.
    apply FalseE.
    exact neq_7_5 H75.
Qed.

Theorem Adj8_not_2_4 : ~Adj8 2 4.
apply notI.
assume H24 : Adj8 2 4.
apply (Adj8_cases_2 4 H24).
- assume H41 : 4 = 1.
  apply FalseE.
  exact neq_4_1 H41.
- assume Hrest : 4 = 3 \/ 4 = 6.
  apply Hrest.
  + assume H43 : 4 = 3.
    apply FalseE.
    exact neq_4_3 H43.
  + assume H46 : 4 = 6.
    apply FalseE.
    apply neq_6_4.
    prove 6 = 4.
    rewrite <- H46.
    exact eq_refl 4.
Qed.

Theorem Adj8_not_2_5 : ~Adj8 2 5.
apply notI.
assume H25 : Adj8 2 5.
apply (Adj8_cases_2 5 H25).
- assume H51 : 5 = 1.
  apply FalseE.
  exact neq_5_1 H51.
- assume Hrest : 5 = 3 \/ 5 = 6.
  apply Hrest.
  + assume H53 : 5 = 3.
    apply FalseE.
    exact neq_5_3 H53.
  + assume H56 : 5 = 6.
    apply FalseE.
    apply neq_6_5.
    prove 6 = 5.
    rewrite <- H56.
    exact eq_refl 5.
Qed.

Theorem Adj8_not_2_7 : ~Adj8 2 7.
apply notI.
assume H27 : Adj8 2 7.
apply (Adj8_cases_2 7 H27).
- assume H71 : 7 = 1.
  apply FalseE.
  exact neq_7_1 H71.
- assume Hrest : 7 = 3 \/ 7 = 6.
  apply Hrest.
  + assume H73 : 7 = 3.
    apply FalseE.
    exact neq_7_3 H73.
  + assume H76 : 7 = 6.
    apply FalseE.
    exact neq_7_6 H76.
Qed.

Theorem Adj8_not_3_5 : ~Adj8 3 5.
apply notI.
assume H35 : Adj8 3 5.
apply (Adj8_cases_3 5 H35).
- assume H52 : 5 = 2.
  apply FalseE.
  exact neq_5_2 H52.
- assume Hrest : 5 = 4 \/ 5 = 7.
  apply Hrest.
  + assume H54 : 5 = 4.
    apply FalseE.
    exact neq_5_4 H54.
  + assume H57 : 5 = 7.
    apply FalseE.
    apply neq_7_5.
    prove 7 = 5.
    rewrite <- H57.
    exact eq_refl 5.
Qed.

Theorem Adj8_not_3_6 : ~Adj8 3 6.
apply notI.
assume H36 : Adj8 3 6.
apply (Adj8_cases_3 6 H36).
- assume H62 : 6 = 2.
  apply FalseE.
  exact neq_6_2 H62.
- assume Hrest : 6 = 4 \/ 6 = 7.
  apply Hrest.
  + assume H64 : 6 = 4.
    apply FalseE.
    exact neq_6_4 H64.
  + assume H67 : 6 = 7.
    apply FalseE.
    apply neq_7_6.
    prove 7 = 6.
    rewrite <- H67.
    exact eq_refl 6.
Qed.

Theorem Adj8_not_4_6 : ~Adj8 4 6.
apply notI.
assume H46 : Adj8 4 6.
apply (Adj8_cases_4 6 H46).
- assume H60 : 6 = 0.
  apply FalseE.
  exact neq_6_0 H60.
- assume Hrest : 6 = 3 \/ 6 = 5.
  apply Hrest.
  + assume H63 : 6 = 3.
    apply FalseE.
    exact neq_6_3 H63.
  + assume H65 : 6 = 5.
    apply FalseE.
    exact neq_6_5 H65.
Qed.

Theorem Adj8_not_4_7 : ~Adj8 4 7.
apply notI.
assume H47 : Adj8 4 7.
apply (Adj8_cases_4 7 H47).
- assume H70 : 7 = 0.
  apply FalseE.
  exact neq_7_0 H70.
- assume Hrest : 7 = 3 \/ 7 = 5.
  apply Hrest.
  + assume H73 : 7 = 3.
    apply FalseE.
    exact neq_7_3 H73.
  + assume H75 : 7 = 5.
    apply FalseE.
    exact neq_7_5 H75.
Qed.

Theorem Adj8_not_5_7 : ~Adj8 5 7.
apply notI.
assume H57 : Adj8 5 7.
apply (Adj8_cases_5 7 H57).
- assume H71 : 7 = 1.
  apply FalseE.
  exact neq_7_1 H71.
- assume Hrest : 7 = 4 \/ 7 = 6.
  apply Hrest.
  + assume H74 : 7 = 4.
    apply FalseE.
    exact neq_7_4 H74.
  + assume H76 : 7 = 6.
    apply FalseE.
    exact neq_7_6 H76.
Qed.

Theorem Adj8_triangle_free : triangle_free 8 Adj8.
Admitted.

Theorem Adj8_no_4_indep : no_k_indep 8 Adj8 4.
Admitted.

Theorem not_TwoRamseyProp_3_4_8 : ~TwoRamseyProp 3 4 8.
Admitted.

Theorem TwoRamseyProp_3_4_9 : TwoRamseyProp 3 4 9.
Admitted.
