Definition sigma_generated : set -> set -> set :=
  fun Omega F =>
    Eps_i (fun G =>
      is_sigma_field Omega G
      /\ F c= G
      /\ (forall H, is_sigma_field Omega H -> F c= H -> G c= H)).

Definition is_premeasure : set -> set -> (set -> set) -> prop :=
  fun Omega F mu =>
    is_field Omega F
    /\ ((forall A :e F, mu A :e real /\ 0 <= mu A)
    /\ (mu Empty = 0
    /\ (forall f : set -> set,
          (forall n :e omega, f n :e F) ->
          pairwise_disjoint f ->
          bigcup_nat f :e F ->
          mu (bigcup_nat f) = series_sum (fun n => mu (f n))))).

Definition is_measure_extension : set -> set -> (set -> set) -> (set -> set) -> prop :=
  fun Omega F mu mu_ext =>
    is_premeasure Omega F mu
    /\ is_probability_measure Omega (sigma_generated Omega F) mu_ext
    /\ (forall A :e F, mu_ext A = mu A).

Theorem premeasure_is_field :
  forall Omega F, forall mu : set -> set,
    is_premeasure Omega F mu -> is_field Omega F.
let Omega. let F. let mu : set -> set.
assume H.
exact andEL (is_field Omega F)
            ((forall A :e F, mu A :e real /\ 0 <= mu A)
             /\ (mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n))))) H.
Qed.

Theorem premeasure_empty :
  forall Omega F, forall mu : set -> set,
    is_premeasure Omega F mu -> mu Empty = 0.
let Omega. let F. let mu : set -> set.
assume H.
claim Hrest: (forall A :e F, mu A :e real /\ 0 <= mu A)
             /\ (mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n)))).
  exact andER (is_field Omega F)
              ((forall A :e F, mu A :e real /\ 0 <= mu A)
               /\ (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n))))) H.
claim Hrest2: mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n))).
  exact andER (forall A :e F, mu A :e real /\ 0 <= mu A)
              (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n)))) Hrest.
exact andEL (mu Empty = 0)
            (forall f : set -> set,
              (forall n :e omega, f n :e F) ->
              pairwise_disjoint f ->
              bigcup_nat f :e F ->
              mu (bigcup_nat f) = series_sum (fun n => mu (f n))) Hrest2.
Qed.

Theorem premeasure_value_real :
  forall Omega F, forall mu : set -> set,
    is_premeasure Omega F mu -> forall A :e F, mu A :e real.
let Omega. let F. let mu : set -> set.
assume H.
claim Hrest: (forall A :e F, mu A :e real /\ 0 <= mu A)
             /\ (mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n)))).
  exact andER (is_field Omega F)
              ((forall A :e F, mu A :e real /\ 0 <= mu A)
               /\ (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n))))) H.
claim Hnonneg: forall A :e F, mu A :e real /\ 0 <= mu A.
  exact andEL (forall A :e F, mu A :e real /\ 0 <= mu A)
              (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n)))) Hrest.
let A.
assume HA: A :e F.
exact andEL (mu A :e real) (0 <= mu A) (Hnonneg A HA).
Qed.

Theorem premeasure_nonneg :
  forall Omega F, forall mu : set -> set,
    is_premeasure Omega F mu -> forall A :e F, 0 <= mu A.
let Omega. let F. let mu : set -> set.
assume H.
claim Hrest: (forall A :e F, mu A :e real /\ 0 <= mu A)
             /\ (mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n)))).
  exact andER (is_field Omega F)
              ((forall A :e F, mu A :e real /\ 0 <= mu A)
               /\ (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n))))) H.
claim Hnonneg: forall A :e F, mu A :e real /\ 0 <= mu A.
  exact andEL (forall A :e F, mu A :e real /\ 0 <= mu A)
              (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n)))) Hrest.
let A.
assume HA: A :e F.
exact andER (mu A :e real) (0 <= mu A) (Hnonneg A HA).
Qed.

Theorem premeasure_countable_additivity :
  forall Omega F, forall mu : set -> set,
    is_premeasure Omega F mu ->
    forall f : set -> set,
      (forall n :e omega, f n :e F) ->
      pairwise_disjoint f ->
      bigcup_nat f :e F ->
      mu (bigcup_nat f) = series_sum (fun n => mu (f n)).
let Omega. let F. let mu : set -> set.
assume H.
claim Hrest: (forall A :e F, mu A :e real /\ 0 <= mu A)
             /\ (mu Empty = 0
             /\ (forall f : set -> set,
                   (forall n :e omega, f n :e F) ->
                   pairwise_disjoint f ->
                   bigcup_nat f :e F ->
                   mu (bigcup_nat f) = series_sum (fun n => mu (f n)))).
  exact andER (is_field Omega F)
              ((forall A :e F, mu A :e real /\ 0 <= mu A)
               /\ (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n))))) H.
claim Hrest2: mu Empty = 0
              /\ (forall f : set -> set,
                    (forall n :e omega, f n :e F) ->
                    pairwise_disjoint f ->
                    bigcup_nat f :e F ->
                    mu (bigcup_nat f) = series_sum (fun n => mu (f n))).
  exact andER (forall A :e F, mu A :e real /\ 0 <= mu A)
              (mu Empty = 0
               /\ (forall f : set -> set,
                     (forall n :e omega, f n :e F) ->
                     pairwise_disjoint f ->
                     bigcup_nat f :e F ->
                     mu (bigcup_nat f) = series_sum (fun n => mu (f n)))) Hrest.
claim Hadd: forall f : set -> set,
    (forall n :e omega, f n :e F) ->
    pairwise_disjoint f ->
    bigcup_nat f :e F ->
    mu (bigcup_nat f) = series_sum (fun n => mu (f n)).
  exact andER (mu Empty = 0)
              (forall f : set -> set,
                (forall n :e omega, f n :e F) ->
                pairwise_disjoint f ->
                bigcup_nat f :e F ->
                mu (bigcup_nat f) = series_sum (fun n => mu (f n))) Hrest2.
let f.
assume Hf.
assume Hdisj.
assume Hbig.
exact Hadd f Hf Hdisj Hbig.
Qed.

Theorem caratheodory_measurable_complement :
  forall Omega, forall mu : set -> set, forall A,
    caratheodory_measurable Omega mu A ->
    caratheodory_measurable Omega mu (Omega :\: A).
let Omega. let mu : set -> set. let A.
assume H.
claim HA: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) H.
claim Hcar: forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A).
  exact andER (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) H.
apply andI (Omega :\: A c= Omega)
           (forall E, E c= Omega -> mu E = mu (E :/\: (Omega :\: A)) + mu (E :\: (Omega :\: A))).
- exact setminus_Subq Omega A.
- let E.
  assume HE: E c= Omega.
  claim HEOmega: E :/\: Omega = E.
    exact binintersect_Subq_eq_1 E Omega HE.
  claim Hinter: E :/\: (Omega :\: A) = E :\: A.
  {
    claim Hbin: (E :/\: Omega) :\: A = E :/\: (Omega :\: A).
      exact binintersect_setminus E Omega A.
    claim Hbin_sym: E :/\: (Omega :\: A) = (E :/\: Omega) :\: A.
      exact eq_sym ((E :/\: Omega) :\: A) (E :/\: (Omega :\: A)) Hbin.
    rewrite Hbin_sym.
    rewrite HEOmega.
    reflexivity.
  }
  claim Hdiff: E :\: (Omega :\: A) = E :/\: A.
  {
    claim Hsub: E :\: Omega c= E :\: E.
      exact setminus_Subq_contra E Omega E HE.
    claim Hself: E :\: E c= Empty.
    {
      rewrite (setminus_selfannih E).
      exact Subq_Empty Empty.
    }
    claim Hsub_empty: E :\: Omega c= Empty.
      exact Subq_tra (E :\: Omega) (E :\: E) Empty Hsub Hself.
    claim Hempty: E :\: Omega = Empty.
      exact Empty_Subq_eq (E :\: Omega) Hsub_empty.
    claim Hdiff0: E :\: (Omega :\: A) = (E :\: Omega) :\/: (E :/\: A).
      exact setminus_setminus E Omega A.
    rewrite Hdiff0.
    rewrite Hempty.
    rewrite (binunion_idl (E :/\: A)).
    reflexivity.
  }
  claim HcarE: mu E = mu (E :/\: A) + mu (E :\: A).
    exact Hcar E HE.
  rewrite Hinter.
  rewrite Hdiff.
  rewrite (real_add_comm (mu (E :\: A)) (mu (E :/\: A))).
  exact HcarE.
Qed.

Theorem measurable_set_complement :
  forall Omega, forall mu : set -> set, forall A,
    measurable_set Omega mu A ->
    measurable_set Omega mu (Omega :\: A).
let Omega. let mu : set -> set. let A.
assume H.
exact caratheodory_measurable_complement Omega mu A H.
Qed.

Theorem caratheodory_measurable_empty :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    caratheodory_measurable Omega mu Empty.
let Omega. let mu : set -> set.
assume Hmu.
apply andI (Empty c= Omega)
           (forall E, E c= Omega -> mu E = mu (E :/\: Empty) + mu (E :\: Empty)).
- exact Subq_Empty Omega.
- let E.
  assume HE: E c= Omega.
  claim Hinter: E :/\: Empty = Empty.
    exact binintersect_annir E.
  claim Hdiff: E :\: Empty = E.
    exact setminus_idr E.
  claim HmuEmpty: mu Empty = 0.
    exact outer_measure_empty Omega mu Hmu.
  rewrite Hinter.
  rewrite Hdiff.
  rewrite HmuEmpty.
  rewrite (real_add_zero_l (mu E)).
  reflexivity.
Qed.

Theorem caratheodory_measurable_omega :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    caratheodory_measurable Omega mu Omega.
let Omega. let mu : set -> set.
assume Hmu.
apply andI (Omega c= Omega)
           (forall E, E c= Omega -> mu E = mu (E :/\: Omega) + mu (E :\: Omega)).
- exact Subq_ref Omega.
- let E.
  assume HE: E c= Omega.
  claim Hinter: E :/\: Omega = E.
    exact binintersect_Subq_eq_1 E Omega HE.
  claim Hsub: E :\: Omega c= E :\: E.
    exact setminus_Subq_contra E Omega E HE.
  claim Hself: E :\: E c= Empty.
  {
    rewrite (setminus_selfannih E).
    exact Subq_Empty Empty.
  }
  claim Hsub_empty: E :\: Omega c= Empty.
    exact Subq_tra (E :\: Omega) (E :\: E) Empty Hsub Hself.
  claim Hempty: E :\: Omega = Empty.
    exact Empty_Subq_eq (E :\: Omega) Hsub_empty.
  claim HmuEmpty: mu Empty = 0.
    exact outer_measure_empty Omega mu Hmu.
  rewrite Hinter.
  rewrite Hempty.
  rewrite HmuEmpty.
  rewrite (real_add_zero_r (mu E)).
  reflexivity.
Qed.

Theorem measurable_set_empty :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    measurable_set Omega mu Empty.
let Omega. let mu : set -> set.
assume Hmu.
exact caratheodory_measurable_empty Omega mu Hmu.
Qed.

Theorem measurable_set_omega :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    measurable_set Omega mu Omega.
let Omega. let mu : set -> set.
assume Hmu.
exact caratheodory_measurable_omega Omega mu Hmu.
Qed.

Theorem caratheodory_measurable_intersection :
  forall Omega, forall mu : set -> set, forall A B,
    caratheodory_measurable Omega mu A ->
    caratheodory_measurable Omega mu B ->
    caratheodory_measurable Omega mu (A :/\: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
claim HAsub: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim HBsub: B c= Omega.
  exact andEL (B c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: B) + mu (E :\: B)) HB.
claim HcarA: forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A).
  exact andER (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim HcarB: forall E, E c= Omega -> mu E = mu (E :/\: B) + mu (E :\: B).
  exact andER (B c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: B) + mu (E :\: B)) HB.
apply andI (A :/\: B c= Omega)
           (forall E, E c= Omega -> mu E = mu (E :/\: (A :/\: B)) + mu (E :\: (A :/\: B))).
- exact Subq_tra (A :/\: B) A Omega (binintersect_Subq_1 A B) HAsub.
- let E.
  assume HE: E c= Omega.
  claim HEA: E :/\: A c= Omega.
    exact Subq_tra (E :/\: A) E Omega (binintersect_Subq_1 E A) HE.
  claim HmuE0: mu E = mu (E :/\: A) + mu (E :\: A).
    exact HcarA E HE.
  claim HmuEA: mu (E :/\: A) = mu ((E :/\: A) :/\: B) + mu ((E :/\: A) :\: B).
    exact HcarB (E :/\: A) HEA.
  claim HmuE1: mu E = (mu ((E :/\: A) :/\: B) + mu ((E :/\: A) :\: B)) + mu (E :\: A).
  {
    rewrite HmuE0.
    rewrite HmuEA.
    reflexivity.
  }
  claim Hassoc: (mu ((E :/\: A) :/\: B) + mu ((E :/\: A) :\: B)) + mu (E :\: A)
                = mu ((E :/\: A) :/\: B) + (mu ((E :/\: A) :\: B) + mu (E :\: A)).
  {
    exact eq_sym (mu ((E :/\: A) :/\: B) + (mu ((E :/\: A) :\: B) + mu (E :\: A)))
                 ((mu ((E :/\: A) :/\: B) + mu ((E :/\: A) :\: B)) + mu (E :\: A))
                 (real_add_assoc (mu ((E :/\: A) :/\: B)) (mu ((E :/\: A) :\: B)) (mu (E :\: A))).
  }
  claim HmuE2: mu E = mu ((E :/\: A) :/\: B) + (mu ((E :/\: A) :\: B) + mu (E :\: A)).
  {
    rewrite HmuE1.
    exact Hassoc.
  }
  set D := E :\: (A :/\: B).
  claim HDsub: D c= Omega.
  {
    claim HDsubE: D c= E.
      exact setminus_Subq E (A :/\: B).
    exact Subq_tra D E Omega HDsubE HE.
  }
  claim HmuD0: mu D = mu (D :/\: A) + mu (D :\: A).
    exact HcarA D HDsub.
  claim Hinter: D :/\: A = (E :/\: A) :\: B.
  {
    apply set_ext.
    - prove D :/\: A c= (E :/\: A) :\: B.
      let z.
      assume Hz: z :e D :/\: A.
      claim HzD: z :e D. exact binintersectE1 D A z Hz.
      claim HzA: z :e A. exact binintersectE2 D A z Hz.
      claim HzE: z :e E. exact setminusE1 E (A :/\: B) z HzD.
      claim HzNotAB: z /:e A :/\: B. exact setminusE2 E (A :/\: B) z HzD.
      claim HnAB: z /:e A \/ z /:e B.
        exact binintersect_nIn_E A B z HzNotAB.
      claim HzNotB: z /:e B.
      {
        apply orE (z /:e A) (z /:e B) (z /:e B)
          (fun HnA => FalseE (HnA HzA) (z /:e B))
          (fun HnB => HnB)
          HnAB.
      }
      apply setminusI.
      + apply binintersectI.
        * exact HzE.
        * exact HzA.
      + exact HzNotB.
    - prove (E :/\: A) :\: B c= D :/\: A.
      let z.
      assume Hz: z :e (E :/\: A) :\: B.
      claim HzEA: z :e E :/\: A.
        exact setminusE1 (E :/\: A) B z Hz.
      claim HzE: z :e E.
        exact binintersectE1 E A z HzEA.
      claim HzA: z :e A.
        exact binintersectE2 E A z HzEA.
      claim HzNotB: z /:e B.
        exact setminusE2 (E :/\: A) B z Hz.
      apply binintersectI.
      + apply setminusI.
        * exact HzE.
        * assume HContra.
          claim HzB: z :e B. exact binintersectE2 A B z HContra.
          exact HzNotB HzB.
      + exact HzA.
  }
  claim Hdiff: D :\: A = E :\: A.
  {
    apply set_ext.
    - prove D :\: A c= E :\: A.
      let z.
      assume Hz: z :e D :\: A.
      claim HzD: z :e D.
        exact setminusE1 D A z Hz.
      claim HzNotA: z /:e A.
        exact setminusE2 D A z Hz.
      claim HzE: z :e E.
        exact setminusE1 E (A :/\: B) z HzD.
      exact setminusI E A z HzE HzNotA.
    - prove E :\: A c= D :\: A.
      let z.
      assume Hz: z :e E :\: A.
      claim HzE: z :e E.
        exact setminusE1 E A z Hz.
      claim HzNotA: z /:e A.
        exact setminusE2 E A z Hz.
      claim HzNotAB: z /:e A :/\: B.
      {
        assume HContra.
        claim HzA: z :e A. exact binintersectE1 A B z HContra.
        exact HzNotA HzA.
      }
      claim HzD: z :e D.
        exact setminusI E (A :/\: B) z HzE HzNotAB.
      exact setminusI D A z HzD HzNotA.
  }
  claim HmuD1: mu D = mu ((E :/\: A) :\: B) + mu (E :\: A).
  {
    rewrite HmuD0.
    rewrite Hinter.
    rewrite Hdiff.
    reflexivity.
  }
  claim HmuDsym: mu ((E :/\: A) :\: B) + mu (E :\: A) = mu D.
    exact eq_sym (mu D) (mu ((E :/\: A) :\: B) + mu (E :\: A)) HmuD1.
  claim HeqInter: (E :/\: A) :/\: B = E :/\: (A :/\: B).
  {
    exact eq_sym (E :/\: (A :/\: B)) ((E :/\: A) :/\: B) (binintersect_asso E A B).
  }
  rewrite HmuE2.
  rewrite HeqInter.
  rewrite HmuDsym.
  reflexivity.
Qed.

Theorem measurable_set_intersection :
  forall Omega, forall mu : set -> set, forall A B,
    measurable_set Omega mu A ->
    measurable_set Omega mu B ->
    measurable_set Omega mu (A :/\: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
exact caratheodory_measurable_intersection Omega mu A B HA HB.
Qed.

Theorem caratheodory_measurable_union :
  forall Omega, forall mu : set -> set, forall A B,
    caratheodory_measurable Omega mu A ->
    caratheodory_measurable Omega mu B ->
    caratheodory_measurable Omega mu (A :\/: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
claim HAsub: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim HBsub: B c= Omega.
  exact andEL (B c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: B) + mu (E :\: B)) HB.
claim HAc: caratheodory_measurable Omega mu (Omega :\: A).
  exact caratheodory_measurable_complement Omega mu A HA.
claim HBc: caratheodory_measurable Omega mu (Omega :\: B).
  exact caratheodory_measurable_complement Omega mu B HB.
claim Hinter: caratheodory_measurable Omega mu ((Omega :\: A) :/\: (Omega :\: B)).
  exact caratheodory_measurable_intersection Omega mu (Omega :\: A) (Omega :\: B) HAc HBc.
claim Hcomp: caratheodory_measurable Omega mu (Omega :\: ((Omega :\: A) :/\: (Omega :\: B))).
  exact caratheodory_measurable_complement Omega mu ((Omega :\: A) :/\: (Omega :\: B)) Hinter.
claim Heq: A :\/: B = Omega :\: ((Omega :\: A) :/\: (Omega :\: B)).
{
  apply set_ext.
  - prove A :\/: B c= Omega :\: ((Omega :\: A) :/\: (Omega :\: B)).
    let z.
    assume Hz: z :e A :\/: B.
    apply setminusI.
    + apply orE (z :e A) (z :e B) (z :e Omega)
        (fun HzA => HAsub z HzA)
        (fun HzB => HBsub z HzB)
        (binunionE A B z Hz).
    + assume HContra.
      apply orE (z :e A) (z :e B) False
        (fun HzA =>
          setminusE2 Omega A z (binintersectE1 (Omega :\: A) (Omega :\: B) z HContra) HzA)
        (fun HzB =>
          setminusE2 Omega B z (binintersectE2 (Omega :\: A) (Omega :\: B) z HContra) HzB)
        (binunionE A B z Hz).
  - prove (Omega :\: ((Omega :\: A) :/\: (Omega :\: B))) c= A :\/: B.
    let z.
    assume Hz: z :e Omega :\: ((Omega :\: A) :/\: (Omega :\: B)).
    claim HzOmega: z :e Omega.
      exact setminusE1 Omega ((Omega :\: A) :/\: (Omega :\: B)) z Hz.
    claim HzNotInter: z /:e (Omega :\: A) :/\: (Omega :\: B).
      exact setminusE2 Omega ((Omega :\: A) :/\: (Omega :\: B)) z Hz.
    claim HnInter: z /:e (Omega :\: A) \/ z /:e (Omega :\: B).
      exact binintersect_nIn_E (Omega :\: A) (Omega :\: B) z HzNotInter.
    apply orE (z /:e (Omega :\: A)) (z /:e (Omega :\: B)) (z :e A :\/: B)
      (fun HnA =>
        orE (z /:e Omega) (z :e A) (z :e A :\/: B)
          (fun HnOmega => FalseE (HnOmega HzOmega) (z :e A :\/: B))
          (fun HzA => binunionI1 A B z HzA)
          (setminus_nIn_E Omega A z HnA))
      (fun HnB =>
        orE (z /:e Omega) (z :e B) (z :e A :\/: B)
          (fun HnOmega => FalseE (HnOmega HzOmega) (z :e A :\/: B))
          (fun HzB => binunionI2 A B z HzB)
          (setminus_nIn_E Omega B z HnB))
      HnInter.
}
rewrite Heq.
exact Hcomp.
Qed.

Theorem measurable_set_union :
  forall Omega, forall mu : set -> set, forall A B,
    measurable_set Omega mu A ->
    measurable_set Omega mu B ->
    measurable_set Omega mu (A :\/: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
exact caratheodory_measurable_union Omega mu A B HA HB.
Qed.

Theorem measurable_family_is_field :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    is_field Omega (measurable_family Omega mu).
let Omega. let mu : set -> set.
assume Hmu.
set F := measurable_family Omega mu.
apply andI (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
           (forall A B, A :e F -> B :e F -> (A :\/: B) :e F).
- apply andI (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
             (forall A :e F, (Omega :\: A) :e F).
  - apply andI ((forall A :e F, A c= Omega) /\ Omega :e F)
               (Empty :e F).
    + apply andI (forall A :e F, A c= Omega)
                 (Omega :e F).
      * let A.
        assume HA: A :e F.
        claim HApow: A :e Power Omega.
          exact SepE1 (Power Omega) (fun X => measurable_set Omega mu X) A HA.
        exact PowerE Omega A HApow.
      * exact SepI (Power Omega) (fun X => measurable_set Omega mu X)
          Omega (Self_In_Power Omega) (measurable_set_omega Omega mu Hmu).
    + exact SepI (Power Omega) (fun X => measurable_set Omega mu X)
        Empty (Empty_In_Power Omega) (measurable_set_empty Omega mu Hmu).
  - let A.
    assume HA: A :e F.
    claim Hmeas: measurable_set Omega mu A.
      exact SepE2 (Power Omega) (fun X => measurable_set Omega mu X) A HA.
    exact SepI (Power Omega) (fun X => measurable_set Omega mu X)
      (Omega :\: A) (setminus_In_Power Omega A) (measurable_set_complement Omega mu A Hmeas).
- let A. let B.
  assume HA: A :e F.
  assume HB: B :e F.
  claim HApow: A :e Power Omega.
    exact SepE1 (Power Omega) (fun X => measurable_set Omega mu X) A HA.
  claim HBpow: B :e Power Omega.
    exact SepE1 (Power Omega) (fun X => measurable_set Omega mu X) B HB.
  claim HAsub: A c= Omega.
    exact PowerE Omega A HApow.
  claim HBsub: B c= Omega.
    exact PowerE Omega B HBpow.
  claim HunionSub: A :\/: B c= Omega.
    exact binunion_Subq_min A B Omega HAsub HBsub.
  claim HunionPow: A :\/: B :e Power Omega.
  {
    apply PowerEq Omega (A :\/: B).
    assume _ H2.
    exact (H2 HunionSub).
  }
  claim HAmeas: measurable_set Omega mu A.
    exact SepE2 (Power Omega) (fun X => measurable_set Omega mu X) A HA.
  claim HBmeas: measurable_set Omega mu B.
    exact SepE2 (Power Omega) (fun X => measurable_set Omega mu X) B HB.
  exact SepI (Power Omega) (fun X => measurable_set Omega mu X)
    (A :\/: B) HunionPow (measurable_set_union Omega mu A B HAmeas HBmeas).
Qed.

Theorem caratheodory_measurable_setminus :
  forall Omega, forall mu : set -> set, forall A B,
    caratheodory_measurable Omega mu A ->
    caratheodory_measurable Omega mu B ->
    caratheodory_measurable Omega mu (A :\: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
claim HAsub: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim HBc: caratheodory_measurable Omega mu (Omega :\: B).
  exact caratheodory_measurable_complement Omega mu B HB.
claim Hinter: caratheodory_measurable Omega mu (A :/\: (Omega :\: B)).
  exact caratheodory_measurable_intersection Omega mu A (Omega :\: B) HA HBc.
claim HAOmega: A :/\: Omega = A.
  exact binintersect_Subq_eq_1 A Omega HAsub.
set g := fun X : set => X :\: B.
claim Hg: (A :/\: Omega) :\: B = A :\: B.
  exact func_congr g (A :/\: Omega) A HAOmega.
claim Hg_sym: A :\: B = (A :/\: Omega) :\: B.
  exact eq_sym ((A :/\: Omega) :\: B) (A :\: B) Hg.
claim Htmp: (A :/\: Omega) :\: B = A :/\: (Omega :\: B).
  exact binintersect_setminus A Omega B.
claim Heq: A :\: B = A :/\: (Omega :\: B).
  exact eq_trans (A :\: B) ((A :/\: Omega) :\: B) (A :/\: (Omega :\: B)) Hg_sym Htmp.
rewrite Heq.
exact Hinter.
Qed.

Theorem measurable_set_setminus :
  forall Omega, forall mu : set -> set, forall A B,
    measurable_set Omega mu A ->
    measurable_set Omega mu B ->
    measurable_set Omega mu (A :\: B).
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
exact caratheodory_measurable_setminus Omega mu A B HA HB.
Qed.

Theorem caratheodory_measurable_disjoint_add :
  forall Omega, forall mu : set -> set, forall A B,
    caratheodory_measurable Omega mu A ->
    B c= Omega ->
    Disjoint A B ->
    mu (A :\/: B) = mu A + mu B.
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HBsub: B c= Omega.
assume Hd: Disjoint A B.
claim HdEq: A :/\: B = Empty.
  exact Hd.
claim HAsub: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim Hcar: forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A).
  exact andER (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
set E := A :\/: B.
claim HEsub: E c= Omega.
  exact binunion_Subq_min A B Omega HAsub HBsub.
claim HmuE: mu E = mu (E :/\: A) + mu (E :\: A).
  exact Hcar E HEsub.
claim Hinter: E :/\: A = A.
{
  apply set_ext.
  - prove E :/\: A c= A.
    let x.
    assume Hx: x :e E :/\: A.
    exact binintersectE2 E A x Hx.
  - prove A c= E :/\: A.
    let x.
    assume HxA: x :e A.
    apply binintersectI.
    + exact binunionI1 A B x HxA.
    + exact HxA.
}
claim Hdiff: E :\: A = B.
{
  apply set_ext.
  - prove E :\: A c= B.
    let x.
    assume Hx: x :e E :\: A.
    claim HxE: x :e E.
      exact setminusE1 E A x Hx.
    claim HxNotA: x /:e A.
      exact setminusE2 E A x Hx.
    apply binunionE A B x HxE.
    + assume HxA: x :e A.
      exact FalseE (HxNotA HxA) (x :e B).
    + assume HxB: x :e B.
      exact HxB.
  - prove B c= E :\: A.
    let x.
    assume HxB: x :e B.
    apply setminusI.
    + exact binunionI2 A B x HxB.
    + assume HxA: x :e A.
      claim HxInter: x :e A :/\: B.
        exact binintersectI A B x HxA HxB.
      claim HxEmpty: x :e Empty.
      {
        rewrite <- HdEq.
        exact HxInter.
      }
      exact EmptyE x HxEmpty.
}
rewrite HmuE.
rewrite Hinter.
rewrite Hdiff.
reflexivity.
Qed.

Theorem measurable_set_disjoint_add :
  forall Omega, forall mu : set -> set, forall A B,
    measurable_set Omega mu A ->
    measurable_set Omega mu B ->
    Disjoint A B ->
    mu (A :\/: B) = mu A + mu B.
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
assume Hd: Disjoint A B.
claim HBsub: B c= Omega.
  exact measurable_set_subset Omega mu B HB.
exact caratheodory_measurable_disjoint_add Omega mu A B HA HBsub Hd.
Qed.

Theorem measurable_set_monotone :
  forall Omega, forall mu : set -> set, forall A B,
    is_outer_measure Omega mu ->
    measurable_set Omega mu A ->
    B c= Omega ->
    A c= B ->
    mu A <= mu B.
let Omega. let mu : set -> set. let A. let B.
assume Hmu.
assume HA.
assume HBsub: B c= Omega.
assume HAsubB: A c= B.
claim Hcar: forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A).
  exact andER (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim HmuB: mu B = mu (B :/\: A) + mu (B :\: A).
  exact Hcar B HBsub.
claim Hinter: B :/\: A = A.
{
  apply set_ext.
  - prove B :/\: A c= A.
    let x.
    assume Hx: x :e B :/\: A.
    exact binintersectE2 B A x Hx.
  - prove A c= B :/\: A.
    let x.
    assume HxA: x :e A.
    apply binintersectI.
    + exact HAsubB x HxA.
    + exact HxA.
}
claim HmuB2: mu B = mu A + mu (B :\: A).
{
  rewrite HmuB.
  rewrite Hinter.
  reflexivity.
}
claim HBdiffSub: B :\: A c= Omega.
{
  claim HBdiffSubB: B :\: A c= B.
    exact setminus_Subq B A.
  exact Subq_tra (B :\: A) B Omega HBdiffSubB HBsub.
}
claim Hnonneg: 0 <= mu (B :\: A).
  exact outer_measure_nonneg Omega mu Hmu (B :\: A) HBdiffSub.
claim Hle: mu A <= mu A + mu (B :\: A).
  exact real_zero_le_implies_add_le (mu A) (mu (B :\: A)) Hnonneg.
rewrite HmuB2.
exact Hle.
Qed.

Theorem caratheodory_measurable_union_add_intersection :
  forall Omega, forall mu : set -> set, forall A B,
    caratheodory_measurable Omega mu A ->
    B c= Omega ->
    mu (A :\/: B) + mu (A :/\: B) = mu A + mu B.
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HBsub: B c= Omega.
claim HAsub: A c= Omega.
  exact andEL (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
claim Hcar: forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A).
  exact andER (A c= Omega)
              (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A)) HA.
set U := A :\/: B.
claim HUsub: U c= Omega.
  exact binunion_Subq_min A B Omega HAsub HBsub.
claim HmuU: mu U = mu (U :/\: A) + mu (U :\: A).
  exact Hcar U HUsub.
claim HUinter: U :/\: A = A.
{
  apply set_ext.
  - prove U :/\: A c= A.
    let x.
    assume Hx: x :e U :/\: A.
    exact binintersectE2 U A x Hx.
  - prove A c= U :/\: A.
    let x.
    assume HxA: x :e A.
    apply binintersectI.
    + exact binunionI1 A B x HxA.
    + exact HxA.
}
claim HUdiff: U :\: A = B :\: A.
{
  apply set_ext.
  - prove U :\: A c= B :\: A.
    let x.
    assume Hx: x :e U :\: A.
    claim HxU: x :e U.
      exact setminusE1 U A x Hx.
    claim HxNotA: x /:e A.
      exact setminusE2 U A x Hx.
    apply binunionE A B x HxU.
    + assume HxA: x :e A.
      exact FalseE (HxNotA HxA) (x :e B :\: A).
    + assume HxB: x :e B.
      exact setminusI B A x HxB HxNotA.
  - prove B :\: A c= U :\: A.
    let x.
    assume Hx: x :e B :\: A.
    claim HxB: x :e B.
      exact setminusE1 B A x Hx.
    claim HxNotA: x /:e A.
      exact setminusE2 B A x Hx.
    apply setminusI.
    + exact binunionI2 A B x HxB.
    + exact HxNotA.
}
claim HmuU2: mu U = mu A + mu (B :\: A).
{
  rewrite HmuU.
  rewrite HUinter.
  rewrite HUdiff.
  reflexivity.
}
claim HmuB: mu B = mu (B :/\: A) + mu (B :\: A).
  exact Hcar B HBsub.
claim HmuB2: mu B = mu (A :/\: B) + mu (B :\: A).
{
  rewrite HmuB.
  rewrite (binintersect_com B A).
  reflexivity.
}
rewrite HmuU2.
rewrite HmuB2.
rewrite <- (real_add_assoc (mu A) (mu (B :\: A)) (mu (A :/\: B))).
rewrite (real_add_comm (mu (B :\: A)) (mu (A :/\: B))).
reflexivity.
Qed.

Theorem measurable_set_union_add_intersection :
  forall Omega, forall mu : set -> set, forall A B,
    measurable_set Omega mu A ->
    measurable_set Omega mu B ->
    mu (A :\/: B) + mu (A :/\: B) = mu A + mu B.
let Omega. let mu : set -> set. let A. let B.
assume HA.
assume HB.
claim HBsub: B c= Omega.
  exact measurable_set_subset Omega mu B HB.
exact caratheodory_measurable_union_add_intersection Omega mu A B HA HBsub.
Qed.

Theorem bigcup_nat_subset :
  forall Omega, forall f : set -> set,
    (forall n :e omega, f n c= Omega) ->
    bigcup_nat f c= Omega.
let Omega. let f : set -> set.
assume Hf.
let x.
assume Hx: x :e bigcup_nat f.
claim BigDef: bigcup_nat f = Union {f n|n :e omega}. { reflexivity. }
claim HxU: x :e Union {f n|n :e omega}.
{ rewrite <- BigDef. exact Hx. }
apply (UnionE_impred {f n|n :e omega} x HxU).
let Y.
assume HxY: x :e Y.
assume HY: Y :e {f n|n :e omega}.
apply (ReplE_impred omega f Y HY).
let n.
assume Hn: n :e omega.
assume HYeq: Y = f n.
claim Hxfn: x :e f n.
{ rewrite <- HYeq. exact HxY. }
exact Hf n Hn x Hxfn.
Qed.

Theorem bigcup_fin_subset :
  forall Omega, forall f : set -> set, forall n,
    (forall i :e n, f i c= Omega) ->
    bigcup_fin f n c= Omega.
let Omega. let f : set -> set. let n.
assume Hf.
let x.
assume Hx: x :e bigcup_fin f n.
claim BigDef: bigcup_fin f n = Union {f i|i :e n}. { reflexivity. }
claim HxU: x :e Union {f i|i :e n}.
{ rewrite <- BigDef. exact Hx. }
apply (UnionE_impred {f i|i :e n} x HxU).
let Y.
assume HxY: x :e Y.
assume HY: Y :e {f i|i :e n}.
apply (ReplE_impred n f Y HY).
let i.
assume Hi: i :e n.
assume HYeq: Y = f i.
claim Hxfi: x :e f i.
{ rewrite <- HYeq. exact HxY. }
exact Hf i Hi x Hxfi.
Qed.

Theorem bigcup_fin_1 :
  forall f : set -> set,
    bigcup_fin f 1 = f 0.
let f : set -> set.
apply set_ext.
- prove bigcup_fin f 1 c= f 0.
  let x.
  assume Hx: x :e bigcup_fin f 1.
  claim BigDef: bigcup_fin f 1 = Union {f i|i :e 1}. { reflexivity. }
  claim HxU: x :e Union {f i|i :e 1}.
  { rewrite <- BigDef. exact Hx. }
  apply (UnionE_impred {f i|i :e 1} x HxU).
  let Y.
  assume HxY: x :e Y.
  assume HY: Y :e {f i|i :e 1}.
  apply (ReplE_impred 1 f Y HY).
  let i.
  assume Hi: i :e 1.
  assume HYeq: Y = f i.
  claim Hxfi: x :e f i.
  { rewrite <- HYeq. exact HxY. }
  claim Hi0: i = 0.
  {
    claim Hcases: i :e 0 \/ i = 0.
    { exact ordsuccE 0 i Hi. }
    apply orE (i :e 0) (i = 0) (i = 0)
      (fun HiIn0 =>
        FalseE (EmptyE i HiIn0) (i = 0))
      (fun HiEq => HiEq)
      Hcases.
  }
  rewrite <- Hi0.
  exact Hxfi.
- prove f 0 c= bigcup_fin f 1.
  let x.
  assume Hx: x :e f 0.
  claim BigDef: bigcup_fin f 1 = Union {f i|i :e 1}. { reflexivity. }
  rewrite BigDef.
  claim H0in: 0 :e 1.
  { exact ordsuccI2 0. }
  claim Hfam0: f 0 :e {f i|i :e 1}.
  { exact ReplI 1 f 0 H0in. }
  exact UnionI {f i|i :e 1} x (f 0) Hx Hfam0.
Qed.

Theorem bigcup_fin_succ :
  forall f : set -> set, forall n,
    bigcup_fin f (ordsucc n) = bigcup_fin f n :\/: f n.
let f : set -> set. let n.
apply set_ext.
- prove bigcup_fin f (ordsucc n) c= bigcup_fin f n :\/: f n.
  let x.
  assume Hx: x :e bigcup_fin f (ordsucc n).
  claim BigDef: bigcup_fin f (ordsucc n) = Union {f i|i :e ordsucc n}. { reflexivity. }
  claim HxU: x :e Union {f i|i :e ordsucc n}.
  { rewrite <- BigDef. exact Hx. }
  apply (UnionE_impred {f i|i :e ordsucc n} x HxU).
  let Y.
  assume HxY: x :e Y.
  assume HY: Y :e {f i|i :e ordsucc n}.
  apply (ReplE_impred (ordsucc n) f Y HY).
  let i.
  assume Hi: i :e ordsucc n.
  assume HYeq: Y = f i.
  claim Hxfi: x :e f i.
  { rewrite <- HYeq. exact HxY. }
  claim Hcases: i :e n \/ i = n.
  { exact ordsuccE n i Hi. }
  apply orE (i :e n) (i = n) (x :e bigcup_fin f n :\/: f n).
  + assume Hin.
    claim BigDef2: bigcup_fin f n = Union {f j|j :e n}. { reflexivity. }
    claim HxFin: x :e bigcup_fin f n.
    {
      rewrite BigDef2.
      claim HYin: f i :e {f j|j :e n}.
      { exact ReplI n f i Hin. }
      exact UnionI {f j|j :e n} x (f i) Hxfi HYin.
    }
    exact binunionI1 (bigcup_fin f n) (f n) x HxFin.
  + assume Heq.
    claim Hxfn: x :e f n.
    { rewrite <- Heq. exact Hxfi. }
    exact binunionI2 (bigcup_fin f n) (f n) x Hxfn.
  + exact Hcases.
- prove bigcup_fin f n :\/: f n c= bigcup_fin f (ordsucc n).
  let x.
  assume Hx: x :e bigcup_fin f n :\/: f n.
  claim BigDef: bigcup_fin f (ordsucc n) = Union {f i|i :e ordsucc n}. { reflexivity. }
  rewrite BigDef.
  apply binunionE (bigcup_fin f n) (f n) x Hx.
  + assume HxFin: x :e bigcup_fin f n.
    claim BigDef2: bigcup_fin f n = Union {f j|j :e n}. { reflexivity. }
    claim HxU: x :e Union {f j|j :e n}.
    { rewrite <- BigDef2. exact HxFin. }
    apply (UnionE_impred {f j|j :e n} x HxU).
    let Y.
    assume HxY: x :e Y.
    assume HY: Y :e {f j|j :e n}.
    apply (ReplE_impred n f Y HY).
    let j.
    assume Hj: j :e n.
    assume HYeq: Y = f j.
    claim Hxfj: x :e f j.
    { rewrite <- HYeq. exact HxY. }
    claim Hj_succ: j :e ordsucc n.
    { exact ordsuccI1 n j Hj. }
    claim HYin: f j :e {f i|i :e ordsucc n}.
    { exact ReplI (ordsucc n) f j Hj_succ. }
    exact UnionI {f i|i :e ordsucc n} x (f j) Hxfj HYin.
  + assume HxFn: x :e f n.
    claim Hn_succ: n :e ordsucc n.
    { exact ordsuccI2 n. }
    claim Hfam: f n :e {f i|i :e ordsucc n}.
    { exact ReplI (ordsucc n) f n Hn_succ. }
    exact UnionI {f i|i :e ordsucc n} x (f n) HxFn Hfam.
Qed.

Theorem bigcup_fin_subset_bigcup_nat :
  forall f : set -> set, forall n :e omega,
    bigcup_fin f n c= bigcup_nat f.
let f : set -> set. let n.
assume Hn: n :e omega.
let x.
assume Hx: x :e bigcup_fin f n.
claim HnSub: n c= omega.
{ exact omega_TransSet n Hn. }
claim BigDef: bigcup_fin f n = Union {f i|i :e n}. { reflexivity. }
claim HxU: x :e Union {f i|i :e n}.
{ rewrite <- BigDef. exact Hx. }
apply (UnionE_impred {f i|i :e n} x HxU).
let Y.
assume HxY: x :e Y.
assume HY: Y :e {f i|i :e n}.
apply (ReplE_impred n f Y HY).
let i.
assume Hi: i :e n.
assume HYeq: Y = f i.
claim Hxfi: x :e f i.
{ rewrite <- HYeq. exact HxY. }
claim HiOmega: i :e omega.
{ exact HnSub i Hi. }
claim BigDef2: bigcup_nat f = Union {f j|j :e omega}. { reflexivity. }
rewrite BigDef2.
claim HYin: f i :e {f j|j :e omega}.
{ exact ReplI omega f i HiOmega. }
exact UnionI {f j|j :e omega} x (f i) Hxfi HYin.
Qed.

Theorem bigcup_fin_measurable :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    forall f : set -> set,
      (forall n :e omega, measurable_set Omega mu (f n)) ->
      forall n :e omega, measurable_set Omega mu (bigcup_fin f n).
let Omega. let mu : set -> set.
assume Hmu.
let f : set -> set.
assume Hfmeas.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hgen: forall k, nat_p k -> measurable_set Omega mu (bigcup_fin f k).
{
  apply nat_ind.
  - prove measurable_set Omega mu (bigcup_fin f 0).
    claim H0: 0 :e omega. { exact nat_p_omega 0 nat_0. }
    claim H0eq: bigcup_fin f 0 = Empty.
    {
      claim BigDef: bigcup_fin f 0 = Union {f i|i :e 0}. { reflexivity. }
      rewrite BigDef.
      rewrite (Repl_Empty f).
      exact Union_Empty.
    }
    rewrite H0eq.
    exact measurable_set_empty Omega mu Hmu.
  - let k.
    assume Hk: nat_p k.
    assume IH: measurable_set Omega mu (bigcup_fin f k).
    prove measurable_set Omega mu (bigcup_fin f (ordsucc k)).
    claim HkOmega: k :e omega.
    { exact nat_p_omega k Hk. }
    claim Hfk: measurable_set Omega mu (f k).
    { exact Hfmeas k HkOmega. }
    rewrite (bigcup_fin_succ f k).
    exact measurable_set_union Omega mu (bigcup_fin f k) (f k) IH Hfk.
}
exact Hgen n Hn_nat.
Qed.

Theorem pairwise_disjoint_bigcup_fin_disjoint_succ :
  forall f : set -> set, forall n :e omega,
    pairwise_disjoint f ->
    Disjoint (bigcup_fin f (ordsucc n)) (f (ordsucc n)).
let f : set -> set.
let n.
assume Hn: n :e omega.
assume Hdisj: pairwise_disjoint f.
prove bigcup_fin f (ordsucc n) :/\: f (ordsucc n) = Empty.
apply Empty_Subq_eq.
let x.
assume Hx: x :e bigcup_fin f (ordsucc n) :/\: f (ordsucc n).
claim HxFin: x :e bigcup_fin f (ordsucc n).
{ exact binintersectE1 (bigcup_fin f (ordsucc n)) (f (ordsucc n)) x Hx. }
claim HxSucc: x :e f (ordsucc n).
{ exact binintersectE2 (bigcup_fin f (ordsucc n)) (f (ordsucc n)) x Hx. }
claim BigDef: bigcup_fin f (ordsucc n) = Union {f i|i :e ordsucc n}. { reflexivity. }
claim HxU: x :e Union {f i|i :e ordsucc n}.
{ rewrite <- BigDef. exact HxFin. }
apply (UnionE_impred {f i|i :e ordsucc n} x HxU).
let Y.
assume HxY: x :e Y.
assume HY: Y :e {f i|i :e ordsucc n}.
apply (ReplE_impred (ordsucc n) f Y HY).
let i.
assume Hi: i :e ordsucc n.
assume HYeq: Y = f i.
claim HxFi: x :e f i.
{ rewrite <- HYeq. exact HxY. }
claim Hineq: i <> ordsucc n.
{
  assume HiEq.
  claim Hcontra: ordsucc n :e ordsucc n.
  { rewrite <- HiEq at 1. exact Hi. }
  exact In_irref (ordsucc n) Hcontra.
}
claim HsuccSub: ordsucc n c= omega.
{ exact TransSet_ordsucc_In_Subq omega omega_TransSet n Hn. }
claim HiOmega: i :e omega.
{ exact HsuccSub i Hi. }
claim HdisjFi: Disjoint (f i) (f (ordsucc n)).
{ exact Hdisj i HiOmega (ordsucc n) (omega_ordsucc n Hn) Hineq. }
claim Hempty: f i :/\: f (ordsucc n) = Empty.
{ exact HdisjFi. }
claim HxInter: x :e f i :/\: f (ordsucc n).
{ exact binintersectI (f i) (f (ordsucc n)) x HxFi HxSucc. }
claim HxEmpty: x :e Empty.
{ rewrite <- Hempty. exact HxInter. }
exact HxEmpty.
Qed.

Theorem measurable_set_bigcup_fin_disjoint_sum :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    forall f : set -> set,
      (forall n :e omega, measurable_set Omega mu (f n)) ->
      pairwise_disjoint f ->
      forall n :e omega,
        mu (bigcup_fin f (ordsucc n)) = partial_sum (fun k => mu (f k)) n.
let Omega. let mu : set -> set.
assume Hmu.
let f : set -> set.
assume Hfmeas.
assume Hdisj: pairwise_disjoint f.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hgen: forall k, nat_p k -> mu (bigcup_fin f (ordsucc k)) = partial_sum (fun j => mu (f j)) k.
{
  apply nat_ind.
  - prove mu (bigcup_fin f (ordsucc 0)) = partial_sum (fun j => mu (f j)) 0.
    claim H0omega: 0 :e omega. { exact nat_p_omega 0 nat_0. }
    claim H1omega: ordsucc 0 :e omega.
    { exact omega_ordsucc 0 H0omega. }
    rewrite (bigcup_fin_1 f).
    rewrite (partial_sum_0 (fun j => mu (f j))).
    reflexivity.
  - let k.
    assume Hk: nat_p k.
    assume IH: mu (bigcup_fin f (ordsucc k)) = partial_sum (fun j => mu (f j)) k.
    prove mu (bigcup_fin f (ordsucc (ordsucc k))) = partial_sum (fun j => mu (f j)) (ordsucc k).
    claim HkOmega: k :e omega.
    { exact nat_p_omega k Hk. }
    claim HsuccOmega: ordsucc k :e omega.
    { exact omega_ordsucc k HkOmega. }
    claim Hprev_meas: measurable_set Omega mu (bigcup_fin f (ordsucc k)).
    { exact bigcup_fin_measurable Omega mu Hmu f Hfmeas (ordsucc k) HsuccOmega. }
    claim Hcurr_meas: measurable_set Omega mu (f (ordsucc k)).
    { exact Hfmeas (ordsucc k) HsuccOmega. }
    claim Hdisj_step: Disjoint (bigcup_fin f (ordsucc k)) (f (ordsucc k)).
    { exact pairwise_disjoint_bigcup_fin_disjoint_succ f k HkOmega Hdisj. }
    rewrite (bigcup_fin_succ f (ordsucc k)).
    claim Hadd: mu (bigcup_fin f (ordsucc k) :\/: f (ordsucc k)) =
                mu (bigcup_fin f (ordsucc k)) + mu (f (ordsucc k)).
    { exact measurable_set_disjoint_add Omega mu (bigcup_fin f (ordsucc k)) (f (ordsucc k)) Hprev_meas Hcurr_meas Hdisj_step. }
    rewrite Hadd.
    rewrite IH.
    rewrite (partial_sum_succ (fun j => mu (f j)) k HkOmega).
    rewrite (real_add_comm (mu (f (ordsucc k))) (partial_sum (fun j => mu (f j)) k)).
    reflexivity.
}
exact Hgen n Hn_nat.
Qed.

Theorem measurable_set_bigcup_fin_le_bigcup_nat :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    forall f : set -> set,
      (forall n :e omega, measurable_set Omega mu (f n)) ->
      pairwise_disjoint f ->
      forall n :e omega,
        partial_sum (fun k => mu (f k)) n <= mu (bigcup_nat f).
let Omega. let mu : set -> set.
assume Hmu.
let f : set -> set.
assume Hfmeas.
assume Hdisj: pairwise_disjoint f.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hsucc: ordsucc n :e omega.
{ exact omega_ordsucc n Hn. }
claim Hfin_meas: measurable_set Omega mu (bigcup_fin f (ordsucc n)).
{ exact bigcup_fin_measurable Omega mu Hmu f Hfmeas (ordsucc n) Hsucc. }
claim HsubAll: forall k :e omega, f k c= Omega.
{
  let k.
  assume Hk: k :e omega.
  exact measurable_set_subset Omega mu (f k) (Hfmeas k Hk).
}
claim HbigSub: bigcup_nat f c= Omega.
{ exact bigcup_nat_subset Omega f HsubAll. }
claim HfinSub: bigcup_fin f (ordsucc n) c= bigcup_nat f.
{ exact bigcup_fin_subset_bigcup_nat f (ordsucc n) Hsucc. }
claim HmuFin: mu (bigcup_fin f (ordsucc n)) <= mu (bigcup_nat f).
{ exact measurable_set_monotone Omega mu (bigcup_fin f (ordsucc n)) (bigcup_nat f) Hmu Hfin_meas HbigSub HfinSub. }
rewrite <- (measurable_set_bigcup_fin_disjoint_sum Omega mu Hmu f Hfmeas Hdisj n Hn).
exact HmuFin.
Qed.

Theorem measurable_set_countable_additivity_disjoint :
  forall Omega, forall mu : set -> set,
    is_outer_measure Omega mu ->
    forall f : set -> set,
      (forall n :e omega, measurable_set Omega mu (f n)) ->
      pairwise_disjoint f ->
      summable (fun n => mu (f n)) ->
      mu (bigcup_nat f) = series_sum (fun n => mu (f n)).
let Omega. let mu : set -> set.
assume Hmu.
let f : set -> set.
assume Hfmeas.
assume Hdisj: pairwise_disjoint f.
assume Hsummable: summable (fun n => mu (f n)).
set g := fun n : set => mu (f n).
claim HbigSubAll: forall n :e omega, f n c= Omega.
{
  let n.
  assume Hn: n :e omega.
  exact measurable_set_subset Omega mu (f n) (Hfmeas n Hn).
}
claim HbigSub: bigcup_nat f c= Omega.
{ exact bigcup_nat_subset Omega f HbigSubAll. }
claim HmuBig_real: mu (bigcup_nat f) :e real.
{ exact outer_measure_value_real Omega mu Hmu (bigcup_nat f) HbigSub. }
claim Hupper: is_upper_bound g (mu (bigcup_nat f)).
{
  let n.
  assume Hn: n :e omega.
  exact measurable_set_bigcup_fin_le_bigcup_nat Omega mu Hmu f Hfmeas Hdisj n Hn.
}
claim Hsum_lub: is_least_upper_bound g (series_sum g).
{ exact sum_nat_is_least_upper_bound g Hsummable. }
claim Hsum_le: series_sum g <= mu (bigcup_nat f).
{
  claim Hmin: forall t :e real, is_upper_bound g t -> series_sum g <= t.
  { exact andER (is_upper_bound g (series_sum g))
                (forall t :e real, is_upper_bound g t -> series_sum g <= t)
                Hsum_lub. }
  exact Hmin (mu (bigcup_nat f)) HmuBig_real Hupper.
}
claim Hsubadd: mu (bigcup_nat f) <= series_sum g.
{ exact outer_measure_subadditivity Omega mu Hmu f HbigSubAll. }
claim Hsum_real: series_sum g :e real.
{ exact sum_nat_real g Hsummable. }
exact real_leq_antisym (mu (bigcup_nat f)) HmuBig_real (series_sum g) Hsum_real Hsubadd Hsum_le.
Qed.
