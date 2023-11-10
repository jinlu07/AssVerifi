From AssVerifi Require Import CSSsVerification.
From AssVerifi Require Import Neqdefinition.
From AssVerifi Require Import SafeinHt.
From AssVerifi Require Import Aid.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope language_scope.
Definition IMPLEMENTATIONs2 :=
  t2_A1 ::=plan 1101;;
  t2_A1 ::=add 1102;;
  t2_A1 ::=add 1103;;
  t2_A1 ::=add 1104;;
  t2_A1 ::=add 1105;;
  s2 ::=asgn t2_A1;;
  PROCESSEXE s2 1;;
  free s2`1;;
  t1_A1' ::=plan 1201;;
  att (s2,t1_A1');;
  PROCESSEXE s2 1;;
  SKIP.

Lemma IMPLEMENTATIONs2_Abt1 :
forall (tt1_A1 tt1_A2 tt1_A1' tt2_A1 :nat)
       (loc_11 loc_21 loc_31 loc_42 loc_53 :nat)
       (loc_52 :nat)
       (loc_41 loc_51 loc_12 :nat),

neq0_tt4 tt1_A2 tt1_A1' tt1_A1 tt2_A1 ->
neq0_loc9 loc_11 loc_21 loc_31 loc_42 loc_53 loc_52 loc_41 loc_51 loc_12 ->

neq_t4 t1_A1' t1_A1 t1_A2 t2_A1 ->
neq_tt4 tt1_A2 tt1_A1' tt1_A1 tt2_A1 ->
neq_loc9 loc_11 loc_21 loc_31 loc_42 loc_53 loc_52 loc_41 loc_51 loc_12 ->

(null_sV,
t1_A1' !st-> tt1_A1'; t1_A2 !st-> tt1_A2; t1_A1 !st-> tt1_A1; null_sT,
s1 !ss-> [tt1_A1']; null_sS,
(loc_51!hv-> 0340;loc_41!hv-> 0517 ;loc_52!hv-> 1000 ; emp_heapV),
(tt1_A1'!ht-> [v2o loc_41;v2o loc_51]; emp_heapT )) =[
  IMPLEMENTATIONs2
]=> St (
(j !sv-> 0; len !sv-> 1; null_sV,
t1_A1' !st-> tt1_A1'; t2_A1 !st-> tt2_A1; t1_A2 !st-> tt1_A2; t1_A1 !st-> tt1_A1; null_sT,
s2 !ss-> []; s1 !ss-> [tt1_A1']; null_sS,
(loc_51!hv-> 0340;loc_41!hv-> 0517 ;loc_52!hv-> 1000 ; emp_heapV),
(tt1_A1'!ht-> [v2o loc_41;v2o loc_51]; emp_heapT ))).
Proof.
  unfold neq_t4, neq_tt4, neq_loc9.
  intros tt1_A1 tt1_A2 tt1_A1' tt2_A1.
  intros loc_11 loc_21 loc_31 loc_42 loc_53 loc_52 loc_41 loc_51 loc_12.
  intros [H [H0 [H1 H2]]].
  intros [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]].
  intros [H12 [H13 [H14 [H15 [H16 H17]]]]].
  intros [H18 [H19 [H20 [H21 [H22 H23]]]]].
  intros [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 
         [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 [H48 [H49 [H50 [H51 [H52 [H53 
         [H54 [H55 [H56 [H57 [H58 H59]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  eapply E_Seq.
  - eapply E_Tplan with (tloc := tt2_A1) (loc := loc_11).     (*1101*)
    reflexivity. rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto.
    apply hT_update_neq. auto.
  - eapply E_Seq.
    eapply E_Tadd with (tloc := tt2_A1) (loc := loc_21).     (*1102*)
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 1101).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq. auto. auto. auto. auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.                                              (*1103*)
    eapply E_Tadd with (tloc := tt2_A1) (loc := loc_31).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt25;auto. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. apply hV_update_neq. auto. auto. auto. auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.                                                (*1104*)
    eapply E_Tadd with (tloc := tt2_A1) (loc := loc_42).
    reflexivity. rewrite hT_update_eq. reflexivity. 
    intros l L0.
    apply SafeinHt36;auto. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto. auto. auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.                                                 (*1105*)
    eapply E_Tadd with (tloc := tt2_A1) (loc := loc_53).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt47;auto. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq. auto. auto. auto. auto. auto. auto. auto. simpl.
    rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Sasgn with (tloc := tt2_A1). simpl. rewrite sT_update_eq. reflexivity.

    eapply E_Seq.
    eapply E_Seq.
    eapply E_Tlength. simpl. reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt58;auto.
    simpl. reflexivity.

    eapply E_Seq.
    eapply E_Ass. reflexivity. simpl.

    eapply E_WhileLoop.
    reflexivity.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt58;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_11; v2o loc_21; v2o loc_31; v2o loc_42; v2o loc_53]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq. rewrite hV_remove_neq. 
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    unfold not_in_domV.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt47;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_21; v2o loc_31; v2o loc_42; v2o loc_53]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq. rewrite hV_remove_neq. 
    rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    unfold not_in_domV.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt36;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_31; v2o loc_42; v2o loc_53]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq.
    rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    unfold not_in_domV.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt25;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_42; v2o loc_53]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    unfold not_in_domV.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 1105).
    rewrite L0. rewrite hV_update_eq. reflexivity.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_53]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_work. rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    unfold not_in_domV.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. auto. auto.
    eapply E_WhileEnd. reflexivity.
    rewrite sV_update_shadow.

    eapply E_Seq.
    eapply E_Tfree with (s := s2). reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply Inllist in L0. exists (Some []).
    rewrite L0. rewrite hT_update_eq. reflexivity.
    reflexivity. rewrite hT_update_eq. reflexivity. reflexivity.
    rewrite hT_remove_work. simpl. rewrite <- beq_refl. simpl.
    rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Tplan with (tloc := tt1_A1') (loc := loc_12).
    reflexivity. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq. auto. auto. auto.
    rewrite hT_update_eq. reflexivity.