From AssVerifi Require Import CSSsVerification.
From AssVerifi Require Import Neqdefinition.
From AssVerifi Require Import SafeinHt.
From AssVerifi Require Import Aid.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope language_scope.
Definition IMPLEMENTATIONs1 :=
  t1_A1 ::=plan 0417;;
  t1_A1 ::=add 0617;;
  t1_A1 ::=add 0817;;
  s1 ::=asgn t1_A1;;
  PROCESSEXE s1 1;;
  free s1`1;;
  t1_A2 ::=plan 1000;;
  t1_A2 ::=add 1001;;
  t1_A2 ::=add 1002;;
  t1_A2 ::=add 1003;;
  t1_A2 ::=add 1004;;
  att (s1,t1_A2);;
  PROCESSEXE s1 1;;
  free s1`1;;
  t1_A1' ::=plan 0340;;
  t1_A1' ::=add 0517;;
  att (s1,t1_A1');;
  PROCESSEXE s1 1;;
  free s1`1;;
  comp s1;;
  SKIP.

Lemma IMPLEMENTATIONs1_Correct :
forall (tt1_A1 tt1_A2 tt1_A1' :nat)
       (loc_11 loc_21 loc_31 loc_41 loc_51 :nat)
       (loc_22 loc_32 loc_52 :nat),

neq0_tt3 tt1_A2 tt1_A1' tt1_A1 ->
neq0_loc8 loc_11 loc_21 loc_31 loc_41 loc_51 loc_22 loc_32 loc_52 ->

neq_t3 t1_A1' t1_A1 t1_A2 ->
neq_tt3 tt1_A2 tt1_A1' tt1_A1 ->
neq_loc8 loc_11 loc_21 loc_31 loc_41 loc_51 loc_22 loc_32 loc_52 ->

empty_st =[
  IMPLEMENTATIONs1
]=> St (
(j !sv-> 0;len !sv-> 2; null_sV,
 t1_A1' !st-> tt1_A1'; t1_A2 !st-> tt1_A2; t1_A1 !st-> tt1_A1; null_sT,
 s1 !ss-> [fin]; null_sS, 
 emp_heapV,
 emp_heapT)).
Proof.
  unfold neq0_tt3, neq0_loc8, neq_t3, neq_tt3, neq_loc8.
  intros tt1_A1 tt1_A2 tt1_A1'.
  intros loc_11 loc_21 loc_31 loc_41 loc_51 loc_22 loc_32 loc_52.
  intros [H [H0 H1]].
  intros [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]].
  intros [H10 [H11 H12]].
  intros [H13 [H14 H15]].
  intros [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 
         [H28 [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 
         [H40 [H41 [H42 H43]]]]]]]]]]]]]]]]]]]]]]]]]]].
  eapply E_Seq.
  - eapply E_Tplan with (loc := loc_11); reflexivity.
  - eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1) (loc := loc_21).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 417).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    apply hV_update_neq. auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1) (loc := loc_31). 
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto. reflexivity.
    rewrite hV_update_neq. apply hV_update_neq.
    auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Sasgn with (tloc := tt1_A1). simpl. rewrite sT_update_eq. reflexivity.

    eapply E_Seq.
    eapply E_Seq.
    eapply E_Tlength. simpl. reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt3;auto.
    simpl. reflexivity.

    eapply E_Seq.
    eapply E_Ass. reflexivity. simpl.

    eapply E_WhileLoop.
    reflexivity.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt3;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_11; v2o loc_21; v2o loc_31]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. simpl. reflexivity.
    rewrite hV_remove_neq. rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_21; v2o loc_31]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. simpl. reflexivity.
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 817).
    rewrite L0. rewrite hV_update_eq. reflexivity.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_31]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_work. rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity. reflexivity.
    eapply E_WhileEnd. reflexivity.
    rewrite sV_update_shadow.

    eapply E_Seq.
    eapply E_Tfree with (s := s1). reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply Inllist in L0. exists (Some []).
    rewrite L0. rewrite hT_update_eq. reflexivity.
    reflexivity. rewrite hT_update_eq. reflexivity. reflexivity.
    rewrite hT_remove_work. simpl. rewrite <- beq_refl. simpl.
    rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Tplan with (tloc := tt1_A2) (loc := loc_11);reflexivity. simpl.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_22).
    reflexivity. rewrite hT_update_eq. reflexivity. 
    intros l L0.
    apply Inlist in L0. exists (Some 1000).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    apply hV_update_neq. 
    auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_32).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto.
    reflexivity.
    rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_41).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt3;auto.
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_52).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt4;auto.
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq.
    auto. auto. auto. auto. simpl.
    rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Sattach with (tloc := tt1_A2). simpl. rewrite sT_update_eq. reflexivity.
    reflexivity. rewrite sS_update_eq.
    intros l L0.
    unfold in_list_list in L0. discriminate.
    simpl. rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Seq.
    eapply E_Tlength. simpl. reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt5;auto.
    simpl. reflexivity. rewrite sV_update_shadow_2.

    eapply E_Seq.
    eapply E_Ass. reflexivity. simpl. rewrite sV_update_shadow_2.

    eapply E_WhileLoop.
    reflexivity.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt5;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_11; v2o loc_22; v2o loc_32; v2o loc_41; v2o loc_52]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq. rewrite hV_remove_neq. 
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt4;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_22; v2o loc_32; v2o loc_41; v2o loc_52]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq. rewrite hV_remove_neq. 
    rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt3;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_32; v2o loc_41; v2o loc_52]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_neq.
    rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_41; v2o loc_52]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 1004).
    rewrite L0. rewrite hV_update_eq. reflexivity.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_52]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_work. rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity. reflexivity.
    eapply E_WhileEnd. reflexivity.
    rewrite sV_update_shadow.

    eapply E_Seq.
    eapply E_Tfree with (s := s1). reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply Inllist in L0. exists (Some []).
    rewrite L0. rewrite hT_update_eq. reflexivity.
    reflexivity. rewrite hT_update_eq. reflexivity. reflexivity.
    rewrite hT_remove_work. simpl. rewrite <- beq_refl. simpl.
    rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Tplan with (tloc := tt1_A1') (loc := loc_41);reflexivity.
    simpl.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1') (loc := loc_51).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 340).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    apply hV_update_neq.
    auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Sattach with (tloc := tt1_A1'). simpl. rewrite sT_update_eq. reflexivity.
    reflexivity. rewrite sS_update_eq.
    intros l L0.
    unfold in_list_list in L0.
    discriminate.
    simpl. rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Seq.
    eapply E_Tlength. simpl. reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto.
    simpl. reflexivity. rewrite sV_update_shadow_2.

    eapply E_Seq.
    eapply E_Ass. reflexivity. simpl. rewrite sV_update_shadow_2.

    eapply E_WhileLoop.
    reflexivity.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_41; v2o loc_51]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_neq. rewrite hV_remove_work.
    rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity.
    reflexivity. auto.

    eapply E_WhileLoop.
    reflexivity. rewrite sV_update_shadow.
    eapply E_Seq.
    eapply E_Texe. simpl. reflexivity.
    rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 517).
    rewrite L0. rewrite hV_update_eq. reflexivity.
    rewrite sS_update_eq. reflexivity.
    intros l L0.
    apply Inllist in L0.
    rewrite L0. exists (Some [v2o loc_51]).
    rewrite hT_update_eq. reflexivity.
    reflexivity. reflexivity. simpl.
    rewrite hV_remove_work. rewrite hT_update_shadow.

    eapply E_Ass. simpl. reflexivity. reflexivity.
    eapply E_WhileEnd. reflexivity.
    rewrite sV_update_shadow.

    eapply E_Seq.
    eapply E_Tfree with (s := s1). reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply Inllist in L0. exists (Some []).
    rewrite L0. rewrite hT_update_eq. reflexivity.
    reflexivity. rewrite hT_update_eq. reflexivity. reflexivity.
    rewrite hT_remove_work. simpl. rewrite <- beq_refl. simpl.
    rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Scomp. rewrite sS_update_eq.
    reflexivity. rewrite sS_update_shadow.

    eapply E_Skip.
    reflexivity. reflexivity. reflexivity.
Qed.
Close Scope language_scope.