From AssVerifi Require Import CSSsVerification.
From AssVerifi Require Import Neqdefinition.
From AssVerifi Require Import SafeinHt.
From AssVerifi Require Import SafeinSs.
From AssVerifi Require Import Aid.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope language_scope.
Definition DEPLOYMENTs1 :=
  t1_A1 ::=plan 0417;;
  t1_A1 ::=add 0617;;
  t1_A1 ::=add 0817;;
  t1_A2 ::=plan 1000;;
  t1_A2 ::=add 1001;;
  t1_A2 ::=add 1002;;
  t1_A2 ::=add 1003;;
  t1_A2 ::=add 1004;;
  t1_A1' ::=plan 0340;;
  t1_A1' ::=add 0517;;
  s1 ::=asgn t1_A1;;
  att (s1,t1_A2);;
  att (s1,t1_A1');;
  x ::={s1`2,3}.

Lemma DEPLOYMENTs1_Correct :
forall (tt1_A1 tt1_A2 tt1_A1' :nat)
       (loc_11_A1 loc_21_A1 loc_31_A1 loc_41_A1 loc_51_A1 :nat)
       (loc_11_A2 loc_22_A2 loc_32_A2 loc_41_A2 loc_52_A2 :nat),

neq0_tt3 tt1_A2 tt1_A1' tt1_A1 ->
neq0_loc10 loc_11_A1 loc_21_A1 loc_31_A1 loc_41_A1 loc_51_A1
          loc_11_A2 loc_22_A2 loc_32_A2 loc_41_A2 loc_52_A2 ->

neq_t3 t1_A1' t1_A1 t1_A2 ->
neq_tt3 tt1_A2 tt1_A1' tt1_A1 ->
neq_loc10 loc_11_A1 loc_21_A1 loc_31_A1 loc_41_A1 loc_51_A1
          loc_11_A2 loc_22_A2 loc_32_A2 loc_41_A2 loc_52_A2 ->

empty_st =[
  DEPLOYMENTs1
]=> St (
(x!sv->1002; null_sV,
 t1_A1' !st-> tt1_A1'; t1_A2 !st-> tt1_A2; t1_A1 !st-> tt1_A1; null_sT,
 s1 !ss-> [tt1_A1;tt1_A2;tt1_A1']; null_sS,
 (loc_51_A1!hv-> 0517 ;loc_41_A1!hv-> 0340 ;
  loc_52_A2!hv-> 1004 ;loc_41_A2!hv-> 1003 ;loc_32_A2!hv-> 1002 ;loc_22_A2!hv-> 1001 ;loc_11_A2!hv-> 1000 ;
  loc_31_A1!hv-> 0817 ;loc_21_A1!hv-> 0617 ;loc_11_A1!hv-> 0417; emp_heapV),
 (tt1_A1'!ht-> [v2o loc_41_A1;v2o loc_51_A1];
  tt1_A2!ht-> [v2o loc_11_A2;v2o loc_22_A2;v2o loc_32_A2;v2o loc_41_A2;v2o loc_52_A2];
  tt1_A1!ht-> [v2o loc_11_A1;v2o loc_21_A1;v2o loc_31_A1]; emp_heapT ))).

Proof.
  unfold neq0_tt3, neq0_loc10, neq_t3, neq_tt3, neq_loc10.
  intros tt1_A1 tt1_A2 tt1_A1'.
  intros loc_11_A1 loc_21_A1 loc_31_A1 loc_41_A1 loc_51_A1
         loc_11_A2 loc_22_A2 loc_32_A2 loc_41_A2 loc_52_A2.
  intros [H [H0 H1]].
  intros [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]].
  intros [H12 [H13 H14]].
  intros [H15 [H16 H17]].
  intros [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 
         [H33 [H34 [H35 [H36 [H37 [H38 [H39 [H40 [H41 [H42 [H43 [H44 [H45 [H46 [H47 
         [H48 [H49 [H50 [H51 [H52 [H53 [H54 [H55 [H56 [H57 [H58 [H59 [H60 [H61 H62
         ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  eapply E_Seq.
  - eapply E_Tplan with (loc := loc_11_A1); reflexivity.
  - eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1) (loc := loc_21_A1).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 417).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    apply hV_update_neq. auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1) (loc := loc_31_A1). 
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt2;auto. reflexivity.
    rewrite hV_update_neq. apply hV_update_neq.
    auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tplan with (tloc := tt1_A2) (loc := loc_11_A2). reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto.
    apply hT_update_neq. auto. simpl.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_22_A2).
    reflexivity. rewrite hT_update_eq. reflexivity. 
    intros l L0.
    apply Inlist in L0. exists (Some 1000).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq. 
    auto. auto. auto. auto. simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_32_A2).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt25;auto.
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. apply hV_update_neq. 
    auto. auto. auto. auto. auto. simpl.
    rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_41_A2).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt36;auto.
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto. auto. auto. auto.
    simpl. rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A2) (loc := loc_52_A2).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply SafeinHt47;auto.
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    apply hV_update_neq.
    auto. auto. auto. auto. auto. auto. auto. simpl.
    rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Tplan with (tloc := tt1_A1') (loc := loc_41_A1).
    reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto. auto. auto. auto. auto. auto.
    rewrite hT_update_neq. apply hT_update_neq. auto. auto. simpl.

    eapply E_Seq.
    eapply E_Tadd with (tloc := tt1_A1') (loc := loc_51_A1).
    reflexivity. rewrite hT_update_eq. reflexivity.
    intros l L0.
    apply Inlist in L0. exists (Some 340).
    rewrite L0. rewrite hV_update_eq. reflexivity. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_neq. apply hV_update_neq.
    auto. auto. auto. auto. auto. auto. auto. auto. auto. simpl.
    rewrite hT_update_shadow.

    eapply E_Seq.
    eapply E_Sasgn with (tloc := tt1_A1). simpl. 
    rewrite sT_update_neq. rewrite sT_update_neq. rewrite sT_update_eq. reflexivity.
    auto. auto. auto.

    eapply E_Seq.
    eapply E_Sattach with (tloc := tt1_A2). simpl.
    rewrite sT_update_neq. rewrite sT_update_eq. reflexivity. auto.
    reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply Inllist in L0. rewrite L0.
    exists (Some [v2o loc_11_A1; v2o loc_21_A1; v2o loc_31_A1]).
    rewrite hT_update_neq. rewrite hT_update_neq. rewrite hT_update_eq.
    reflexivity. rewrite <- L0. auto. rewrite <- L0. auto.
    simpl. rewrite sS_update_shadow.

    eapply E_Seq.
    eapply E_Sattach with (tloc := tt1_A1'). simpl. rewrite sT_update_eq. reflexivity.
    reflexivity. rewrite sS_update_eq.
    intros l L0.
    apply SafeinSs23d;auto.
    simpl. rewrite sS_update_shadow.

    eapply E_Tlookup. simpl; auto. rewrite hT_update_neq.
    rewrite hT_update_eq. reflexivity. auto.
    intros l L0.
    apply SafeinHt58z;auto.
    simpl. reflexivity. reflexivity.
    rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
    rewrite hV_update_neq. rewrite hV_update_eq.
    reflexivity. auto. auto. auto. auto.
Qed.
Close Scope language_scope.