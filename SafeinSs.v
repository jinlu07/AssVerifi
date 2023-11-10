From AssVerifi Require Import CSSsVerification.
From AssVerifi Require Import Aid.
Require Import Coq.Strings.String.
Import ListNotations.

Lemma InSs : forall n1 n2 l,
  in_list_list [n1;n2] l = true -> 
n1 <> 0 -> n2 <> 0 -> 
l = n1 \/ l = n2.
Proof.
  intros.
    destruct (l =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct (l =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. 
    rewrite beq_neq in L1. rewrite neq_comm in L1. rewrite <- beq_neq in L1.
    rewrite beq_neq in L2. rewrite neq_comm in L2. rewrite <- beq_neq in L2.
    unfold in_list_list in H.
    rewrite L1 in H. rewrite L2 in H.
    discriminate.
Qed.

Lemma SafeinSs23d : forall (v1 v2 v3: list (option nat)) l n1 n2 n3,
in_list_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n1 <> n2 -> n1 <> n3 -> n3 <> n2 ->
exists k , (n3 !ht-> v3;n2 !ht-> v2; n1 !ht-> v1; emp_heapT) l = k.
Proof.
  intros.
  apply InSs in H.
  destruct H; rewrite H.
  exists (Some v1).
  rewrite hT_update_neq. rewrite hT_update_neq. rewrite hT_update_eq. reflexivity.
  auto. auto.
  exists (Some v2).
  rewrite hT_update_neq. rewrite hT_update_eq. reflexivity.
  auto. auto. auto.
Qed.

Lemma SafeinSs2z3 : forall (v1 v2 v3: list (option nat)) l n1 n2 n3,
in_list_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n1 <> n2 -> n1 <> n3 -> n3 <> n2 ->
exists k , (n1 !ht-> v1;n3 !ht-> v3;n2 !ht-> v2; emp_heapT) l = k.
Proof.
  intros.
  apply InSs in H.
  destruct H; rewrite H.
  exists (Some v1).
  rewrite hT_update_eq. reflexivity.
  exists (Some v2).
  rewrite hT_update_neq. rewrite hT_update_neq. rewrite hT_update_eq. reflexivity.
  auto. auto. auto. auto.
Qed.