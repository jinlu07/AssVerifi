From AssVerifi Require Import CSSsVerification.
From AssVerifi Require Import Aid.
Require Import Coq.Strings.String.
Require Export Coq.Lists.List.
Import ListNotations.

Lemma OptEqVal : forall (n1 n2:nat),
  Some n1 = Some n2 -> n1 = n2.
Proof.
  intros.
  inversion H. auto.
Qed.

Lemma ValEqOpt : forall (n1 n2:nat),
  n1 = n2 -> Some n1 = Some n2.
Proof.
  intros. auto.
Qed.
  
Lemma Inlist : forall n l,
  in_list [v2o n] l = true -> n = o2v l.
Proof.
  intros. unfold v2o, o2v.
  inversion H.
  destruct l.
  - destruct (n =? n0) eqn: H'.
    apply beq_true in H'; auto.
    discriminate.
  - discriminate.
Qed.

Lemma Inllist : forall n l,
  in_list_list [n] l = true -> n = l.
Proof.
  intros.
  inversion H.
  destruct l.
  - destruct (n =? 0) eqn: H'.
    apply beq_true in H'; auto.
    discriminate.
  - destruct (n =? S l) eqn: H'.
    apply beq_true in H'; auto.
    discriminate.
Qed.

Lemma oneqv : forall (l : option nat) n,
  n <> 0 ->
  (o2v l =? n) = beq_op_nat (v2o n) l.
Proof.
  intros.
  destruct l; simpl.
  - rewrite beq_comm. auto.
  - destruct n. destruct H. auto.
    auto.
Qed.

Lemma InHt : forall (l : option nat) n1 n2,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> 
o2v l = n1 \/ o2v l = n2.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    discriminate. auto. auto.
Qed.

Lemma InHt1 : forall (l : option nat) n1 n2 n3,
in_list [v2o n1; v2o n2; v2o n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 ->
o2v l = n1 \/ o2v l = n2 \/ o2v l = n3.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    destruct ((o2v l) =? n3) eqn : L3.
    apply beq_eq in L3.
    rewrite L3. right. right. reflexivity.
    rewrite oneqv in L3.
    rewrite L3 in H.
    discriminate. auto. auto. auto.
Qed.

Lemma InHt2 : forall (l : option nat) n1 n2 n3 n4,
in_list [v2o n1; v2o n2; v2o n3; v2o n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
o2v l = n1 \/ o2v l = n2 \/ o2v l = n3 \/ o2v l = n4.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    destruct ((o2v l) =? n3) eqn : L3.
    apply beq_eq in L3.
    rewrite L3. right. right. auto.
    rewrite oneqv in L3.
    rewrite L3 in H.
    destruct ((o2v l) =? n4) eqn : L4.
    apply beq_eq in L4. auto.
    rewrite oneqv in L4.
    rewrite L4 in H.
    discriminate. auto. auto. auto. auto.
Qed.

Lemma InHt3 : forall (l : option nat) n1 n2 n3 n4 n5,
in_list [v2o n1; v2o n2; v2o n3; v2o n4; v2o n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
o2v l = n1 \/ o2v l = n2 \/ o2v l = n3 \/ o2v l = n4 \/ o2v l = n5.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    destruct ((o2v l) =? n3) eqn : L3.
    apply beq_eq in L3.
    rewrite L3. right. right. auto.
    rewrite oneqv in L3.
    rewrite L3 in H.
    destruct ((o2v l) =? n4) eqn : L4.
    apply beq_eq in L4. auto.
    rewrite oneqv in L4.
    rewrite L4 in H.
    destruct ((o2v l) =? n5) eqn : L5.
    apply beq_eq in L5.
    rewrite L5. right. right. right. right. auto.
    rewrite oneqv in L5.
    rewrite L5 in H.
    discriminate.
    auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt2 : forall (l : option nat) n1 n2 n6 n7,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n1 <> n2 ->
exists k , (n2 !hv-> n6; n1 !hv-> n7; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H; rewrite H.
  exists (Some n7).
  rewrite hV_update_neq. rewrite hV_update_eq. reflexivity.
  auto.
  exists (Some n6).
  rewrite hV_update_eq. reflexivity.
  auto. auto.
Qed.

Lemma SafeinHt3 : forall (l : option nat) n1 n2 n3 n6 n7 n8,
in_list [v2o n1; v2o n2; v2o n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 ->
n1 <> n2 -> n1<>n3 -> n2<>n3 ->
exists k , (n3 !hv->n8;n2 !hv-> n6; n1 !hv-> n7; emp_heapV)
              (o2v l) = k.
Proof.
  intros.
  apply InHt1 in H.
  destruct H. rewrite H.
  exists (Some n7).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq. reflexivity.
  auto. auto.
  destruct H. rewrite H.
  exists (Some n6).
  rewrite hV_update_neq. rewrite hV_update_eq. reflexivity. auto.
  rewrite H.
  exists (Some n8).
  rewrite hV_update_eq.
  auto. auto. auto. auto. 
Qed.

Lemma SafeinHt4 : forall (l : option nat) n1 n2 n3 n4 n6 n7 n8 n9,
in_list [v2o n1; v2o n2; v2o n3; v2o n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
n1 <> n2 -> n1<>n3 -> n1<>n4 -> n2<>n3 -> n2<>n4 ->
n3<>n4 ->
exists k , (n4!hv->n9;n3 !hv->n8;n2 !hv-> n6; n1 !hv-> n7;
             emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt2 in H.
  destruct H. rewrite H.
  exists (Some n7).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
  rewrite hV_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n6).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq. 
  reflexivity. auto. auto.
  destruct H. rewrite H.
  exists (Some n8).
  rewrite hV_update_neq. rewrite hV_update_eq. auto. auto.
  rewrite H.
  exists (Some n9).
  rewrite hV_update_eq. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt5 : forall (l : option nat) n1 n2 n3 n4 n5 n11 n12 n13 n14 n15,
in_list [v2o n1; v2o n2; v2o n3; v2o n4; v2o n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 ->
 n3<>n4 -> n3<>n5 ->
 n4<>n5 -> 
exists k , (n5!hv->n15;n4!hv->n14;n3!hv->n13;n2!hv->n12;n1!hv->n11;emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt3 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto.
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto.
  rewrite H.
  exists (Some n15).
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt58 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n11 n12 n13 n14 
                                          n15 n16 n17 n18,
in_list [v2o n1; v2o n2; v2o n3; v2o n4; v2o n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 ->
 n6<>n7 -> n6<>n8 ->
 n7<>n8 ->
exists k , (n5!hv->n15;n4!hv->n14;n3!hv->n13;n2!hv->n12;n1!hv->n11;
            n6!hv->n16;n7!hv->n17;n8!hv->n18; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt3 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto. auto.
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto.
  rewrite H.
  exists (Some n15).
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt58z : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 
                                          n15 n16 n17 n18 n19 n20,
in_list [v2o n1; v2o n2; v2o n3; v2o n4; v2o n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0->
n9 <> 0 -> n10 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 ->
 n8<>n9 -> n8<>n10 ->
 n9<>n10 ->
exists k , (n6!hv->n16;n7!hv->n17;
            n5!hv->n15;n4!hv->n14;n3!hv->n13;n2!hv->n12;n1!hv->n11;
            n8!hv->n18;n9!hv->n19;n10!hv->n20; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt3 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
  rewrite H.
  exists (Some n15).
  rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto. auto. auto.
Qed.
Lemma SafeinHt47 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n11 n12 n13 n14 
                                          n15 n16 n17,
in_list [v2o n1; v2o n2; v2o n3; v2o n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 ->
 n5<>n6 -> n5<>n7 ->
 n6<>n7 ->
exists k , (n4!hv->n14;n3!hv->n13;n2!hv->n12;n1!hv->n11;
            n5!hv->n15;n6!hv->n16;n7!hv->n17; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt2 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto. auto.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto.
  rewrite H.
  exists (Some n14).
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto.
Qed.

Lemma SafeinHt34 : forall (l : option nat) n1 n2 n3 n4 n6 n7 n8 n9,
in_list [v2o n1; v2o n2; v2o n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
n1 <> n2 -> n1<>n3 -> n1<>n4 -> n2<>n3 -> n2<>n4 ->
n3<>n4 ->
exists k , (n3 !hv->n8;n2 !hv-> n6; n1 !hv-> n7;n4!hv->n9;
             emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt1 in H.
  destruct H. rewrite H.
  exists (Some n7).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto. auto.
  destruct H. rewrite H.
  exists (Some n6).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto.
  rewrite H.
  exists (Some n8).
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
Qed.

Lemma SafeinHt36 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n11 n12 n13 n14 
                                          n15 n16,
in_list [v2o n1; v2o n2; v2o n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 ->
 n4<>n5 -> n4<>n6 ->
 n5<>n6 ->
exists k , (n3!hv->n13;n2!hv->n12;n1!hv->n11;
            n4!hv->n14;n5!hv->n15;n6!hv->n16; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt1 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto.
  rewrite H.
  exists (Some n13).
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto.
Qed.

Lemma SafeinHt37z : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n11 n12 n13 n14 
                                          n15 n16 n17,
in_list [v2o n1; v2o n2; v2o n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 ->
 n5<>n6 -> n5<>n7 ->
 n6<>n7 ->
exists k , (n4!hv->n14;n5!hv->n15;n6!hv->n16;
            n3!hv->n13;n2!hv->n12;n1!hv->n11;n7!hv->n17; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt1 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto.
  rewrite H.
  exists (Some n13).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq. 
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt25 : forall (l : option nat) n1 n2 n3 n4 n5 n11 n12 n13 n14 
                                          n15,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 ->
 n3<>n4 -> n3<>n5 ->
 n4<>n5 ->
exists k , (n2!hv->n12;n1!hv->n11;
            n3!hv->n13;n4!hv->n14;n5!hv->n15; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_eq.
  reflexivity. auto. auto.
Qed.

Lemma SafeinHt24 : forall (l : option nat) n1 n2 n3 n4 n11 n12 n13 n14,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 ->
 n2<>n3 -> n2<>n4 ->
 n3<>n4 -> 
exists k , (n2!hv->n12;n1!hv->n11;
            n3!hv->n13;n4!hv->n14; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_eq.
  reflexivity. auto. auto.
Qed.

Lemma SafeinHt23 : forall (l : option nat) n1 n2 n3 n11 n12 n13,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 ->
 n1<>n2 -> n1<>n3 ->
 n2<>n3 ->
exists k , (n2!hv->n12;n1!hv->n11;
            n3!hv->n13; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_eq.
  reflexivity. auto. auto.
Qed.

Lemma SafeinHt27 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n11 n12 n13 n14 
                                          n15 n16 n17,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 ->
 n5<>n6 -> n5<>n7 ->
 n6<>n7 ->
exists k , (n2!hv->n12;n1!hv->n11;n3!hv->n13;n4!hv->n14;
            n5!hv->n15;n6!hv->n16;n7!hv->n17; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_eq.
  reflexivity. auto. auto.
Qed.

Lemma SafeinHt28d : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n11 n12 n13 n14 
                                          n15 n16 n17 n18,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 ->
 n6<>n7 -> n6<>n8 ->
 n7<>n8 ->
exists k , (n3!hv->n13;n4!hv->n14;n5!hv->n15;n6!hv->n16;n7!hv->n17;
           n8!hv->n18;n2!hv->n12;n1!hv->n11; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHt26z : forall (l : option nat) n1 n2 n3 n4 n5 n6 n11 n12 n13 n14 
                                          n15 n16,
in_list [v2o n1; v2o n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 ->
 n4<>n5 -> n4<>n6 ->
 n5<>n6 ->
exists k , (n3!hv->n13;n4!hv->n14;n5!hv->n15;
     n2!hv->n12;n1!hv->n11;n6!hv->n16; emp_heapV) (o2v l) = k.
Proof.
  intros.
  apply InHt in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_neq. rewrite hV_update_eq.
  reflexivity.
  auto. auto. auto. auto.
  rewrite H.
  exists (Some n12).
  rewrite hV_update_neq. rewrite hV_update_neq. rewrite hV_update_neq.
  rewrite hV_update_eq.
  reflexivity. auto. auto. auto. auto. auto.
Qed.





