From AssVerifi Require Import util Aid.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(*定义五元组来表示系统状态*)

(*Sv, St, Ss*)
Definition storeV := id -> nat.
Definition storeT := id -> nat.
Definition storeS := id -> list nat.

(*Hv,Ht因为可能对应不到值,所以用可选类型*)
Definition heapV := nat -> option nat.
Definition heapT := nat -> option (list (option nat)).

(*定义空堆*)
Definition emp_heapV : heapV :=
  fun (n: nat) => None.

Definition emp_heapT : heapT :=
  fun (n: nat) => None.

(*定义命题 : 在堆的定义域中*)
Definition in_domV (loc: nat) (hv: heapV) : Prop :=
  exists n, hv loc = Some n.

Definition in_domT (tloc: nat) (ht: heapT) : Prop :=
  exists l, ht tloc = Some l.

(*定义命题 : 不在堆的定义域中*)
Definition not_in_domV (loc: nat) (hv: heapV) : Prop :=
  hv loc = None.

Definition not_in_domT (tloc: nat) (ht: heapT) : Prop :=
  ht tloc = None.


(*在定义域的(Some n) + 不在定义域的(None) 为全集*)
Theorem in_not_in_dec_V :
  forall l h, {in_domV l h} + {not_in_domV l h}.
Proof.
  intros l h.
  unfold in_domV, not_in_domV.
  destruct (h l).
  - left. exists n. auto.
  - right. auto.
Qed.

Theorem in_not_in_dec_T :
  forall l h, {in_domT l h} + {not_in_domT l h}.
Proof.
  intros l h.
  unfold in_domT, not_in_domT.
  destruct (h l).
  - left. exists l0. auto.
  - right. auto.
Qed.

(*定义命题:两堆不相交*)
Definition disjointV (h1 h2: heapV) : Prop :=
  forall l, not_in_domV l h1 \/ not_in_domV l h2.

Definition disjointT (h1 h2: heapT) : Prop :=
  forall l, not_in_domT l h1 \/ not_in_domT l h2.

(*heap1 析取 heap2*)
Definition h_unionV (h1 h2: heapV) : heapV :=
  fun l =>
    if (in_not_in_dec_V l h1) then h1 l else h2 l.

Definition h_unionT (h1 h2: heapT) : heapT :=
  fun l =>
    if (in_not_in_dec_T l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subsetV (h1 h2: heapV) : Prop :=
  forall loc n, h1 loc = Some n -> h2 loc = Some n.

Definition h_subsetT (h1 h2: heapT) : Prop :=
  forall tloc l, h1 tloc = Some l -> h2 tloc = Some l.


(* store update *)
Definition sV_update (s: storeV) (x: id) (n: nat) : storeV :=
  fun x' => if beq_id x x' then n else s x'.

Definition sT_update (s: storeT) (x: id) (n: nat) : storeT :=
  fun x' => if beq_id x x' then n else s x'.

Definition sS_update (s: storeS) (x: id) (nli: list nat) : storeS :=
  fun x' => if beq_id x x' then nli else s x'.

Notation "x '!sv->' v ';' m" := (sV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!st->' v ';' m" := (sT_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!ss->' v ';' m" := (sS_update m x v)
            (at level 100, v at next level, right associativity).

(* heap update *)
Definition hV_update (h: heapV) (loc: nat) (n: nat) : heapV :=
  fun loc' => if beq_nat loc loc' then Some n else h loc'.

Definition hT_update (h: heapT) (tloc: nat) (l: list (option nat)) : heapT :=
  fun tloc' => if beq_nat tloc tloc' then Some l else h tloc'.

Notation "x '!hv->' v ';' m" := (hV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!ht->' v ';' m" := (hT_update m x v)
            (at level 100, v at next level, right associativity).

(*在list中找是否有x*)
Fixpoint in_list_bool (llist:list nat) (x:nat) : bool :=
match llist with
|nil => false
|t::xli => if beq_nat t x then true else in_list_bool xli x
end.

(* heap remove *)
Definition hV_remove (h:heapV) (l:nat) : heapV :=
fun x => if beq_nat x l then None else h x.

Fixpoint hV_remove_list (h:heapV) (llist:list nat): heapV :=
match llist with
|nil => h
|x::l => hV_remove_list (hV_remove h x) l
end.

Definition hT_remove (h:heapT) (l:nat) : heapT :=
fun x => if beq_nat x l then None else h x.

(****Some Lemma****)
Lemma sV_update_eq : forall storeV x v,
   (x !sv-> v ; storeV) x = v.
Proof.
  intros.
  unfold sV_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma sT_update_eq : forall storeT x v,
   (x !st-> v ; storeT) x = v.
Proof.
  intros.
  unfold sT_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sT_update_neq :forall sT x1 x2 v,
   x1 <> x2
->(x2 !st-> v ; sT) x1 = sT x1.
Proof.
  intros.
  unfold sT_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sS_update_eq : forall storeS x v,
   (x !ss-> v ; storeS) x = v.
Proof.
  intros.
  unfold sS_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sS_update_neq :forall sS x1 x2 v,
   x1 <> x2
->(x2 !ss-> v ; sS) x1 = sS x1.
Proof.
  intros.
  unfold sS_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma hV_update_eq : forall heapV x v,
   (x !hv-> v ; heapV) x = Some v.
Proof.
  intros.
  unfold hV_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem hV_update_neq :forall hV x1 x2 v,
   x1 <> x2
->(x2 !hv-> v ; hV) x1 = hV x1.
Proof.
  intros.
  unfold hV_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma hT_update_eq : forall heapT x v,
   (x !ht-> v ; heapT) x = Some v.
Proof.
  intros.
  unfold hT_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem hT_update_neq :forall hT x1 x2 v,
   x1 <> x2
->(x2 !ht-> v ; hT) x1 = hT x1.
Proof.
  intros.
  unfold hT_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sV_update_shadow : forall storeV x v1 v2,
  (x !sv-> v2 ; x !sv-> v1 ; storeV) = (x !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sT_update_shadow : forall storeT x v1 v2,
  (x !st-> v2 ; x !st-> v1 ; storeT) = (x !st-> v2; storeT).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sT_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sT_update_shadow_3 : forall storeT x y v1 v2 v3,
  (x !st-> v2 ; y !st-> v1 ; x !st-> v3 ;storeT) 
= (x !st-> v2; y !st-> v1; storeT).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sT_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sT_update_shadow_4 : forall storeT x y z v1 v2 v3 v4,
  (x !st-> v2 ; y !st-> v1 ; z !st-> v4; x !st-> v3 ;storeT) 
= (x !st-> v2; y !st-> v1; z !st-> v4; storeT).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sT_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_2 : forall storeV x y v1 v2 v3,
  (x !sv-> v2 ; y !sv-> v1 ; x !sv-> v3 ;storeV) 
= (x !sv-> v2; y !sv-> v1; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_3 : forall storeV x y z v1 v2 v3 v4,
  (x !sv-> v2 ; y !sv-> v1 ; z !sv-> v4 ; x !sv-> v3 ;storeV) 
= (x !sv-> v2; y !sv-> v1 ; z !sv-> v4 ; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow : forall storeS x v1 v2,
  (x !ss-> v2 ; x !ss-> v1 ; storeS) = (x !ss-> v2; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow_3 : forall storeS x y v1 v2 v3,
  (x !ss-> v2 ; y !ss-> v1 ; x !ss-> v3 ;storeS) 
= (x !ss-> v2; y !ss-> v1; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hV_update_shadow : forall heapV x v1 v2,
  (x !hv-> v2 ; x !hv-> v1 ; heapV) = (x !hv-> v2; heapV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hV_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hT_update_shadow_4 : forall heapT x y z v1 v2 v3 v4,
  (x !ht-> v2 ; y !ht-> v3 ; z !ht-> v4 ; x !ht-> v1 ; heapT) = 
  (x !ht-> v2;y !ht-> v3 ; z !ht-> v4 ; heapT).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hT_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hT_update_shadow : forall heapT x v1 v2,
  (x !ht-> v2 ; x !ht-> v1 ; heapT) = (x !ht-> v2; heapT).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hT_update.
  destruct (beq_nat x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hT_remove_neq : forall hT x1 x2 v,
   x1 <> x2
-> hT_remove (x2 !ht-> v;hT) x1 
   = (x2 !ht-> v; hT_remove hT x1).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hT_remove.
  destruct (beq_nat x x1) eqn:H1.
  + rewrite beq_eq in H1.
    rewrite H1,hT_update_neq.
    rewrite <- beq_refl.
    trivial. trivial.
  + destruct (beq_nat x x2) eqn:H2.
    - rewrite beq_eq in H2. subst.
      repeat rewrite hT_update_eq. trivial.
    - rewrite beq_neq in H2.
      repeat rewrite hT_update_neq; trivial.
      rewrite H1.
      trivial.
Qed.

Lemma hV_remove_neq : forall hV x1 x2 v,
   x1 <> x2
-> hV_remove (x2 !hv-> v;hV) x1 
   = (x2 !hv-> v; (hV_remove hV x1)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hV_remove.
  destruct (beq_nat x x1) eqn:H1.
  + rewrite beq_eq in H1.
    rewrite H1,hV_update_neq.
    rewrite <- beq_refl.
    trivial. trivial.
  + destruct (beq_nat x x2) eqn:H2.
    - rewrite beq_eq in H2. subst.
      repeat rewrite hV_update_eq. trivial.
    - rewrite beq_neq in H2.
      repeat rewrite hV_update_neq; trivial.
      rewrite H1.
      trivial.
Qed.

Lemma hT_remove_emp : forall x,
  hT_remove emp_heapT x = emp_heapT.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hT_remove.
  destruct (beq_nat x0 x) eqn:H1;
  trivial.
Qed.

Lemma hT_remove_work : forall hT x v,
   not_in_domT x hT
-> hT_remove (x !ht-> v;hT) x = hT.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hT_remove.
  destruct (beq_nat x0 x) eqn:H1.
  - rewrite beq_eq in H1. subst. auto.
  - rewrite beq_neq in H1.
    rewrite hT_update_neq; auto.
Qed.

Lemma hV_remove_work : forall hV x v,
   not_in_domV x hV
-> hV_remove (x !hv-> v;hV) x = hV.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hV_remove.
  destruct (beq_nat x0 x) eqn:H1.
  - rewrite beq_eq in H1. subst. auto.
  - rewrite beq_neq in H1.
    rewrite hV_update_neq; auto.
Qed.


(*定义五元组*)
Definition state : Type := (storeV * storeT * storeS * heapV * heapT).

(*定义状态转换*)
Inductive ext_state : Type :=
|  St: state -> ext_state    (* normal state *)
| Fault: ext_state.            (* fault *)


