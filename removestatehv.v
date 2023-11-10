From AssVerifi Require Import util Aid state.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma hV_remove_work1 : forall hV x1 x2 x3 v1 v2 v3,
   not_in_domV x1 hV -> x1<>x2 -> x1<>x3 -> x2<>x3
-> hV_remove (x3 !hv-> v3; x2 !hv-> v2; x1 !hv-> v1;hV) x1 = (x3!hv->v3;x2!hv->v2;hV).
Proof.
  intros.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_work.
  reflexivity. auto. auto. auto.
Qed.

Lemma hV_remove_work2 : forall hV x1 x2 v1 v2,
   not_in_domV x1 hV -> x1<>x2
-> hV_remove (x2 !hv-> v2; x1 !hv-> v1;hV) x1 = (x2!hv->v2;hV).
Proof.
  intros.
  rewrite hV_remove_neq.
  rewrite hV_remove_work.
  reflexivity. auto. auto.
Qed.

Lemma hV_remove_work3 : forall hV x1 x2 x3 x4 x5 v1 v2 v3 v4 v5,
not_in_domV x1 hV -> 
x1 <> x2 -> x1<>x3 -> x1<>x4 -> x1<>x5 ->
x2<>x3 -> x2<>x4 -> x2<>x5 -> x3<>x4 -> x3<>x5 -> x4<>x5
-> hV_remove (x5 !hv-> v5;x4 !hv-> v4;x3 !hv-> v3;x2 !hv-> v2; x1 !hv-> v1;hV) x1 = 
(x5 !hv-> v5;x4 !hv-> v4;x3 !hv-> v3;x2!hv->v2;hV).
Proof.
  intros.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_work.
  reflexivity. auto. auto. auto. auto. auto.
Qed.

Lemma hV_remove_work4 : forall hV x1 x2 x3 x4 v1 v2 v3 v4,
not_in_domV x1 hV -> 
x1 <> x2 -> x1<>x3 -> x1<>x4 -> x2<>x3 -> x2<>x4 -> x3<>x4
-> hV_remove (x4 !hv-> v4;x3 !hv-> v3;x2 !hv-> v2; x1 !hv-> v1;hV) x1 = 
(x4 !hv-> v4;x3 !hv-> v3;x2!hv->v2;hV).
Proof.
  intros.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_neq.
  rewrite hV_remove_work.
  reflexivity. auto. auto. auto. auto.
Qed.



