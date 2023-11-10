Require Export Coq.omega.Omega.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Logic.

From AssVerifi Require Export util.

Definition neq0_tt3 (n1 n2 n3 : nat) :=
 n1 <> 0 /\ n2 <> 0 /\ n3 <> 0.

Definition neq0_tt4 (n1 n2 n3 n4 : nat) :=
 n1 <> 0 /\ n2 <> 0 /\ n3 <> 0 /\ n4 <> 0.

Definition neq0_loc8 (n1 n2 n3 n4 n5 n6 n7 n8 : nat) :=
 n1 <> 0 /\ n2 <> 0 /\ n3 <> 0 /\ n4 <> 0 /\ n5 <> 0 /\ n6 <> 0 /\ n7 <> 0 /\ n8 <> 0.

Definition neq0_loc9 (n1 n2 n3 n4 n5 n6 n7 n8 n9 :nat) :=
 n1 <> 0 /\ n2 <> 0 /\ n3 <> 0 /\ n4 <> 0 /\ n5 <> 0 /\ n6 <> 0 /\ n7 <> 0 /\ n8 <> 0 /\
 n9 <> 0.

Definition neq0_loc10 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 :nat) :=
 n1 <> 0 /\ n2 <> 0 /\ n3 <> 0 /\ n4 <> 0 /\ n5 <> 0 /\ n6 <> 0 /\ n7 <> 0 /\ n8 <> 0 /\
 n9 <> 0 /\ n10 <> 0.

Definition neq_t3 (n1 n2 n3 : id) :=
 n1<>n2 /\ n1<>n3 /\ n2<>n3.

Definition neq_t4 (n1 n2 n3 n4 : id) :=
 n1<>n2 /\ n1<>n3 /\ n1<>n4 /\ 
 n2<>n3 /\ n2<>n4 /\ n3<>n4.

Definition neq_tt3 (n1 n2 n3 : nat) :=
 n1<>n2 /\ n1<> n3 /\ n2<>n3.

Definition neq_tt4 (n1 n2 n3 n4 : nat) :=
 n1<>n2 /\ n1<>n3 /\ n1<>n4 /\ 
 n2<>n3 /\ n2<>n4 /\ n3<>n4.

Definition neq_loc8 (n1 n2 n3 n4 n5 n6 n7 n8 : nat):=
 n1<>n2 /\ n1<>n3 /\ n1<>n4 /\ n1<>n5 /\ n1<>n6 /\ n1<>n7 /\ n1<>n8 /\
 n2<>n3 /\ n2<>n4 /\ n2<>n5 /\ n2<>n6 /\ n2<>n7 /\ n2<>n8 /\
 n3<>n4 /\ n3<>n5 /\ n3<>n6 /\ n3<>n7 /\ n3<>n8 /\
 n4<>n5 /\ n4<>n6 /\ n4<>n7 /\ n4<>n8 /\
 n5<>n6 /\ n5<>n7 /\ n5<>n8 /\
 n6<>n7 /\ n6<>n8 /\
 n7<>n8.

Definition neq_loc9 (n1 n2 n3 n4 n5 n6 n7 n8 n9 :nat) :=
 n1<>n2 /\ n1<>n3 /\ n1<>n4 /\ n1<>n5 /\ n1<>n6 /\ n1<>n7 /\ n1<>n8 /\ n1<>n9 /\ 
 n2<>n3 /\ n2<>n4 /\ n2<>n5 /\ n2<>n6 /\ n2<>n7 /\ n2<>n8 /\ n2<>n9 /\ 
 n3<>n4 /\ n3<>n5 /\ n3<>n6 /\ n3<>n7 /\ n3<>n8 /\ n3<>n9 /\ 
 n4<>n5 /\ n4<>n6 /\ n4<>n7 /\ n4<>n8 /\ n4<>n9 /\ 
 n5<>n6 /\ n5<>n7 /\ n5<>n8 /\ n5<>n9 /\ 
 n6<>n7 /\ n6<>n8 /\ n6<>n9 /\ 
 n7<>n8 /\ n7<>n9 /\ 
 n8<>n9.

Definition neq_loc10 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 :nat):=
 n1<>n2 /\ n1<>n3 /\ n1<>n4 /\ n1<>n5 /\ n1<>n6 /\ n1<>n7 /\ n1<>n8 /\ n1<>n9 /\ n1<>n10 /\
 n2<>n3 /\ n2<>n4 /\ n2<>n5 /\ n2<>n6 /\ n2<>n7 /\ n2<>n8 /\ n2<>n9 /\ n2<>n10 /\
 n3<>n4 /\ n3<>n5 /\ n3<>n6 /\ n3<>n7 /\ n3<>n8 /\ n3<>n9 /\ n3<>n10 /\
 n4<>n5 /\ n4<>n6 /\ n4<>n7 /\ n4<>n8 /\ n4<>n9 /\ n4<>n10 /\
 n5<>n6 /\ n5<>n7 /\ n5<>n8 /\ n5<>n9 /\ n5<>n10 /\
 n6<>n7 /\ n6<>n8 /\ n6<>n9 /\ n6<>n10 /\
 n7<>n8 /\ n7<>n9 /\ n7<>n10 /\
 n8<>n9 /\ n8<>n10 /\
 n9<>n10.




