Require Export Coq.omega.Omega.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.Lists.List.
Require Export Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* export all bindings *)
From AssVerifi Require Export util.
From AssVerifi Require Export language.
From AssVerifi Require Export semantic.
From AssVerifi Require Export state.
Require Export Logic.
Require Import Coq.Strings.String.


(*Some variables*)
Definition i  : id := Id "i".
Definition j  : id := Id "j".
Definition x : id := Id "x".
Definition s1 : id := Id "s1".
Definition s2 : id := Id "s2".
Definition s3 : id := Id "s3".
Definition s4 : id := Id "s4".
Definition s5 : id := Id "s5".
Definition s6 : id := Id "s6".
Definition s7 : id := Id "s7".
Definition t1_A1 : id := Id "t1_A1".
Definition t1_A2 : id := Id "t1_A2".
Definition t1_A1' : id := Id "t1_A1'".
Definition t2_A1 : id := Id "t2_A1".
Definition len : id := Id "len".

(*The definition of empty state*)
Definition null_sV : storeV :=
  fun (n : id) => 0.

Definition null_sT : storeT :=
  fun (n : id) => 0.

Definition null_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (null_sV, null_sT, null_sS, emp_heapV, emp_heapT).

Open Scope language_scope.
Definition PROCESSEXE (s :id) (i :nat):=
  len ::=#t s`i;;
  j ::= len;; 
  WHILE (1 <= j) DO 
    stexe1 s`i;;
    j ::= j - 1
    END.
Close Scope language_scope.