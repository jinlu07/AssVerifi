From AssVerifi Require Import util.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
From Coq Require Import Strings.String.
Import ListNotations.

(*******语法部分********)

(*算术表达式*)
Inductive aexp: Type :=
| ANum : nat -> aexp
| AId : id -> aexp    (* Var *)
| APlus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp.

(*布尔表达式*)
Inductive bexp: Type :=
| BTrue : bexp
| BFalse: bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
| BOr  : bexp -> bexp -> bexp.

(*DY转运车表达式*)
Inductive texp : Type :=
| TNull : texp
| TNum : nat -> texp
| TId  : id -> texp     (* TVar *)
| TAddr: id -> aexp -> texp.

(*决策方案表达式*)
Inductive sexp : Type :=
| SNull : sexp
| SFin : sexp
| SId : id -> sexp.


Inductive command: Type :=
| CSkip         : command
| CAss          : id -> aexp -> command
| CSeq          : command -> command -> command
| CIf           : bexp  -> command -> command -> command
| CWhile        : bexp -> command -> command
(*方案s*)
| CSasgn        : id -> texp -> command
| CSattach      : id -> texp -> command
| CSappend      : id -> id -> command
| CScomp        : id -> command
| CSlength      : id -> id -> command
(*DY转运车 t*)
| CTplan        : id -> aexp -> command
| CTadd         : texp -> aexp -> command
| CTlookup      : id -> texp -> aexp -> command
| CTlength      : id -> texp -> command
| CTreplace     : sexp -> aexp -> texp -> command
| CTexe         : texp -> command
| CTfree        : texp -> command.

Coercion ANum : nat >-> aexp.
Coercion AId : id >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Coercion TId : id >-> texp.
Coercion SId : id >-> sexp.
Bind Scope language_scope with aexp.
Bind Scope language_scope with bexp.
Bind Scope language_scope with texp.
Bind Scope language_scope with command.
Delimit Scope language_scope with language.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : language_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : language_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : language_scope.

Notation "x = y" := (BEq x y) (at level 70, no associativity) : language_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : language_scope.
Notation "~ b" := (BNot b) (at level 75, right associativity) : language_scope.
Notation "x /\ y" := (BAnd x y) (at level 80, right associativity) : language_scope.
Notation "x \/ y" := (BOr x y) (at level 85, right associativity) : language_scope.

Notation "x ` y" := (TAddr x y) (at level 75) : language_scope.

Notation " 'SKIP' " := CSkip : language_scope.
Notation "x ::= a" := (CAss x a) (at level 60) : language_scope.
Notation "c1 ;; c2" := 
  (CSeq c1 c2) (at level 80, right associativity) : language_scope.
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity) : language_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : language_scope.

Notation "x '::=asgn' y" := (CSasgn x y) (at level 80) : language_scope.
Notation "'att' ( x , y )" := (CSattach x y) (at level 80) : language_scope.
Notation "'app' ( x , y )" := (CSappend x y) (at level 80) : language_scope.
Notation "'comp' x" := (CScomp x) (at level 80) : language_scope.
Notation "x '::=#s' y" := (CSlength x y) (at level 80) : language_scope.

Notation "x '::=plan' y" := (CTplan x y) (at level 80) : language_scope.
Notation "x '::=add' y" := (CTadd x y) (at level 80) : language_scope.
Notation "x ::={ y , z }" := (CTlookup x y z) (at level 80) : language_scope.
Notation "x '::=#t' y" := (CTlength x y) (at level 80) : language_scope.
Notation "x '::=rep' y" := (CTreplace x y) (at level 80) : language_scope.
Notation "'stexe1' x" := (CTexe x) (at level 80) : language_scope.
Notation "'free' x" := (CTfree x) (at level 80) : language_scope.





