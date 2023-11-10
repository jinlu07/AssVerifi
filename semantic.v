Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
From AssVerifi Require Import language.
From AssVerifi Require Import state.
From AssVerifi Require Import util.
Import ListNotations.

Fixpoint aeval (stoV: storeV) (a:aexp) : nat :=
match a with
| ANum n => n
| AId name => stoV name
| APlus a1 a2 => (aeval stoV a1) + (aeval stoV a2)
| AMult a1 a2 => (aeval stoV a1) * (aeval stoV a2)
| AMinus a1 a2 => (aeval stoV a1) - (aeval stoV a2)
end.


Fixpoint findt (li:list nat) (loc:nat): option nat :=
match li with
| [] => None
| x::xli => if (beq_nat loc 1) then Some x else (findt xli (loc-1))
end.

Fixpoint teval (stoV:storeV) (stoT:storeT) 
                (stoS:storeS) (t:texp) : option nat :=
match t with
| TNull => None
| TNum n => Some n
| TId name => Some (stoT name)
| TAddr sname a => findt (stoS sname) (aeval stoV a)
end.
 

Fixpoint beval stoV (b:bexp) : option bool :=
match b with
| BTrue   => Some true
| BFalse  => Some false
| BEq a1 a2 => Some (beq_nat (aeval stoV a1) (aeval stoV a2))
| BLe a1 a2 => Some (leb (aeval stoV a1) (aeval stoV a2))
| BNot b1   =>(match (beval stoV b1) with
               | None => None
               | Some x => Some (negb x)
               end)
| BAnd b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1,Some x2 => Some (andb x1 x2)
                 end)
| BOr  b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1, Some x2 => Some (orb x1 x2)
                 end)
end.


(* auxiliary function *)
(*可选类型的nat比较*)
Definition beq_op_nat (x y: option nat) : bool :=
match x,y with
| None,None => true
| Some n1,Some n2 => beq_nat n1 n2
| _,_ => false
end.

(*在list中找第i个数*)
Fixpoint nth_list (n:nat) (l:list nat) :option nat :=
match n,l with
| _, [] => None
| O,(h::t) => Some h
| S n,(h::t) => nth_list n t
end.

(*得到list中第1个数*)
Definition get_first (l:list nat) :option nat :=
match l with
| [] => None
| h::t => Some h
end.

(*在optioblist中找第i个数*)
Fixpoint nth_list_o (n:nat) (l:list (option nat)) :option nat :=
match n,l with
| _, (None::t) => None
| _, [] => None
| S O,(Some h::t) => Some h
| O, _ => None
| S n,(Some h::t) => nth_list_o n t
end.

(*改变list中的第i个数改为m*)
Fixpoint nth_update (i m:nat) (l:list nat) :list nat :=
match i,l with
| _, [] => []
| O, (h::t) => [m] ++ t
| S n,(h::t) => nth_update n m t
end.
(*firstn取列表前i个 返回改变后的list*)
Definition nth_list_update (i m:nat) (l:list nat) :list nat :=
let rest := firstn i l in 
 rest ++ nth_update i m l.

(* Definition sF_nth_update (s: storeF) (f:id) (i m:nat) : storeF :=
  fun x => if beq_id f x then (nth_list_update (i-1) m (s f))
           else s x. *)

Definition value_change (n:nat) :=
  fun m => if beq_nat m n then m else n.

(*将list中的全部改变*)
Fixpoint list_update (li:list nat) (n : nat) : list nat :=
  map (value_change n) li.

Fixpoint in_list_list (li:list nat) (x:nat) : bool :=
match li with
| [] => false
| t::xli => if beq_nat t x then true else in_list_list xli x
end.

(*在listoption中找是否有x*)
Fixpoint in_list (li:list (option nat)) (x:option nat) : bool :=
match li with
| [] => false
| t::xli => if beq_op_nat t x then true else in_list xli x
end.

(*把list的尾巴去掉*)
Fixpoint cuttail (li:list nat) : list nat :=
match li with
| [] => []
| [h] => []
| h :: t => h :: cuttail t
end.

(*将listoption的尾巴去掉 none*)
Fixpoint cuttail_o (li:list (option nat)) : list (option nat) :=
match li with
| [] => []
| [_] => []
| None :: t => []
| Some h :: t => Some h :: cuttail_o t
end.

(*将optionlist转为list*)
Definition get_content (nli:list (option nat)) : list nat :=
let f := fun t => match t with
                 | Some n => n
                 | None => 0
                 end
in (map f nli).

Definition o2v (m:option nat) : nat :=
  match m with
  | Some n => n
  | None => 0
  end.

Definition v2o (m:nat) : option nat :=
  Some m.


(*判断listoption是否为空或全为none*)
Fixpoint all_none (opli:list (option nat)) : bool :=
match opli with
| [] => true
| x::li => if beq_op_nat x None then all_none li
           else false
end.

(*将listoption改为listlistoption ht*)
Fixpoint h_unionT_many (hT:heapT) (locli :list (option nat)) (nli : list (list (option nat))) : heapT :=
match locli,nli with
| bloc::blocs,l::ls => h_unionT_many (hT_update hT (o2v bloc) l) blocs ls
| [],[] => hT
| _,_ => hT
end.

(* Lemma nth_update_neq :forall sF f1 f2 v i n,
   f1 <> f2
-> sF_nth_update (f2 !sf-> v ; sF) f1 i n = 
  (f2 !sf-> v;(sF_nth_update sF f1 i n)).
Proof.
Admitted. *)

Definition BlockSafe stoV stoT stoS (hv:heapV) (hT:heapT) t bl llist: Prop :=  
    (teval stoV stoT stoS t) = Some bl ->
    hT bl = Some llist ->
    forall l, in_list llist l = true ->
              exists k, hv (o2v l) = Some k.

Fixpoint sS_remove_wei (l:list nat) (m:nat) : list nat:=
match l with
| nil => nil
| x::ll => if (beq_nat m x) then ll else sS_remove_wei ll m
end.

Definition list_o_remove_one (l:list (option nat)) :list (option nat):=
match l with
| nil =>nil
| x::h => h
end.

Inductive ceval: command -> state -> ext_state -> Prop :=
(**旧指令集**)
| E_Skip  : forall stat,
              ceval CSkip stat (St stat)

| E_Ass   : forall stoV stoT stoS hV hT x a n, (aeval stoV a) = n ->
              ceval (CAss x a) (stoV,stoT,stoS,hV,hT)
                       (St ((x !sv-> n; stoV),stoT,stoS,hV,hT))

| E_Seq   : forall c1 c2 st0 st1 opst,
              ceval c1 st0 (St st1) ->
              ceval c2 st1 opst ->
              ceval (CSeq c1 c2) st0 opst
| E_Seq_Fault: forall c1 c2 st0,
               ceval c1 st0 Fault ->
               ceval (CSeq c1 c2) st0 Fault
| E_IfTure: forall stoV stoT stoS hV hT opst b c1 c2,
              beval stoV b = Some true ->
              ceval c1 (stoV,stoT,stoS,hV,hT) opst ->
              ceval (CIf b c1 c2) (stoV,stoT,stoS,hV,hT) opst
| E_IfFalse: forall stoV stoT stoS hV hT opst b c1 c2,
              beval stoV b = Some false ->
              ceval c2 (stoV,stoT,stoS,hV,hT) opst ->
              ceval (CIf b c1 c2) (stoV,stoT,stoS,hV,hT) opst
| E_If_Fault : forall stoV stoT stoS hV hT b c1 c2,
              beval stoV b = None ->
              ceval (CIf b c1 c2) (stoV,stoT,stoS,hV,hT) Fault


| E_WhileEnd : forall b stoV stoT stoS hV hT c,
                 beval stoV b = Some false ->
                 ceval (CWhile b c) (stoV,stoT,stoS,hV,hT) (St (stoV,stoT,stoS,hV,hT))

| E_WhileLoop : forall stoV stoT stoS hV hT opst b c st,
                  beval stoV b = Some true ->
                  ceval c (stoV,stoT,stoS,hV,hT) (St st) ->
                  ceval (CWhile b c) st opst ->
                  ceval (CWhile b c) (stoV,stoT,stoS,hV,hT) opst
| E_WhileLoop_Fault : forall stoV stoT stoS hV hT b c,
                      beval stoV b = Some true ->
                      ceval c (stoV,stoT,stoS,hV,hT) Fault ->
                      ceval (CWhile b c) (stoV,stoT,stoS,hV,hT) Fault
| E_While_Fault :  forall stoV stoT stoS hV hT b c,
                   beval stoV b = None ->
                   ceval (CWhile b c) (stoV,stoT,stoS,hV,hT) Fault

(**新指令集**)
(*决策方案指令 *)
| E_Sasgn : forall stoV stoT stoS hV hT s t tloc,
                teval stoV stoT stoS t = Some tloc ->                    (*地址*)
                 ceval (CSasgn s t) (stoV,stoT,stoS,hV,hT)
                          (St (stoV,stoT,(s !ss-> [tloc]; stoS),hV,hT))

| E_Sasgn_Fault : forall stoV stoT stoS hV hT s t,
                 teval stoV stoT stoS t = None ->
                 ceval (CSasgn s t) (stoV,stoT,stoS,hV,hT) Fault

| E_Sattach : forall stoV stoT stoS hV hT s t sss tloc,
                        teval stoV stoT stoS t = Some tloc ->            (*se.te*)
                        sss = stoS s ->
                        (forall l, in_list_list sss l = true -> exists k, hT l = k) ->
                        ceval (CSattach s t) (stoV,stoT,stoS,hV,hT)
                                 (St (stoV,stoT,(s !ss-> (sss ++ [tloc]); stoS),hV,hT))

| E_Sattach_FaultT : forall stoV stoT stoS hV hT s t,
                          teval stoV stoT stoS t = None ->
                          ceval (CSattach s t) (stoV,stoT,stoS,hV,hT) Fault

| E_Sattach_FaultHt : forall stoV stoT stoS hV hT s t sss,
                          sss = stoS s ->
                          (exists l, in_list_list sss l = true -> hT l = None) ->
                          ceval (CSattach s t) (stoV,stoT,stoS,hV,hT) Fault

| E_Sappend : forall stoV stoT stoS hV hT s s1 sss sss1,
                        sss = stoS s ->
                        sss1 = stoS s1 ->                       (*se.se1*)
                        ceval (CSappend s s1) (stoV,stoT,stoS,hV,hT)
                                 (St (stoV,stoT,(s !ss-> (sss ++ sss1); stoS),hV,hT))

| E_Scomp : forall stoV stoT stoS hV hT s,
                nil = stoS s ->
                ceval (CScomp s) (stoV,stoT,stoS,hV,hT)
                         (St (stoV,stoT,(s !ss-> [fin];stoS),hV,hT))

| E_Scomp_Fault : forall stoV stoT stoS hV hT s sss,
                sss = stoS s ->
                ceval (CScomp s) (stoV,stoT,stoS,hV,hT) Fault

| E_Slength : forall stoV stoT stoS hV hT s sss m x,
              stoS s = sss ->
              length sss = m ->
              ceval (CSlength x s) (stoV,stoT,stoS,hV,hT)
                    (St ((x !sv-> m;stoV),stoT,stoS,hV,hT))

(*DY转运车指令*)
| E_Tplan : forall stoV stoT stoS hV hT t e n tloc loc,
              aeval stoV e = n ->
              hV loc = None ->
              hT tloc = None ->
              ceval (CTplan t e) (stoV,stoT,stoS,hV,hT)
                    (St (stoV, (t !st-> tloc; stoT), stoS,
                      (loc !hv-> n;hV), (tloc !ht-> [v2o loc];hT)))


| E_Tadd : forall stoV stoT stoS hV hT t e n loc tloc llist,
              (teval stoV stoT stoS t) = Some tloc ->
              hT tloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              aeval stoV e = n ->
              hV loc = None ->
              ceval (CTadd t e) (stoV,stoT,stoS,hV,hT)
             (St (stoV, stoT, stoS, (loc !hv-> n;hV), (tloc !ht-> llist ++ [(v2o loc)];hT)))

| E_Tadd_FaultT : forall stoV stoT stoS hV hT t e,
              (teval stoV stoT stoS t) = None ->
              ceval (CTadd t e) (stoV,stoT,stoS,hV,hT) Fault

| E_Tadd_FaultHp : forall stoV stoT stoS hV hT t e tloc llist,
              (teval stoV stoT stoS t) = Some tloc ->
              hT tloc = Some llist ->
              (exists l, in_list llist l = true -> hV (o2v l) = None) ->
              ceval (CTadd t e) (stoV,stoT,stoS,hV,hT) Fault

| E_Tlookup : forall stoV stoT stoS hV hT t tloc loc llist e x m j,
              (teval stoV stoT stoS t) = Some tloc ->
              hT tloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              aeval stoV e = j ->
              nth_list_o j llist = Some loc ->
              hV loc = Some m ->
                ceval (CTlookup x t e) (stoV,stoT,stoS,hV,hT)
                         (St ((x !sv-> m;stoV),stoT,stoS,hV,hT))

| E_Tlookup_FaultT : forall stoV stoT stoS hV hT x t e,
                      (teval stoV stoT stoS t) = None ->
                      ceval (CTlookup x t e) (stoV,stoT,stoS,hV,hT) Fault

| E_Tlookup_FaultHp : forall stoV stoT stoS hV hT x t n e llist,
                      (teval stoV stoT stoS t) = Some n ->
                      hT n = Some llist ->
                      (exists l, in_list llist l = true -> hV (o2v l) = None) ->
                      ceval (CTlookup x t e) (stoV,stoT,stoS,hV,hT) Fault

| E_Tlength : forall stoV stoT stoS hV hT t x tloc llist m,
              (teval stoV stoT stoS t) = Some tloc ->
              hT tloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
              length llist = m ->
              ceval (CTlength x t) (stoV,stoT,stoS,hV,hT)
                    (St ((x !sv-> m; stoV),stoT,stoS,hV,hT))


| E_Treplace : forall stoV stoT stoS hV hT t tloc llist s sss e i,
              (teval stoV stoT stoS t) = Some tloc ->
              hT tloc = Some llist ->
              sss = stoS s ->
              (forall l, in_list_list sss l = true -> exists k, hT l = k) ->
              (aeval stoV e) = i ->
              ceval (CTreplace (SId s) e t) (stoV,stoT,stoS,hV,hT)
                         (St (stoV,stoT,(s !ss-> nth_list_update i tloc sss ;stoS),hV,hT))

| E_Treplace_FaultT : forall stoV stoT stoS hV hT t s e,
                    (teval stoV stoT stoS t) = None ->
                     ceval (CTreplace (SId s) e t) (stoV,stoT,stoS,hV,hT) Fault

| E_Treplace_FaultHt : forall stoV stoT stoS hV hT t s e sss,
                       sss = stoS s ->
                       (exists l, in_list_list sss l = true -> hT l = None) ->
                       ceval (CTreplace (SId s) e t) (stoV,stoT,stoS,hV,hT) Fault

| E_Texe : forall stoV stoT stoS hV hT lt t llist list h s sss,
                 teval stoV stoT stoS t = Some lt ->
                 hT lt = Some llist ->
                 (forall l, in_list llist l = true -> exists k, hV (o2v l) = k) ->
                 sss = stoS s ->
                 (forall l, in_list_list sss l = true -> exists k, hT l = k) ->
                 get_first (get_content llist) = Some h ->
                 list_o_remove_one llist = list ->
                 ceval
                 (CTexe t) (stoV,stoT,stoS,hV,hT)
                 (St (stoV,stoT,stoS,
                 (hV_remove hV h),(hT_update hT lt list)))

| E_Texe_FaultT : forall stoV stoT stoS hV hT t,
                 (teval stoV stoT stoS t)= None ->
                 ceval (CTexe t) (stoV,stoT,stoS,hV,hT) Fault

| E_Texe_FaultHt : forall stoV stoT stoS hV hT lt t,
                 teval stoV stoT stoS t = Some lt ->
                 hT lt = None ->
                 ceval (CTexe t) (stoV,stoT,stoS,hV,hT) Fault

| E_Texe_FaultHv : forall stoV stoT stoS hV hT lt t llist,
                 teval stoV stoT stoS t = Some lt ->
                 hT lt = Some llist ->
                 (exists l, in_list llist l = true -> hV (o2v l) = None) ->
                 ceval
                 (CTexe t) (stoV,stoT,stoS,hV,hT) Fault

| E_Tfree : forall stoV stoT stoS hV hT lt t llist s sss,
            sss = stoS s ->
            (forall l, in_list_list sss l = true -> exists k, hT l = k) ->
            teval stoV stoT stoS t = Some lt ->
            hT lt = Some llist ->
            nil = llist ->
            ceval (CTfree t) (stoV,stoT,stoS,hV,hT)
            (St (stoV,stoT,(s !ss-> rev(sS_remove_wei (rev sss) lt)++ sS_remove_wei sss lt;stoS),
            hV,(hT_remove hT lt)))

| E_Tfree_FaultHt : forall stoV stoT stoS hV hT t s sss,
                  sss = stoS s ->
                  (exists l, in_list_list sss l = true -> hT l = None) ->
                  ceval (CTfree t) (stoV,stoT,stoS,hV,hT) Fault

| E_Tfree_FaultT : forall stoV stoT stoS hV hT lt t llist,
                   teval stoV stoT stoS t = Some lt ->
                   hT lt = Some llist ->
                   nil <> llist ->
                   ceval (CTfree t) (stoV,stoT,stoS,hV,hT) Fault.


Notation "st '=[' c ']=>' st'" := (ceval c st st') 
                                  (at level 40).