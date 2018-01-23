Require Import Relation_Definitions.
Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.

Require Import Coq.Classes.Morphisms.

Require Import VCC.Tactics.
Require Import VCC.Freshvars.
Require Import VCC.Basics.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import Coq.Logic.Classical_Prop.

Notation heap:=(@ heap val).


(** *Operations*)

(*Binary operations*)
Inductive binary_operation : Type :=
  | Oadd : binary_operation             (** addition (binary [+]) *)
  | Osub : binary_operation             (** subtraction (binary [-]) *)
  | Omul : binary_operation             (** multiplication (binary [*]) *)
  | Odiv : binary_operation             (** division ([/]) *)
  | Omod : binary_operation             (** remainder ([%]) *)
  | Oand : binary_operation             (** bitwise and ([&]) *)
  | Oor : binary_operation              (** bitwise or ([|]) *)
  | Oxor : binary_operation             (** bitwise xor ([|]) *)
  | Oeq: binary_operation               (** comparison ([==]) *)
  | One: binary_operation               (** comparison ([!=]) *)
  | Olt: binary_operation               (** comparison ([<]) *)
  | Ogt: binary_operation               (** comparison ([>]) *)
  | Ole: binary_operation               (** comparison ([<=]) *)
  | Oge: binary_operation.              (** comparison ([>=]) *)


(*
Definition sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2)
*)

(** * Expressions *)
Inductive expr : Type :=
  | Econst_int ( i: int) (ty: type) (* integer constant*)
  | Etempvar (id: ident) (ty: type)  (**r constant *)
  | Ederef (ex:expr) (ty: type)       (* pointer dereference (unary * ) *)
  | Ebinop  (bo:binary_operation) (ex1:expr) (ex2:expr) (ty: type)  (* binary operations *).

Definition type_of_expr (ex:expr):=
  match ex with
  | Econst_int _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Ebinop _ _ _ ty => ty
  end.

Notation expr_zero:= (Econst_int Int.zero Tint).

(*Ghost expressions*)
Inductive gexpr : Type :=
  | Rexpr (ex: expr)
  | GEconst_ptr ( adr: address) (ty: type)
  | GEconst_nat ( n: nat) (ty: type) 
  | GEconst_bool (b: bool) (ty: type) 
  | GEtempvar (id: ident) (ty: type)  (**r constant *)
  | GEderef (ex:gexpr) (ty: type)        (* pointer dereference (unary * ) *)
  | GEbinop  (bo:binary_operation) (ex1:gexpr) (ex2:gexpr) (ty: type).

Definition type_of_gexpr (ex:gexpr):=
  match ex with
  | Rexpr ex => type_of_expr ex
  | GEconst_ptr _ ty => ty
  | GEconst_nat _ ty => ty
  | GEconst_bool _ ty => ty
  | GEtempvar _ ty => ty
  | GEderef _ ty => ty
  | GEbinop _ _ _ ty => ty
  end.
Coercion Rexpr: expr >-> gexpr.

(*Free GHOST variables of a GHOST expression*)
(* Very important to notice that program variables don't count.*)
(* the reason is that this is used by the verifier to get FRESH vars.*)
(* The verifier can only create ghost variables. *)
Fixpoint free_vars_expr (e:gexpr): PositiveSet.t:=
  match e with
  | GEtempvar id _ => singleton id
  | GEderef ex _ => free_vars_expr ex
  | GEbinop _ ex1 ex2 _ => union (free_vars_expr ex1) (free_vars_expr ex2)
  | _ => empty
  end.
  
Inductive deref_loc (h: heap) (adr: block * ptrofs) : val -> Prop :=
  | deref_loc_value: forall v,
      h adr = Some v ->
      deref_loc h adr v.

(** * Evaluating binarry expressions  *)

Definition bool2int (b:bool):=
  match b with
    false => Int.zero
  | true => Int.one
  end.

Definition eval_int_binop (op:binary_operation) (a:int)(b:int): option val:=
  Some (Vint
          match op with
       | Oadd => (Int.add a b)
       | Osub => (Int.sub a b) 
       | Omul => (Int.mul a b) 
       | Odiv => (Int.divs a b) 
       | Omod => (Int.mods a b) 
       | Oand => (Int.and a b) 
       | Oor => (Int.or a b)
       | Oxor => (Int.xor a b)
       | Oeq => (bool2int (Int.eq a b))
       | One => (bool2int (negb (Int.eq a b)))
       | Olt => (bool2int (Int.lt a b))
       | Ole => (bool2int (negb (Int.lt b a)))
       | Ogt => (bool2int (Int.lt b a))
       | Oge => (bool2int (negb (Int.lt a b)))
          end).

Definition eval_nat_binop (op:binary_operation) (a:nat)(b:nat): option gval:=
  (match op with
   | Oadd => Some (GVnat (a + b))
   | Osub => Some (GVnat (a - b))
   | Omul => Some (GVnat (a * b))
   | Odiv => Some (GVnat (a/b) )
   | Omod => Some (GVnat (Nat.modulo a b))
   | Oeq => Some (GVbool (Nat.eqb a b))
   | One => Some (GVbool (negb (Nat.eqb a b)))
   | Olt => Some (GVbool (Nat.ltb a b))
   | Ole => Some (GVbool (negb (Nat.ltb b a)))
   | Ogt => Some (GVbool (Nat.ltb b a))
   | Oge => Some (GVbool (negb (Nat.ltb a b)))
   | _ => None
   end)%nat.

Definition eval_bool_binop (op:binary_operation) (a:bool)(b:bool): option bool:=
  match op with
  | Oand => Some (a && b) 
  | Oor => Some (a || b)
  | Oxor => Some (xorb a b)
  | _ => None
  end.


Definition eval_ptr_int_binop (ty:type)(op:binary_operation) (p:positive*int)(a:int):
  option (positive*int):=
  let (b1,ofs1):= p in
  match op with
  | Oadd =>
    Some (b1,Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) a))
  | Osub =>
    Some (b1,Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) a))
  | _ => None
  end.

Definition eq_block := peq.
Definition valid_ptr (h:Basics.heap) b ofs: bool :=
  match h (b,ofs) with
  | None => false
  | Some _ => true
  end.

Definition eval_ptr_ptr_binop (m:Basics.heap)(op:binary_operation) (p1 p2:positive*int):
  option bool:=
  let (b1,ofs1):= p1 in
  let (b2,ofs2):= p2 in
  match op with
  | Oeq =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some (Int.eq ofs1 ofs2)
      else Some false
    else None 
  | One =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some (negb (Int.eq ofs1 ofs2))
      else Some true
    else None 
  | Olt =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some  (Int.lt ofs1 ofs2)
      else None
    else None 
  | Ogt =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some (negb (Int.lt ofs1 ofs2))
      else None
    else None
  | Ole =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some (negb (Int.lt ofs2 ofs1))
      else None
    else None  
  | Oge =>
    if (valid_ptr m b1 ofs1 &&
        valid_ptr m b2 ofs2) then
      if eq_block b1 b2 then
        Some (Int.lt ofs2 ofs1)
      else None
    else None 
  | _ => None
  end. 

Definition eval_binop (h:heap) (ty:type) (op:binary_operation) (v1:val)(v2:val): option val:=
  match v1, v2 with
  | Vint n1, Vint n2 =>
    eval_int_binop op n1 n2
  | Vptr p, Vint n =>
    option_map Vptr
    (eval_ptr_int_binop ty op p n)
  | Vptr p1, Vptr p2 =>
    option_map (fun x => Vint (bool2int x))
    (eval_ptr_ptr_binop h op p1 p2)
  | _, _ => None 
  end.

(*pure ghost binary operations*)
Definition eval_gbinop (h:heap) (ty:type) (op:binary_operation)(v1:gval)(v2:gval): option gval:=
  match v1, v2 with
  | GVptr p1, GVptr p2 =>
    option_map GVbool
               (eval_ptr_ptr_binop h op p1 p2)
  | GVnat n1, GVnat n2 =>
    eval_nat_binop op n1 n2
  | GVbool b1, GVbool b2 =>
    option_map GVbool
      (eval_bool_binop op b1 b2)
  | _, _ => None 
  end.

Definition eval_ubinop (h:heap) (ty:type) (op:binary_operation)(v1:uval)(v2:uval): option uval:=
  match v1, v2 with
  | RV rv1, RV rv2 =>
    option_map RV
    (eval_binop h ty op rv1 rv2)
  | GV gv1, GV gv2 =>
    option_map GV
    (eval_gbinop h ty op gv1 gv2) 
  | GV (GVptr p), RV (Vint n) =>
    option_map (fun x => GV (GVptr x))
               (eval_ptr_int_binop ty op p n)
  | _,_=> None
  end.

(** * Evaluating expression  *)

(* Inductive eval_ubinop:  binary_operation -> uval -> uval -> uval -> Prop:=
| eval_Rbinop: forall op v1 v2 v,
    eval_binop op v1 v2 v ->
    eval_ubinop op v1 v2 v
| eval_Gbinop: forall op v1 v2 v,
    eval_gbinop op v1 v2 v ->
    eval_ubinop op v1 v2 v. *)

Fixpoint val_type (h:heap)(v:val)(ty:type):Prop:=
  match v, ty with
  | Vptr p, Tpointer ty' =>
    match ty', (h p) with
      _, Some v' => val_type h v' ty'
    | Tvoid, _ => True 
    | _, None => False
    end 
  | Vint _, Tint => True
  | _, _ => False
  end. 

    
Inductive eval_expr' (e:renv)(h:heap): expr -> val -> Prop :=
  | eval_Econst_int: forall i ty,
      eval_expr' e h (Econst_int i ty) (Vint i)
  | eval_Etempvar: forall id v ty,
      find e id = Some v ->
      eval_expr' e h (Etempvar id ty) v
  | eval_Ebinop: forall op ex1 ex2 v1 v2 v ty,
      eval_expr' e h ex1 v1 ->
      eval_expr' e h ex2 v2 ->
      eval_binop h (type_of_expr ex1) op v1 v2 = Some v ->
      eval_expr' e h (Ebinop op ex1 ex2 ty) v
  | eval_Elvalue: forall a adr v,
      eval_lvalue' e h a adr ->
      deref_loc h adr v ->
      eval_expr' e h a v
with eval_lvalue' (e:renv) (h:heap): expr -> (block* ptrofs) -> Prop :=
  | eval_Ederef: forall a adr ty,
      eval_expr' e h a (Vptr adr) ->
      eval_lvalue' e h (Ederef a ty) adr.

Definition eval_expr ex (e:renv)(h:heap):= eval_expr' e h ex.
Definition eval_lvalue ex (e:renv)(h:heap):= eval_lvalue' e h ex.

Definition env_equiv_gexpr ex : relation genv:=
  fun e1 e2 =>
    forall x, PSet.In x (free_vars_expr ex) ->
         (find e1 x) = (find e2 x).

Global Instance Equivalenc_env_equiv_expr: forall ex, Equivalence (env_equiv_gexpr ex).
Proof.
  constructor.
  - constructor.
  - intros ? ? H ? ?. rewrite H; auto.
  - intros ??? H1 H2 ??. rewrite H1, <- H2; auto.
Qed.

Lemma env_equiv_expr_equiv:
  forall ex e1 e2,
    env_equiv e1 e2 ->
    env_equiv_gexpr ex e1 e2.
Proof. intros ? ? ? H ? ?; apply H. Qed.

Inductive eval_gexpr' (e:renv)(h:heap)(ghe:genv):
  gexpr -> uval -> Prop :=
| geval_Rexpr: forall v ex,
    eval_expr ex e h v ->
    eval_gexpr' e h ghe (Rexpr ex) (RV v)
| geval_ptr: forall p ty,
    eval_gexpr' e h ghe (GEconst_ptr p ty) (RV (Vptr p))
| geval_nat: forall n ty,
    eval_gexpr' e h ghe (GEconst_nat n ty) (GV (GVnat n))
| geval_bool: forall b ty,
    eval_gexpr' e h ghe (GEconst_bool b ty) (GV (GVbool b))
| geval_GEtempvar: forall id v ty,
    find ghe id = Some v ->
    eval_gexpr' e h ghe (GEtempvar id ty) v
| geval_GEbinop: forall op ex1 ex2 v1 v2 v ty,
      eval_gexpr' e h ghe ex1 v1 ->
      eval_gexpr' e h ghe ex2 v2 ->
      eval_ubinop h ty op v1 v2 = Some v ->
      eval_gexpr' e h ghe (GEbinop op ex1 ex2 ty) v
| eval_GElvalue: forall a adr v,
    eval_glvalue' e h ghe a adr ->
    deref_loc h adr v ->
      eval_gexpr' e h ghe a (RV v)
with eval_glvalue' (e:renv)(h:heap)(ghe:genv): gexpr -> (block* ptrofs) -> Prop :=
  | eval_GEderef: forall a adr ty,
      eval_gexpr' e h ghe a (RV (Vptr adr)) ->
      eval_glvalue' e h ghe  (GEderef a ty) adr
  | eval_G_Ederef: forall (a:expr) adr ty,
      eval_expr' e h a (Vptr adr) ->
      eval_glvalue' e h ghe (Ederef a ty) adr.

Definition eval_gexpr ex (e:renv)(h:heap)(ghe:genv):= eval_gexpr' e h ghe ex.
Definition eval_glvalue ex (e:renv)(h:heap)(ghe:genv):= eval_glvalue' e h ghe ex.
        
Global Instance Equivalenc_env_equiv_gexpr: forall ex, Equivalence (env_equiv_gexpr ex).
Proof.
  constructor.
  - constructor.
  - intros ? ? H ? ?. rewrite H; auto.
  - intros ??? H1 H2 ??. rewrite H1, <- H2; auto.
Qed.

Lemma env_equiv_gexpr_equiv:
  forall ex e1 e2,
    env_equiv e1 e2 ->
    env_equiv_gexpr ex e1 e2.
Proof. intros ? ? ? H ? ?; apply H. Qed.


Lemma free_vars_env_equiv:
  forall ex k e,
    ~ PSet.In k (free_vars_expr ex) ->
      forall ov,
        env_equiv_gexpr ex (update_env e k ov) e.
Proof.
  induction ex; intros ? ? ? ? ? ?;
  destruct (peq k x); subst;
    try tauto;
    rewrite gso; auto.
Qed.


Ltac fold_eval_expr:=
  match goal with
    | [  |- context[eval_expr' ?e ?h ?ex ?v] ] =>
      progress replace (eval_expr' e h ex v) with (eval_expr ex e h v)
        by reflexivity
    | [  |- context[eval_lvalue' ?e ?h ?ex ?b ?ofs] ] =>
      progress replace (eval_lvalue' e h ex b ofs) with (eval_lvalue ex e h b ofs)
        by reflexivity
    | [  H: context[eval_expr' ?e ?h ?ex ?v]|- _ ] =>
      progress replace (eval_expr' e h ex v) with (eval_expr ex e h v) in H
        by reflexivity
    | [ H: context[eval_lvalue' ?e ?h ?ex ?b ?ofs]  |-  _ ] =>
      progress replace (eval_lvalue' e h ex b ofs) with (eval_lvalue ex e h b ofs) in H
                                                        by reflexivity
    end.
Ltac destruct_eval_expr:=
  repeat (match goal with
         | [ H: eval_expr _ _ _ _ |- _ ] =>
           unfold eval_expr in H; invert H; clear H
         end; try match goal with
                  | [ H: eval_lvalue' _ _ _ _ |- _ ] =>
                    invert H; clear H
                  end);
repeat fold_eval_expr.



Global Instance Proper_eval_expr:
  Proper ( Logic.eq ==> env_equiv ==> Logic.eq  ==> Logic.eq ==> Logic.iff) (eval_expr).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  repeat match goal with
  | [ e: env |- _ ] => revert e
  | [ h: heap |- _ ] => revert h
  | [ v: val |- _ ] => revert v
  end.
  induction y; intros; split; intros; destruct_eval_expr;
    try solve[econstructor; auto];
    try solve[econstructor; auto; rewrite H0 in *; auto].
  
    (*Ederef*)
  - do 2 econstructor.
    eapply IHy; eauto.
    inversion H1; subst; eauto.
  - do 2 econstructor.
    eapply IHy; eauto.
    inversion H1; subst; eauto.
    
    (*Binop*)
  - econstructor; eauto;
    fold_eval_expr;
    first [eapply IHy1| eapply IHy2]; auto.
  - econstructor; eauto;
    fold_eval_expr;
    first [eapply IHy1| eapply IHy2]; auto.
Qed.


Ltac fold_eval_gexpr:=
  match goal with
    | [  |- context[eval_gexpr' ?e ?h ?ghe ?ex ?v] ] =>
      progress replace (eval_gexpr' e h ghe ex v) with (eval_gexpr ex e h ghe v)
        by reflexivity
    | [  |- context[eval_glvalue' ?e ?h ?ghe ?ex ?adr] ] =>
      progress replace (eval_glvalue' e h ghe ex adr) with (eval_glvalue ex e h ghe adr)
        by reflexivity
    | [  H: context[eval_gexpr' ?e ?h ?ghe ?ex ?v]|- _ ] =>
      progress replace (eval_gexpr' e h ghe ex v) with (eval_gexpr ex e h ghe v) in H
        by reflexivity
    | [ H: context[eval_glvalue' ?e ?h ?ghe ?ex ?adr]  |-  _ ] =>
      progress replace (eval_glvalue' e h ghe ex adr) with (eval_glvalue ex e h ghe adr) in H
                                                        by reflexivity
    end.
Ltac destruct_eval_gexpr:=
  repeat (match goal with
         | [ H: eval_gexpr _ _ _ _ _ |- _ ] =>
           unfold eval_gexpr in H; invert H; clear H
         end; try match goal with
                  | [ H: eval_glvalue' _ _ _ _ _ |- _ ] =>
                    invert H; clear H
                  end);
  repeat fold_eval_gexpr.

Global Instance Proper_eval_expr_gexpr:
  forall ex, Proper ( env_equiv  ==> Logic.eq ==> env_equiv_gexpr ex ==> Logic.eq ==> Logic.iff) (eval_gexpr ex).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
    repeat
      match goal with
      | [ e: env |- _ ] => revert dependent e
      | [ h: heap |- _ ] => revert h
      | [ v: uval |- _ ] => revert v
      end.
    induction ex; intros; split; intros;
    destruct_eval_gexpr; econstructor; eauto;
    try match goal with
    | [ H: env_equiv _ _  |- _ ] => rewrite H in *
        end; auto;
      try solve[econstructor; eapply IHex; eauto];
      try solve[
            match goal with
            | [ H: env_equiv_gexpr _ _ _ |- _ ] =>
              rewrite H in *; auto; simpl; apply PSet.singleton_spec; auto
            end].
    - econstructor; eauto.
      econstructor.

      do 2 fold_eval_expr.
      rewrite <- H3; auto.
    - econstructor; eauto.
      econstructor; auto.

      (*Binop*)
    - fold_eval_gexpr.
      eapply IHex1; eauto.
      intros ? ?.
      eapply H1.  simpl; apply PSet.union_spec; tauto.
      
    - fold_eval_gexpr.
      eapply IHex2; eauto.
      intros ? ?.
      eapply H1.  simpl; apply PSet.union_spec; tauto.
      
    - fold_eval_gexpr.
      eapply IHex1; eauto.
      intros ? ?.
      eapply H1.  simpl; apply PSet.union_spec; tauto.
      
    - fold_eval_gexpr.
      eapply IHex2; eauto.
      intros ? ?.
      eapply H1.  simpl; apply PSet.union_spec; tauto.
  Qed.

Global Instance Proper_eval_gexpr:
  Proper ( Logic.eq ==> env_equiv  ==> Logic.eq ==> env_equiv ==> Logic.eq ==> Logic.iff) (eval_gexpr).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  eapply Proper_eval_expr_gexpr; auto.
  apply env_equiv_expr_equiv; auto.
Qed.

Global Instance Proper_eval_expr_glvalue:
  forall ex, Proper ( env_equiv  ==> Logic.eq ==> env_equiv_gexpr ex ==> Logic.eq ==> Logic.iff) (eval_glvalue ex).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
    repeat
      match goal with
      | [ e: env |- _ ] => revert dependent e
      | [ h: heap |- _ ] => revert h
      | [ v: uval |- _ ] => revert v
      end.
    induction ex; intros; split; intros HH; invert HH;
      econstructor; repeat fold_eval_gexpr;
        try solve [rewrite H in *; rewrite H1 in *; assumption].
    - do 2 fold_eval_expr.
      rewrite <- H; auto.
    - do 2 fold_eval_expr.
      rewrite H; auto.
  Qed.

Global Instance Proper_eval_glvalue:
  Proper ( Logic.eq ==> env_equiv  ==> Logic.eq ==> env_equiv ==> Logic.eq ==> Logic.iff) (eval_glvalue).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  eapply Proper_eval_expr_glvalue; auto.
  apply env_equiv_expr_equiv; auto.
Qed.

(* Equivalence between eval_expr/eval_gexpr when the expression is not ghost*)
Lemma eval_gexpr_expr:
  forall (ex : expr) (e : renv) (h : heap) (ghe : genv)  (v : val)
    (H1 : eval_gexpr ex e h ghe v),
    eval_expr ex e h v.
Proof.
  induction ex; intros; destruct_eval_gexpr; auto.
  repeat (econstructor; eauto).
Qed.

Lemma eval_expr_gexpr:
  forall (e : renv) (h : heap) (ghe : genv) (ex2 : expr) (v : val)
    (H1 : eval_expr ex2 e h v),
    eval_gexpr ex2 e h ghe v.
Proof. intros. invert H1; econstructor; eauto. Qed.
Lemma lvalue_glvalue:
  forall (e : renv) (h : heap) (ghe : genv) (ex1 : expr) (addr : block * ptrofs)
    (H: eval_lvalue ex1 e h addr),
    eval_glvalue ex1 e h ghe addr.
Proof. intros; invert H; econstructor; eauto. Qed.


Lemma deref_loc_functional:
  forall (adr0 : block * ptrofs) (h : heap) (v v' : val),
    deref_loc h adr0 v ->
    deref_loc h adr0 v' ->
    v = v'.
Proof.
  intros adr0 h v v' H0 H3.
  invert H0; invert H3. rewrite H1 in H; invert H. auto.
Qed.
 
Lemma eval_expr_functional:
  forall ex e h v v',
    eval_expr ex e h v ->
    eval_expr ex e h v' ->
    v = v'.
Proof.
  induction ex; intros;
    destruct_eval_expr; auto; subst_find; auto.

  (*Deref*)
  - assert (HH: (Vptr adr) = (Vptr adr0)) by
        (eapply IHex; eauto).
    invert HH.
    erewrite deref_loc_functional; eauto.

   (* Binop*)
  - (* eapply eval_binop_functional; eauto. *)
    erewrite (IHex1 _ _ v1 v0) in H7; eauto.
    erewrite (IHex2 _ _ v2 v3) in H7; eauto.
    rewrite H7 in H2; inversion H2; reflexivity.
Qed.
 
Lemma eval_gexpr_functional:
  forall ex e h ghe v v',
    eval_gexpr ex e h ghe v ->
    eval_gexpr ex e h ghe v' ->
    v = v'.
Proof.
  induction ex; intros;
    destruct_eval_gexpr; destruct_eval_expr; auto; subst_find; auto.

  (*binop*)
  - f_equal. 
    replace v1 with v3 in H7 by (eapply eval_expr_functional; eauto).
    replace v2 with v4 in H7 by (eapply eval_expr_functional; eauto).
    rewrite H7 in H2; inversion H2; reflexivity.
  
  - assert (HH: (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
    invert HH. f_equal; eapply deref_loc_functional; eauto.
  - assert (HH: (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
    invert HH. f_equal; eapply deref_loc_functional; eauto.
  - assert (HH: (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
    invert HH. f_equal; eapply deref_loc_functional; eauto.
  - assert (HH: (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
    invert HH. f_equal; eapply deref_loc_functional; eauto.
  - assert (HH: (RV (Vptr adr)) = (Vptr adr0)) by (eapply IHex; eauto).
    invert HH. 
    f_equal; eapply deref_loc_functional; eauto.

    (*ubinop*)
  - erewrite (IHex1 _ _ _ _ _ H5) in H7; eauto.
    erewrite (IHex2 _ _ _ _ _ H6) in H7; eauto.
    rewrite H7 in H2; inversion H2; reflexivity.
Qed.










(** *Typing*)

  (*The semantics of assertions is evaluated with respect to an environment*)
  (*Every definition is proved to be invariant under env. equivalence (Proper)*)

(*
nt n1, Vint n2 =>
    eval_int_binop op n1 n2
  | Vptr p, Vint n =>
    option_map Vptr
    (eval_ptr_int_binop ty op p n)
  | Vptr p1, Vptr p2 =>
    option_map (fun x => Vint (bool2int x))
    (eval_ptr_ptr_binop h op p1 p2)
  | _, _ => None 
*)


Inductive binop_type: binary_operation -> type -> type -> type -> Prop:=
| Intintint: forall op,
    binop_type op Tint Tint Tint
| AddPtrInt: forall ty,
    binop_type Oadd (Tpointer ty) Tint (Tpointer ty)
| SubPtrInt: forall ty,
    binop_type Osub (Tpointer ty) Tint (Tpointer ty)
| OeqPtrPtr: forall ty1 ty2,
    binop_type Oeq (Tpointer ty1) (Tpointer ty2) Tint
| OnePtrPtr: forall ty1 ty2,
    binop_type One (Tpointer ty1) (Tpointer ty2) Tint
| OltPtrPtr: forall ty1 ty2,
    binop_type Olt (Tpointer ty1) (Tpointer ty2) Tint
| OlePtrPtr: forall ty1 ty2,
    binop_type Ole (Tpointer ty1) (Tpointer ty2) Tint
| OgtPtrPtr: forall ty1 ty2,
    binop_type Ogt (Tpointer ty1) (Tpointer ty2) Tint
| OgePtrPtr: forall ty1 ty2,
    binop_type Oge (Tpointer ty1) (Tpointer ty2) Tint.
    

Fixpoint expr_type (ex:expr)(e:env)(h:heap)(ty:type): Prop:=
  match ex with
  | Econst_int _ ty' => ty = Tint /\ ty = ty'
  | Etempvar x ty' => exists v, find e x = Some v /\ val_type h v ty /\ ty = ty'
  | Ederef ex' ty' =>  expr_type ex' e h (Tpointer ty) /\ ty = ty'
  | Ebinop op ex1 ex2 ty' =>
    exists ty1 ty2,
    expr_type ex1 e h ty1 /\
    expr_type ex2 e h ty2 /\
    binop_type op ty1 ty2 ty /\
    ty = ty'
  end.

Ltac destruct_expr_type:=
  match goal with
  | [ H: expr_type ?ex _ _ _ |- _ ] =>
    match ex with
    | Econst_int _ _ => destruct H as (?&?)
    | Etempvar _ _ => destruct H as (?&?&?&?)
    | Ederef _ _ => destruct H as (?&?)
    | Ebinop _ _ _ _ => destruct H as (?&?&?&?&?&?)
    end end.

Lemma expr_type_type_of_expr:
  forall e0 e h ty,
  expr_type e0 e h ty ->
  type_of_expr e0 = ty.
Proof.
  induction e0; intros; destruct_expr_type; auto.
Qed.
       
Fixpoint wt_expr (ex:expr)(ty:type): Prop:=
  match ex with
  | Econst_int i ty' => ty = ty'
  | Etempvar _ ty' => ty = ty'
  | Ederef ex' ty' => ty = ty' /\ wt_expr ex' (Tpointer ty)
  | Ebinop op ex1 ex2 ty' => exists ty1 ty2,
                              wt_expr ex1 ty1 /\
                              wt_expr ex2 ty2 /\
                              ty = ty'
                            
  end.

Fixpoint wt_expr2 (e:env)(h:heap)(ex:expr): Prop:=
  match ex with
  | Econst_int i ty => ty = Tint
  | Etempvar x ty => exists v, find e x = Some v /\ val_type h v ty   
  | Ederef ex' ty => type_of_expr ex' =  (Tpointer ty) /\  wt_expr2 e h ex'
  | Ebinop op ex1 ex2 ty => wt_expr2 e h ex1 /\
                           wt_expr2 e h ex2 /\
                           binop_type op (type_of_expr ex1) (type_of_expr ex2) ty 
                            
  end.

Lemma expr_type_wt2_dec:
  forall (ex : expr) (e : renv) (h : heap) ty,
    expr_type ex e h ty -> wt_expr2 e h ex -> type_of_expr ex = ty.
Proof.
  induction ex; intros destruct_expr_type; auto; simpl.
  - intros. destruct_and; subst; reflexivity.
  - intros ? ? (?&?&?&?) (?&?); auto.
  - intros ? ? (?&?) (?&?); auto.
  - intros ? ? (?&?&?&?&?&?) ?; auto.
Qed.
  
Lemma expr_type_wt:
  forall (ex : expr) (e : renv) (h : heap) ty,
    expr_type ex e h ty -> wt_expr ex ty.
Proof.
  induction ex; intros; destruct_expr_type; auto.
  split; auto.
  eapply IHex; eauto.
  (*binop*) subst; do 2 eexists; split; eauto.
Qed.

Lemma expr_type_wt2:
  forall (ex : expr) (e : renv) (h : heap) ty,
    expr_type ex e h ty -> wt_expr2 e h ex.
Proof.
  induction ex; intros; destruct_expr_type; auto.
  - subst; simpl; reflexivity.
  - subst; simpl. exists x; split; auto.
  - subst; simpl.
    duplicate H.
    eapply IHex in H.
    subst; simpl; split; auto.
    eapply expr_type_wt2_dec; eauto.
  - subst; simpl.
    split; [|split].
    + eapply IHex1; eauto.
    + eapply IHex2; eauto.
    + replace (type_of_expr ex1) with x.
      replace (type_of_expr ex2) with x0.
      auto.
      * symmetry; eapply expr_type_wt2_dec; eauto.
      * symmetry; eapply expr_type_wt2_dec; eauto.
Qed.

(*
Lemma eval_expr_type:
  forall (ex : expr) (e : renv) (h : heap) ty v,
    eval_expr ex e h v ->
    val_type h v ty ->
    wt_expr ex ty ->
    expr_type ex e h ty.
Proof.
  induction ex; simpl; intros.
  - destruct_eval_expr.
    split; destruct ty0; inversion H0; auto.    
  - destruct_eval_expr.
    eexists; split; eauto.
  - destruct_eval_expr.
    destruct H4.
    split; auto.
    eapply IHex; eauto.
    + match goal with
      | [ H: deref_loc _ _ _  |- _ ] => 
        invert H
      end.  
      simpl; rewrite H.
      destruct ty0; auto.
  - destruct_eval_expr.
    destruct H1 as (ty1&ty2&?&?&?); subst.
    exists ty1, ty2.
    repeat split.
    + eapply IHex1; eauto.
    admit.
Admitted.
 *)

(* Eventually this should be 
   "convertible" types      *)
Lemma val_type_functional:
forall h ty1 v ty2,
  val_type h v ty1 ->
  val_type h v ty2 ->
  ty1 = ty2.
Proof.
  intros ? ?.
  induction ty1; intros; destruct v; try solve[inversion H].
  - destruct ty2; inversion H0; auto.
  - destruct ty2; try solve[inversion H0]; auto.
    f_equal.
    assert ((exists v, h p = Some v) \/  ty1 = ty2).
    {
      destruct ty1; simpl in H; destruct (h p) as [v|] eqn:HP; try solve[inversion H];
        try (left ; exists v; auto).
      destruct ty2; simpl in H0; rewrite HP in H0; try solve[inversion H0];
        try (right;auto).
    }
    destruct H1 as [[v HP]| ?]; auto.
    eapply (IHty1 v); eauto.
    + simpl in H. destruct ty1; rewrite HP in H; auto.
    + simpl in H0. destruct ty2; rewrite HP in H0; auto.
Qed.

   (*
Lemma eval_expr_type2:
  forall (ex : expr) (e : renv) (h : heap) ty v,
    eval_expr ex e h v ->
    val_type h v ty ->
    wt_expr2 e h  ex ->
    expr_type ex e h ty.
Proof.
  induction ex; simpl; intros.
  - destruct_eval_expr.
    split; destruct ty0; inversion H0; auto.    
  - destruct_eval_expr.
    destruct H1 as [v' [? ?]].
    rewrite H3 in H; inversion H; subst.
    eexists; repeat split; eauto.
    eapply val_type_functional; eauto.
  - destruct_eval_expr.
    destruct H4.
    split.
    + eapply IHex; eauto.
      simpl.
      inversion H1; subst.
      destruct ty0; rewrite H4; auto.
    + invert H1.
      destruct ex; simpl in H0; invert H0;
        try solve[inversion H4]; try solve[inversion H3].
      * inversion H3; subst.
      
      
    simpl in H4.
    destruct H4.
    split; auto.
    eapply IHex; eauto.
    + match goal with
      | [ H: deref_loc _ _ _  |- _ ] => 
        invert H
      end.  
      simpl; rewrite H.
      destruct ty0; auto.
  - destruct_eval_expr.
    destruct H1 as (ty1&ty2&?&?&?); subst.
    exists ty1, ty2.
    repeat split.
    + eapply IHex1; eauto.
    admit.
Admitted.
    *)

(*
Lemma expr_type_eval:
  forall ex e h v ty,
    eval_expr ex e h v ->
    expr_type ex e h (ty) ->
    val_type h v ty.
Proof.
  induction ex;intros; try solve [do 2 destruct_eval_expr].
  - do 2 destruct_eval_expr.
    destruct_expr_type; subst.
    simpl;trivial.
  - do 2 destruct_eval_expr.
    destruct_expr_type; subst.
    subst_find.
    auto.
  - destruct_eval_expr.
    destruct_expr_type; subst.
    eapply IHex in H; eauto.
    simpl in H.
    invert H1.
    destruct ty; rewrite H in H0; auto.
  - (*binop*)
    destruct_eval_expr.
    destruct_expr_type; subst ty0.
    specialize (IHex1 _ _ _ _ H5 H).
    specialize (IHex2 _ _ _ _ H6 H0).
    clear - H7 IHex1 IHex2 H1.

    Lemma eval_binop_types:
      forall (bo : binary_operation) (ty0 ty1 ty2 ty : type) 
             (h : heap) (v v1 v2 : val),
        eval_binop h ty0 bo v1 v2 = Some v ->
        val_type h v1 ty1 ->
        val_type h v2 ty2 ->
        binop_type bo ty1 ty2 ty ->
        val_type h v ty.
    Proof.
      intros.
      invert H2.
      - destruct v1; try solve[inversion H0].
        destruct v2; try solve[inversion H1].
        simpl in H.
        destruct bo; inversion H; auto.
      - destruct v1; try solve[inversion H0].
        destruct v2; try solve[inversion H1].
        destruct p; simpl in H. inversion H.
        destruct ty0 eqn:HH; simpl.
        simpl.
        unfold eval_ptr_int_binop in H.
    Admitted.

    eapply eval_binop_types; eauto.
Qed.
*)

(*
(*Not needed anymore*)
Lemma expr_type_eval_pointers:
  forall ex e h v ty ty0,
    eval_expr (Ederef ex ty0) e h v ->
    expr_type ex e h (Tpointer ty) ->
    val_type h v ty.
Proof.
  intros.
  eapply expr_type_eval; eauto.
  simpl; split; eauto.
Admitted.
*)
(*
  
  
  induction ex;intros; try solve [do 2 destruct_eval_expr].
  - do 2 destruct_eval_expr.
    destruct_expr_type.
    subst_find.
    simpl in H0.
    invert H1.
    destruct ty0; simpl in H3; rewrite H in H3; auto.
  - destruct_eval_expr.
    destruct_expr_type.
    eapply IHex in H; eauto.
    simpl in H.
    invert H1.
    destruct ty0;  rewrite H in H2; auto.
  - (*binop*)
    destruct_eval_expr.
    destruct_expr_type. subst ty.
    
    admit.
Admitted.
*)

Global Instance Proper_expr_type_expr: Proper (Logic.eq ==> env_equiv ==> Logic.eq ==>Logic.eq ==> Logic.iff) expr_type.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  repeat match goal with
  | [ e: env |- _ ] => revert e 
  | [ t: type |- _ ] => revert t
  | [ h: heap |- _ ] => revert h
  end.
  induction y; try (simpl; intros; try rewrite H0; first[ reflexivity| f_equiv; apply IHy]).
  (*binopo*)
  - intros; split; intros (? & ? &? & ? & ? & ?); subst; simpl.
    + do 2 eexists; repeat split; eauto.
      eapply IHy1; eauto.
      eapply IHy2; eauto.
    + do 2 eexists; repeat split; eauto.
      eapply IHy1; eauto.
      eapply IHy2; eauto.
Qed.

Fixpoint gval_type (gv:gval)(gty:gtype):Prop:=
  match gv, gty with
  | GVnat _, GTnat | GVbool _, GTbool | GVheap _, GTheap => True 
  | _, _ => False
  end.



Definition uval_type (rh:heap)(uv:uval)(uty:utype):Prop:=
  match uty, uv with
    | RT ty, RV v => val_type rh v ty
    | GT ty, GV v => gval_type v ty
    | _, _ => False
  end.

Fixpoint gexpr_type (gex:gexpr)(e:env)(rh:heap)(ghe:genv)(ty:utype): Prop:=
  match ty, gex with
  | RT ty', Rexpr ex' => expr_type ex' e rh ty'
  | RT ty', GEconst_ptr p _ => val_type rh (Vptr p) ty'
  | GT ty', GEconst_nat n _ => gval_type (GVnat n) ty'
  | GT ty', GEconst_bool b _ => gval_type (GVbool b) ty'
  | _ , GEtempvar x _ => exists v, find ghe x = Some v /\
                               uval_type rh v ty
  | RT ty', GEderef ex' _ =>  gexpr_type ex' e rh ghe (GT (GTpointer ty'))
  | _, _ => False
  end.

Global Instance Proper_gexpr_type: forall gex, Proper (env_equiv ==> Logic.eq ==> env_equiv_gexpr gex ==> Logic.eq ==> Logic.iff) (gexpr_type gex).
Proof.
Admitted.