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
  | Oxor : binary_operation             (** bitwise xor ([^]) *)
  | Oshl : binary_operation             (** left shift ([<<]) *)
  | Oshr : binary_operation             (** right shift ([>>]) *)
  | Oeq: binary_operation               (** comparison ([==]) *)
  | One: binary_operation               (** comparison ([!=]) *)
  | Olt: binary_operation               (** comparison ([<]) *)
  | Ogt: binary_operation               (** comparison ([>]) *)
  | Ole: binary_operation               (** comparison ([<=]) *)
  | Oge: binary_operation.              (** comparison ([>=]) *)


(*
Definition sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2)
*)

(** * 3) Expressions *)
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


(** * 5) Evaluating expression  *)

Definition eval_binop : binary_operation -> val -> val -> val -> Prop.
Admitted.

Definition eval_gbinop : binary_operation -> gval -> gval -> gval -> Prop.
Admitted.

Inductive eval_ubinop:  binary_operation -> uval -> uval -> uval -> Prop:=
| eval_Rbinop: forall op v1 v2 v,
    eval_binop op v1 v2 v ->
    eval_ubinop op v1 v2 v
| eval_Gbinop: forall op v1 v2 v,
    eval_gbinop op v1 v2 v ->
    eval_ubinop op v1 v2 v.

Inductive eval_expr' (e:renv)(h:heap): expr -> val -> Prop :=
  | eval_Econst_int: forall i ty,
      eval_expr' e h (Econst_int i ty) (Vint i)
  | eval_Etempvar: forall id v ty,
      find e id = Some v ->
      eval_expr' e h (Etempvar id ty) v
  | eval_Ebinop: forall op ex1 ex2 v1 v2 v ty,
      eval_expr' e h ex1 v1 ->
      eval_expr' e h ex2 v2 ->
      eval_binop op v1 v2 v ->
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
      eval_ubinop op v1 v2 v ->
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

 Lemma eval_binop_functional: forall op v1 v2 v v',
      eval_binop op v1 v2 v ->
      eval_binop op v1 v2 v' ->
      v = v'.
    Admitted.

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
  - eapply eval_binop_functional; eauto.
    erewrite (IHex1 _ _ v1 v0); eauto.
    erewrite (IHex2 _ _ v2 v3); eauto.
Qed.
Lemma eval_gexpr_functional:
  forall ex e h ghe v v',
    eval_gexpr ex e h ghe v ->
    eval_gexpr ex e h ghe v' ->
    v = v'.
Proof.
  induction ex; intros;
    destruct_eval_gexpr; destruct_eval_expr; auto; subst_find; auto.
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
Qed.










(** *Typing*)

  (*The semantics of assertions is evaluated with respect to an environment*)
  (*Every definition is proved to be invariant under env. equivalence (Proper)*)

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

Fixpoint expr_type (ex:expr)(e:env)(h:heap)(ty:type): Prop:=
  match ex with
  | Econst_int _ ty' => ty = Tint /\ ty = ty'
  | Etempvar x ty' => exists v, find e x = Some v /\ val_type h v ty /\ ty = ty'
  | Ederef ex' ty' =>  expr_type ex' e h (Tpointer ty) /\ ty = ty'
  end.

Ltac destruct_expr_type:=
  match goal with
  | [ H: expr_type ?ex _ _ _ |- _ ] =>
    match ex with
    | Econst_int _ _ => destruct H as (?&?)
    | Etempvar _ _ => destruct H as (?&?&?&?)
    | Ederef _ _ => destruct H as (?&?)
    end end.

Lemma expr_type_type_of_expr:
  forall e0 e h ty,
  expr_type e0 e h ty ->
  type_of_expr e0 = ty.
Proof. induction e0; simpl;
         intros; destruct_and ; auto.
       destruct H as (?&?&?&?); auto.
Qed.
       
Fixpoint wt_expr (ex:expr)(ty:type):=
  match ex with
  | Econst_int i ty' => ty = ty'
  | Etempvar _ ty' => ty = ty'
  | Ederef ex' ty' => ty = ty' /\ wt_expr ex' (Tpointer ty)
  end.

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
Qed.

Lemma expr_type_eval_pointers:
  forall ex e h v ty ty0,
    eval_expr (Ederef ex ty0) e h v ->
    expr_type ex e h (Tpointer ty) ->
    val_type h v ty.
Proof.
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
Qed.

Global Instance Proper_expr_type_expr: Proper (Logic.eq ==> env_equiv ==> Logic.eq ==>Logic.eq ==> Logic.iff) expr_type.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  repeat match goal with
  | [ e: env |- _ ] => revert e 
  | [ t: type |- _ ] => revert t
  | [ h: heap |- _ ] => revert h
  end.
  induction y; simpl; intros; try rewrite H0; first[ reflexivity| f_equiv; apply IHy].
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
  | GT ty', GEtempvar x _ => exists v, find ghe x = Some v /\
                               uval_type rh v ty
  | RT ty', GEderef ex' _ =>  gexpr_type ex' e rh ghe (GT (GTpointer ty'))
  | _, _ => False
  end.

Global Instance Proper_gexpr_type: forall gex, Proper (env_equiv ==> Logic.eq ==> env_equiv_gexpr gex ==> Logic.eq ==> Logic.iff) (gexpr_type gex).
Proof.
Admitted.