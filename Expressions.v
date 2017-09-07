Require Import Relation_Definitions.
Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.

Require Import Coq.Classes.Morphisms.

Require Import VCC.Basics.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import Coq.Logic.Classical_Prop.

Notation heap:=(@ heap val).
(** * 3) Expressions *)

Inductive expr : Type :=
  | Econst_int ( i: int) (* integer constant*)
  | Etempvar (id: ident)  (**r constant *)
  | Ederef (ex:expr).        (* pointer dereference (unary * ) *)
Notation expr_zero:= (Econst_int Int.zero).

Inductive gexpr : Type :=
  | Rexpr (ex: expr) 
  | GEconst_ptr ( adr: address)
  | GEconst_nat ( n: nat) 
  | GEconst_bool (b: bool) 
  | GEtempvar (id: ident)  (**r constant *)
  | GEderef (ex:gexpr)        (* pointer dereference (unary * ) *).
Coercion Rexpr: expr >-> gexpr.

Fixpoint free_vars_expr (e:gexpr): PositiveSet.t:=
  match e with
  | GEtempvar id => singleton id
  | GEderef ex => free_vars_expr ex
  | _ => empty
  end.
  
Inductive deref_loc (h: heap) (adr: block * ptrofs) : val -> Prop :=
  | deref_loc_value: forall v,
      h adr = Some v ->
      deref_loc h adr v.


(** * 5) Evaluating expression  *)

Inductive eval_expr' (e:renv)(h:heap): expr -> val -> Prop :=
  | eval_Econst_int: forall i,
      eval_expr' e h (Econst_int i) (Vint i)
  | eval_Etempvar: forall id v,
      find e id = Some v ->
      eval_expr' e h (Etempvar id) v
  | eval_Elvalue: forall a adr v,
      eval_lvalue' e h a adr ->
      deref_loc h adr v ->
      eval_expr' e h a v
with eval_lvalue' (e:renv) (h:heap): expr -> (block* ptrofs) -> Prop :=
  | eval_Ederef: forall a adr,
      eval_expr' e h a (Vptr adr) ->
      eval_lvalue' e h (Ederef a) adr.

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
| geval_ptr: forall p,
    eval_gexpr' e h ghe (GEconst_ptr p) (RV (Vptr p))
| geval_nat: forall n,
    eval_gexpr' e h ghe (GEconst_nat n) (GV (GVnat n))
| geval_bool: forall b,
    eval_gexpr' e h ghe (GEconst_bool b) (GV (GVbool b))
| geval_GEtempvar: forall id v,
    find ghe id = Some v ->
    eval_gexpr' e h ghe (GEtempvar id) v
| eval_GElvalue: forall a adr v,
    eval_glvalue' e h ghe a adr ->
    deref_loc h adr v ->
      eval_gexpr' e h ghe a (RV v)
with eval_glvalue' (e:renv)(h:heap)(ghe:genv): gexpr -> (block* ptrofs) -> Prop :=
  | eval_GEderef: forall a adr,
      eval_gexpr' e h ghe a (RV (Vptr adr)) ->
      eval_glvalue' e h ghe  (GEderef a) adr.

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

Ltac revert_but HH:=
  repeat match goal with
         | [ H: _ |- _ ] =>
           progress
             match H with
             | HH => idtac
             | _ => revert H
             end
         end.
Ltac invert HH:=
  revert_but HH;
  inversion HH; subst;
  intros.
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
  - do 2 econstructor.
    eapply IHy; eauto.
    inversion H2; subst; eauto.
  - do 2 econstructor.
    eapply IHy; eauto.
    inversion H2; subst; eauto.
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
      try solve[rewrite H2 in *; auto; simpl; apply PSet.singleton_spec; auto].
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
        rewrite H in *; rewrite H1 in *; assumption.
  Qed.

Global Instance Proper_eval_glvalue:
  Proper ( Logic.eq ==> env_equiv  ==> Logic.eq ==> env_equiv ==> Logic.eq ==> Logic.iff) (eval_glvalue).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?; subst.
  eapply Proper_eval_expr_glvalue; auto.
  apply env_equiv_expr_equiv; auto.
Qed.