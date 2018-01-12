
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 
Require Import FSets.FMapPositive.
Import PositiveMap. Module PMap:= PositiveMap. (*For positive-indexed maps*)
Require Import FSets.FMapFacts.

Module PMapsFacts:=  (WFacts_fun OrderedTypeEx.PositiveOrderedTypeBits PMap).
Import PMapsFacts.

Require Import VCC.Tactics.
Require Import VCC.Basics.

(** * 8) Environment *)
Section ParametricInVal.
  Context {val: Type}.
Definition env:Type := PMap.t val.
Definition find  (e:env) (k:ident) := PMap.find k e.
Definition env_fun_equiv: relation (positive -> option val) := pointwise_relation _ Logic.eq.

Global Instance Equivalence_env_fun_equiv: Equivalence env_fun_equiv:= _.
Definition env_equiv: relation env := (fun x y => env_fun_equiv (find x) (find y)).
Global Instance Equivalence_env_equiv: Equivalence env_equiv.
Proof.
  pose proof (Relations.inverse_image_of_equivalence _ _  find env_fun_equiv).
  destruct H; auto.
  constructor;
    destruct (Equivalence_env_fun_equiv); eauto.
Qed.


Definition remove_env (e:env) (k:ident): env:=
  PMap.remove k e.
Global Instance Proper_remove_env: Proper ( env_equiv ==> Logic.eq ==> env_equiv) remove_env.
Proof.
  intros ? ? ? ? ? ? id; subst.
  cbv delta [remove_env] beta.
  destruct (Pos.eq_dec y0 id); auto.
  - subst. cbv [find]; repeat rewrite remove_eq_o; eauto.
  - cbv [find]; repeat rewrite remove_neq_o; eauto.
Qed.

Definition empty_env: env:= PMap.empty _.
Definition update_env (e:env) (k:ident) (value:option val) : env:=
  match value with
    | None => remove_env e k
    | Some v => PMap.add k v e
  end.

Global Instance Proper_update_env: Proper ( env_equiv ==> Logic.eq ==> Logic.eq ==> env_equiv) update_env.
Proof.
  intros ? ? ? ? ? ? ? ? ? id; subst.
  destruct y1 as [v_ty|]; simpl.
  - cbv delta [update_env] beta.
    destruct (Pos.eq_dec y0 id); auto.
    + subst. cbv [find]. repeat rewrite add_eq_o; eauto.
    + cbv [find]; repeat rewrite add_neq_o; eauto.
  - eapply Proper_remove_env; auto.
Qed.


Lemma gro:
  forall id e id',
    id <> id' ->
    find (remove_env e id') id = find e id.
Proof.
  cbv delta[find remove_env] beta; intros.
  rewrite PMap.gro; auto.
Qed.
Lemma grs:
  forall id e,
    find (remove_env e id) id = None.
Proof.
  cbv delta[find remove_env] beta; intros.
  rewrite PMap.grs; auto.
Qed.
Lemma gss:
  forall e id v_ty,
    find (update_env e id v_ty) id = v_ty.
Proof.
  intros.
  destruct v_ty; simpl.
  - cbv delta[find update_env] beta.
    rewrite add_eq_o; auto.
  - rewrite grs; reflexivity.
Qed.
Lemma gso:
  forall e id id' v_ty,
    id <> id' ->
    find (update_env e id v_ty) id' = find e id'.
Proof.
  intros.
  destruct v_ty; simpl.
  - cbv delta[find update_env] beta.
    rewrite add_neq_o; auto.
  - rewrite gro; auto.
Qed.


Lemma redundant_update:
  forall e i v_ty v_ty',
    env_equiv (update_env (update_env e i v_ty) i v_ty')
              (update_env e i v_ty').
Proof.
  intros ? ? ? ? id.
  destruct (peq i id).
  - subst. repeat rewrite gss; reflexivity.
  - repeat rewrite gso; auto.
Qed.
Lemma update_comm:
  forall e i j v_ty v_ty',
    i <> j ->
    env_equiv (update_env (update_env e i v_ty) j v_ty')
              (update_env (update_env e j v_ty') i v_ty).
Proof.
  intros ? ? ? ? ? NEQ id.
  - destruct (peq i id); destruct (peq j id); subst;
    try solve[contradiction NEQ; auto];
    repeat (repeat rewrite gss;
            rewrite gso;
            repeat rewrite gss); auto.
Qed.

Lemma pointless_update:
  forall e k v_ty,
    find e k = v_ty ->
    env_equiv (update_env e k v_ty) e.
Proof.
  intros ? ? ? ? id.
  destruct (peq k id).
  - subst; rewrite gss; reflexivity.
  - rewrite gso; auto.
Qed.

End ParametricInVal.

Definition renv:= @env val.
Definition genv:= @env uval.

Definition find_error (e:renv) (k:ident) : val:=
  match find e k with
  | Some v => v
  | None => Vundef
  end.

Ltac subst_find :=
  repeat
    match goal with
    | [ H: find ?e ?x = Some _, H': find ?e ?x = Some _  |- _ ] =>
      rewrite H in H'; invert H'
    end.
                              