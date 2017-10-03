Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import  Program.Equality.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)
Require Import Coq.Classes.Morphisms.

Require Import VCC.Tactics.
Require Import VCC.Basics. Import Basics.
Require Import VCC.Expressions.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import VCC.Semantics.
Require Import VCC.AssertionSemantics.
Import Expressions.


(*An expressions are defined*)
Fixpoint assert_expr_defined (ex:expr): assertion:=
  match ex with
    Econst_int v => Atrue
  | Etempvar id => Adefined id
  | Ederef ex' =>
    let p:= fresh_var empty in
    (Agexists p ((GEtempvar p)== ex' /\ Aalloc p))%assert
  end.
Fixpoint assert_gexpr_defined (ex:gexpr): assertion:=
  match ex with
  | Rexpr ex' => assert_expr_defined ex'
  | GEconst_ptr p =>
    let xp:= fresh_var empty in
    (Agexists xp ((Etempvar xp)== GEconst_ptr p) /\ Aalloc xp)%assert 
  | GEconst_nat _ => Atrue
  | GEconst_bool _ => Atrue
  | GEtempvar id => Agdefined id
  | GEderef ex' => 
    let xp:= fresh_var (free_vars_expr ex' ) in
    (Agexists xp ((GEtempvar xp)== ex' /\ Aalloc xp))%assert
  end.
Fixpoint assert_lvalue_defined (ex:expr): assertion:=
  match ex with
    Econst_int v => Afalse
  | Etempvar id => Afalse
  | Ederef ex' =>
    let xp:= fresh_var empty in
    (Agexists xp ((Etempvar xp)== ex'))%assert
  end.

(* Correctness the previous three functions*)
Lemma expr_defined_safe:
  forall (ex : expr) ghe (e : env) (h : heap),
    [e, h, ghe]|= (assert_expr_defined ex) ->
    exists v, eval_expr ex e h v.
Proof.
  induction ex; try solve[do 2 econstructor];
    intros ? ? ? H.
  - simpl in H;
      destruct (find e id) eqn:HH; [|contradict H; reflexivity].
    eexists; econstructor; eauto.
  - destruct H as (v1 &( v2 & ? & ?) & adr & ? & ?).
    destruct (h adr) eqn:HH; [|contradiction H2; reflexivity].
    eexists; econstructor;
      econstructor; try eassumption.
    fold_eval_expr.
    simpl_env_gexpr.
    remember (fresh_var empty) as p.
    remember (eval_gexpr ex e h ghe v2) as HH0.
    destruct_eval_gexpr.
    subst HH0.
    destruct_eval_expr.
    simpl_find.
    invert H0; eauto.
    eapply eval_gexpr_expr; eauto.
Qed.
Lemma gexpr_defined_safe:
  forall (ex : gexpr) ghe (e : env) (h : heap),
    [e, h, ghe]|= (assert_gexpr_defined ex) ->
    exists v, eval_gexpr ex e h ghe v.
Proof.
  induction ex; try solve[do 2 econstructor];
    intros ? ? ? H.
  - eapply expr_defined_safe in H as (?&?).
    do 2 econstructor; eauto.
  - simpl in H.
    destruct (find ghe id) eqn:HH; [|contradict H; reflexivity].
    eexists; econstructor; eauto.
  - destruct H as (v1 &( v2 & ? & ?) & adr & ? & ?).
    destruct (h adr) eqn:HH; [|contradiction H2; reflexivity].
    eexists; econstructor;
      econstructor; try eassumption.
    fold_eval_gexpr.
    remember (fresh_var empty) as p.
    simpl_env_gexpr.
    remember (eval_gexpr ex e h ghe v2) as HH0.
    destruct_eval_gexpr.
    subst HH0.
    simpl_find.
    assumption.
Qed.