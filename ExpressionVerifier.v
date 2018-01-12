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


(*An expressions is defined*)
Fixpoint assert_expr_defined (ex:expr): assertion:=
  (match ex with
    Econst_int v ty => Atrue
  | Etempvar id ty => Adefined id
  | Ederef ex' ty =>
    let p:= fresh_var empty in
    let ty':= type_of_expr ex' in
    Agexists p ((GEtempvar p ty')== ex' /\ Aalloc p)
  | Ebinop op ex1 ex2 ty =>
    assert_expr_defined ex1 /\
    assert_expr_defined ex2 /\
    Atrue (* Need type correctness?? *)
   end /\
   Aexpr_type ex (type_of_expr ex) 
  )%assert.

Fixpoint assert_gexpr_defined (ex:gexpr): assertion:=
  match ex with
  | Rexpr ex' => assert_expr_defined ex'
  | GEconst_ptr p ty' =>
    let xp:= fresh_var empty in
    (Agexists xp ((Etempvar xp ty')== ex) /\ Aalloc xp)%assert 
  | GEconst_nat _  _=> Atrue
  | GEconst_bool _ _ => Atrue
  | GEtempvar id _ => Agdefined id
  | GEderef ex' _ => 
    let xp:= fresh_var (free_vars_expr ex' ) in
    let ty':= type_of_gexpr ex' in
    (Agexists xp ((GEtempvar xp ty')== ex' /\ Aalloc xp))%assert
  | GEbinop op ex1 ex2 ty =>
    assert_gexpr_defined ex1 /\
    assert_gexpr_defined ex2 /\
    Atrue (* Need type correctness?? *)
    
  end.

Fixpoint assert_lvalue_defined (ex:expr): assertion:=
  match ex with
    Econst_int v _ => Afalse
  | Etempvar id _ => Afalse
  | Ederef ex' ty =>
    let xp:= fresh_var empty in
    let ty':= type_of_expr ex' in
    (Agexists xp ((Etempvar xp ty')== ex'))%assert
  | Ebinop _ _ _ _ => Afalse
  end.

(* Correctness the previous three functions*)
Lemma expr_defined_safe:
  forall (ex : expr) ghe (e : env) (h : heap),
    [e, h, ghe]|= (assert_expr_defined ex) ->
    exists v, eval_expr ex e h v.
Proof.
  induction ex; try solve[do 2 econstructor];
    intros ? ? ? [].
  - simpl in H;
      destruct (find e id) eqn:HH; [|contradict H; reflexivity].
    eexists; econstructor; eauto.
  - destruct H as (v1 &( v2 & ? & ?) & adr & ? & ?).
    destruct (h adr) eqn:HH; [|contradiction H3; reflexivity].
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
    eapply eval_gexpr_expr; eauto.
  - (* binop *)
    eexists. econstructor.
    
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