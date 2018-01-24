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
Require Import VCC.Assertions.
Import Expressions.

(*An expressions is defined*)
Fixpoint assert_expr_eval (ex:expr)(x:ident): assertion:=
  (match ex with
    Econst_int v ty => Agvariable x (Vint v)
  | Etempvar id ty => Adefined id x
  | Ederef ex' ty =>
    let p:= fresh_var (singleton x) in
    let ty':= type_of_expr ex' in
    Agexists p ((GEtempvar p ty')== ex' /\ Aalloc p x)
  | Ebinop op ex1 ex2 ty =>
    let x1:= fresh_var (union (free_vars_gexpr ex) (singleton x)) in
    let x2:= fresh_var (union (union (free_vars_gexpr ex) (singleton x1)) (singleton x)) in
    Agexists x1
    (Agexists x2
    (assert_expr_eval ex1 x1 /\
    assert_expr_eval ex2 x2 /\
    Abinop op (type_of_expr ex1) x1 x2 x )) (* Need type correctness?? *)
   end /\
   Aexpr_type ex (type_of_expr ex) 
  )%assert.

Definition assert_expr_defined (ex:expr): assertion :=
  let x := fresh_var empty in
  Agexists x (assert_expr_eval ex x).

Fixpoint assert_gexpr_eval (ex:gexpr)(x:ident): assertion:=
  match ex with
  | Rexpr ex' => assert_expr_eval ex' x
  | GEconst_ptr p ty' =>
    ( Agvariable x (Vptr p))%assert 
  | GEconst_nat n  _=> 
    ( Agvariable x (GVnat n))%assert 
  | GEconst_bool b _ => 
    ( Agvariable x (GVbool b))%assert 
  | GEtempvar id _ => Agdefined id x
  | GEderef ex' _ => 
    let xp:= fresh_var (union (free_vars_gexpr ex')(singleton x) ) in
    let ty':= type_of_gexpr ex' in
    (Agexists xp ((GEtempvar xp ty')== ex' /\ Aalloc xp x))%assert
  | GEbinop op ex1 ex2 ty =>
    let x1:= fresh_var (union (free_vars_gexpr ex) (singleton x)) in
    let x2:= fresh_var (union (union (free_vars_gexpr ex) (singleton x1)) (singleton x)) in
    Agexists x1
    (Agexists x2
    ( assert_gexpr_eval ex1 x1 /\
    assert_gexpr_eval ex2 x2 /\
    Abinop op (type_of_gexpr ex1) x1 x2 x )) 
  end.

Definition assert_gexpr_defined (ex:gexpr): assertion :=
  let x := fresh_var (free_vars_gexpr ex) in
  Agexists x (assert_gexpr_eval ex x).

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
Lemma assert_expr_eval_safe:
  forall (ex : expr) ghe (e : env) (h : heap) (id:ident),
    [e, h, ghe]|= (assert_expr_eval ex id) ->
    exists v, eval_expr ex e h v /\
         find ghe id = Some (RV v).
Proof.
  induction ex; try solve[do 2 econstructor];
    intros ? ? ? ? [].
  - (*Econst_int*)
    simpl in H. 
    eexists; econstructor; eauto.
    econstructor.
  - destruct H.
      destruct (find e id) eqn:HH; [|contradict H1; reflexivity].
      eexists; split; eauto.
      econstructor; eauto.
  - destruct H as (v1 & (v2 & ?  &?) & (adr & ? & ? & ?)). 
    destruct (h adr) eqn:HH; [|contradiction H4; reflexivity].
    eexists; split; [econstructor;
      econstructor; try eassumption|].
    + fold_eval_expr.
      simpl_env_gexpr.
      remember (fresh_var empty) as p.
      remember (eval_gexpr ex e h ghe v2) as HH0.
      destruct_eval_gexpr.
      subst HH0.
      destruct_eval_expr.
      simpl_find.
      eapply eval_gexpr_expr; eauto.
    + simpl_find.
      simpl in H3; rewrite H3.
      symmetry; apply gso.
      intros ?.
      eapply (fresh_var_spec (singleton id)).
      apply singleton_spec; assumption.
    
  - (* binop *)
    destruct H as (v1  & v2 & H1 & H2 & ?).
    remember (fresh_var (union (free_vars_gexpr (Ebinop bo ex1 ex2 ty)) (singleton id)))as x1.
    remember (fresh_var
                  (union (union (free_vars_gexpr (Ebinop bo ex1 ex2 ty)) (singleton x1))
                     (singleton id))) as x2.
    eapply IHex1 in H1.
    eapply IHex2 in H2.
    destruct H1 as (v1' & H1 & ?).
    destruct H2 as (v2' & H2 & ?).
    destruct H as (v1'' & v2'' & v3'' & ? & ? & ? & ? ).
    simpl_find.
    simpl in H7.
    destruct v3'' as [v3''|?]; try solve[inversion H7].
    2: destruct (eval_binop h (type_of_expr ex1)  bo v1' v2'); simpl in H7; inversion H7.
    exists v3''. split.
    + econstructor; eauto.
      destruct ((eval_binop h (type_of_expr ex1) bo v1' v2')) eqn:HH; inversion H7; subst.
      auto.
    + subst. simpl_find.
      rewrite <- H6.
      symmetry; repeat rewrite gso; auto.
Qed.

Lemma expr_defined_safe:
  forall (ex : expr) ghe (e : env) (h : heap),
    [e, h, ghe]|= (assert_expr_defined ex) ->
    exists v, eval_expr ex e h v.
Proof.
  intros. 
  destruct H.
  apply assert_expr_eval_safe in H.
  destruct H as (?&?&?).
  eexists; eauto.
Qed.
      
Lemma assert_gexpr_eval_safe:
  forall (ex : gexpr) ghe (e : env) (h : heap) (x:ident),
    [e, h, ghe]|= (assert_gexpr_eval ex x) ->
    exists v, eval_gexpr ex e h ghe v /\
         find ghe x = Some v.
Proof.
  induction ex; try solve[do 2 econstructor];
    intros ? ? ? ? H.
  - eapply assert_expr_eval_safe in H as (?&?&?).
    do 2 econstructor; eauto.
    econstructor; assumption.
  - (*GEconst_ptr*)
    do 2 econstructor.
    eauto; constructor.
    simpl in H; auto.
  - (*GEconst_nat*) 
    do 2 econstructor.
    eauto; constructor.
    simpl in H; auto.
  - (*GEconst_bool*) 
    do 2 econstructor.
    eauto; constructor.
    simpl in H; auto.
  - destruct H.
    destruct (find ghe id) eqn:HH; [|contradict H0; reflexivity].
    eexists; econstructor; eauto.
    econstructor; eauto.
  - destruct H as (v1 &( v2 & ? & ?) & adr & ? & ? & ?).
    destruct (h adr) eqn:HH; [|contradiction H3; reflexivity].
    eexists; econstructor;
      try (econstructor; econstructor); try eassumption.
    + fold_eval_gexpr.
      remember (fresh_var empty) as p.
      simpl_env_gexpr.
      remember (eval_gexpr ex e h ghe v2) as HH0.
      destruct_eval_gexpr.
      subst HH0.
      simpl_find.
      assumption.
    + simpl in H2; rewrite H2.
      symmetry. eapply gso.
      intros ?.
      eapply (fresh_var_spec (union (free_vars_gexpr ex) (singleton x))).
      rewrite H4.
      eapply union_spec. right; eapply singleton_spec; auto. 
      
  - (*binop*)
    
    destruct H as (v1  & v2 & H1 & H2 & ?).
    
    eapply IHex1 in H1.
    eapply IHex2 in H2.
    destruct H1 as (v1' & H1 & ?).
    destruct H2 as (v2' & H2 & ?).
    destruct H as (v1'' & v2'' & v3'' & ? & ? & ? & ? ).
    simpl_find.
    simpl in H5.
    exists v3''. split; auto.
    subst; simpl_env_gexpr.
      remember (fresh_var (union (free_vars_gexpr (GEbinop bo ex1 ex2 ty)) (singleton x)))as x1.
      remember (fresh_var
                  (union (union (free_vars_gexpr (GEbinop bo ex1 ex2 ty)) (singleton x1))
                         (singleton x))) as x2.
      econstructor; eauto.
Qed.

Lemma gexpr_defined_safe:
  forall (ex : gexpr) ghe (e : env) (h : heap),
    [e, h, ghe]|= (assert_gexpr_defined ex) ->
    exists v, eval_gexpr ex e h ghe v.
Proof.
  intros. 
  destruct H.
  apply assert_gexpr_eval_safe in H.
  destruct H as (?&?&?).
  eexists; eauto.
  simpl_env_gexpr; eauto.
Qed.