(*For finite sets*)
Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)
Require Import Coq.Classes.Morphisms.

Require Import Relation_Definitions.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import VCC.Tactics.
Require Import VCC.Freshvars.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import VCC.Basics.
Require Import VCC.Expressions.

Lemma forall_exists_iff: forall A (P Q: A -> Prop),
    (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  intros ? ? ? H1; split; intros [v H2]; eexists; eapply H1; eassumption.
Qed.


Definition option_val_type (rh:heap) (ov:option val) (ty:type): Prop:=
  match ov with
  | Some v => val_type rh v ty
  | None => True 
  end.

Definition option_uval_utype (rh:heap) (ov:option uval) (ty:utype): Prop:=
  match ov with
  | Some v => uval_type rh v ty
  | None => True 
  end.
  
Definition bool_val (v:val)(ty:type): option bool:=
  match v,ty with
  | Vint n, Tint => 
    Some  (negb (Int.eq n Int.zero)) 
  | _, _ => None
  end.


(** * 4) Assertions *)


Inductive assertion:=
| Atrue : assertion
| Afalse : assertion
| Aand : assertion -> assertion -> assertion
| Aor : assertion -> assertion -> assertion
| Anot : assertion -> assertion
| Aexists : ident -> assertion -> assertion
| Agexists : ident -> assertion -> assertion
| Adefined : ident -> assertion
| Agdefined : ident -> assertion
| Aalloc : ident -> assertion
| Aupdate_heap : ident -> ident -> ident -> assertion  (* UPD oldH pointer value newH *)
| Aexists_heap : assertion -> assertion
| Aequal_heap : ident -> assertion  (* UPD oldH pointer value newH *)
| Aexpr_type : expr -> type -> assertion
| Agexpr_type : gexpr -> utype -> assertion
| Aref_eq: gexpr -> gexpr -> assertion
| Aeq: gexpr -> gexpr -> assertion. (* x == 5 *)

Bind Scope assert_scope with assertion.
Delimit Scope assert_scope with assert.
Infix "/\" := Aand (right associativity, at level 80) : assert_scope.
Infix "\/" := Aor (right associativity, at level 85) : assert_scope.
Notation "~ x" := (Anot x) : assert_scope.
Notation "'Ex'" := Aexists (at level 70) : assert_scope.
Notation "'Defined'" := Adefined : assert_scope.
Notation "'UPDATE'" := Aupdate_heap : assert_scope.
Notation "'Alloc'" := Aalloc : assert_scope.
Infix "==" := Aeq (right associativity, at level 65) : assert_scope.

Fixpoint eval_assert (P:assertion)(re:renv)(rh:heap)(ghe:genv): Prop:=
  match P with
  | Atrue => True
  | Afalse => False
  | Aand P1 P2 => eval_assert P1 re rh ghe /\ eval_assert P2 re rh ghe
  | Aor  P1 P2 => eval_assert P1 re rh ghe \/ eval_assert P2 re rh ghe
  | Anot P => ~ eval_assert P re rh ghe
  | Aexists id P =>
    exists v, eval_assert P (update_env re id v) rh ghe
  | Agexists id P =>
    exists v,
    eval_assert P re rh (update_env ghe id v)
  | Adefined id =>  ~ find re id = None
  | Agdefined id =>  ~ find ghe id = None
  | Aalloc p => exists adr,
    find ghe p = Some (RV (Vptr adr)) /\  
    ~ rh adr = None
  | (UPDATE p v h2)%assert =>
    exists p_ v_ h2_,
    find ghe p = Some (RV (Vptr p_)) /\
    find ghe v = Some (RV v_) /\
    find ghe h2 = Some (GV (GVheap h2_)) /\
    h2_ = update_heap rh p_ (Some v_)
  | Aexists_heap P =>
    exists rh',
    eval_assert P re rh' ghe
  | Aequal_heap xh =>
    exists xh_,
    find ghe xh = Some (GV (GVheap xh_)) /\
    rh = xh_
  | Aexpr_type ex ty =>
  expr_type ex re rh ty
    (*exists v, eval_expr ex re rh v /\ val_type rh v ty *)
  | Agexpr_type ex ty => gexpr_type ex re rh ghe ty
  | Aref_eq ex1 ex2 =>
    exists v,
    eval_glvalue ex1 re rh ghe v /\
    eval_gexpr ex2 re rh ghe (Vptr v)
  | Aeq ex1 ex2 =>
    exists v,
    eval_gexpr ex1 re rh ghe v /\
    eval_gexpr ex2  re rh ghe v
  end.

Notation "[ e , h , ghe ] |= P" :=  (eval_assert P e h ghe) (format "[ e ,  h ,  ghe ] |=  P", at level 9, right associativity).
(*
Global Instance Proper_eval_assert: Proper ( Logic.eq ==> env_equiv ==> Logic.eq ==> Logic.iff) eval_assert.
Proof.
  intros ? ? ? ? ? ? ? ? ?; subst.
  revert x0 y0 H0 y1.
  induction y;
    try solve[intros; split;auto]; (*solves trivial*)
    simpl; intros;
      try solve[rewrite H0; reflexivity]; (*solves simple*)
  try solve [repeat match goal with
                    | [ H': ?pred _ _ , H: forall _ _, ?pred _ _ -> _ |- _ ] => specialize (H _ _ H')
                    end; firstorder]. (*solves non quantifiers*)
  - cut (forall v,
            option_val_type v t0 /\ [ (update_env x0 i v), y1] |= y <->
            option_val_type v t0 /\ [ (update_env y0 i v), y1] |= y).
    { intros AA; split; intros [v [? BB]]; exists v; apply AA; auto. }
    intros v.
    rewrite IHy; [reflexivity|f_equiv; assumption].

    (*
  - cut (forall adr v,
      (find x0 i = Some (Vptr adr) /\ (eval_expr e x0 y1 v /\ y1 adr = Some v)) <->
      (find y0 i = Some (Vptr adr) /\ (eval_expr e y0 y1 v /\ y1 adr = Some v))).
    { intros HH; split; intros [adr [? [v ?]]];
        do 2 econstructor; try eexists; rewrite H0 in *; eauto.  }
    intros; split; intros; repeat rewrite H0 in *; assumption.
    *)
  - split; intros [v []]; do 2 econstructor;
      rewrite H0 in *; eassumption.
Qed.
*)

(* Obligations are formulas of the form phi ||= phi', which are passed to the SMT to verify. *)
(* The semantics of obligations is given by entailments *)

Notation obligations:= (list (assertion * assertion)).
Definition assert_entails P Q:=
  forall (e:renv) (h: heap)(ghe:genv), [e, h, ghe] |= P -> [e, h, ghe] |= Q.
Notation "P ||= Q" :=  (assert_entails P Q) (at level 20, right associativity).
Definition assertion_entailment (entailment:assertion * assertion): Prop :=
  let (P,Q):= entailment in P ||= Q.

(*A verified list of obligations is defined thusly: *)
Fixpoint list_entailment (entailments: list (assertion * assertion)): Prop :=
  match entailments with
    nil => True
  | ent::ents => assertion_entailment ent /\ list_entailment ents
  end.
Lemma list_entailment_app:
  forall ls1 ls2,
    list_entailment (ls1 ++ ls2) <->
    list_entailment ls1 /\ list_entailment ls2.
Proof.
  induction ls1.
  - simpl; tauto.
  - simpl; intros; split;
      rewrite and_assoc.
    rewrite IHls1; auto.
    intros [? []]; split; auto.
    apply IHls1; auto.
Qed.

(** *Tactics *)
Ltac destruct_list_entailment:=
  repeat match goal with
         | [ H: list_entailment (_ :: _)  |- _ ] =>
           cbn delta[list_entailment] iota beta in H; destruct H
         | [ H: list_entailment (_ ++ _)  |- _ ] =>
           rewrite list_entailment_app in H; destruct H
         end.
Ltac reduce_list_entailment:=
  repeat match goal with
         | [ |- list_entailment (_ :: _) ] =>
           cbn delta[list_entailment] iota beta; split
         | [ |- list_entailment (_ ++ _) ] =>
           rewrite list_entailment_app; split
         end.

Ltac pre_entailer:=
  match goal with
  | [  |- forall _:renv, forall _ : heap, forall _ : genv, _ ] =>
    let e := fresh "e" in
    let h := fresh "h" in
    intros e h ghe;
    repeat match goal with
           | [ H:  forall _:renv, forall _ : heap, forall _ : genv,  _  |- _ ] => specialize (H e h ghe)
           end
  | [  |- eval_assert _ ?e ?h ?ghe  ] =>
    repeat match goal with
           | [ H:  forall _:renv, forall _ : heap, forall _ : genv, _  |- _ ] => specialize (H e h ghe)
           end
  end.
Ltac entailer:= 
  simpl in *;
  unfold assert_entails in *;
  simpl in *;
  destruct_and;
  reduce_and;
  destruct_list_entailment;
  reduce_list_entailment;
  repeat match goal with
         | [  |- _ /\ _ ] => split 
         end;
  try pre_entailer;
  tauto.


Section FreeFreshVars.
  (** 
   Free variables and fresh variables for assertions:
   Free variables are all ID's in the assertions that are not bound
   to a quantifier.
   Fresh variables are variables not in the fresh set. 
   *)
  (** THIS IS ONLY ABOUT TEMPORAL LOCAL VARIABLES*)
  Definition fresh_var (set_vars:PSet.t): positive:=
    match (max_elt set_vars) with
    | Some x => x~1
    | None => 1
    end.

  (* Simplify hypothesis of the form context[In x s] *)
  Ltac simpl_set HH:=
    repeat first
           [rewrite union_spec in HH |
            rewrite singleton_spec in HH];
    normal_form_not_or.

  (* Simplify goal of the form [~ In x s] *)
  Ltac reduce_in_set:=
    repeat first[ rewrite union_spec;
                  try (eapply Classical_Prop.and_not_or; split)|
                  rewrite singleton_spec ].
  
  Fixpoint free_vars (A: assertion): PSet.t:= (*returns a set od positives*)
    match A with
    | Atrue | Afalse=> empty
    | Aand A1 A2 => union (free_vars A1) (free_vars A2)
    | Aor A1 A2 => union (free_vars A1) (free_vars A2)
    | Anot A' => free_vars A'
    | Aexists id A' => (free_vars A')
    | Agexists x A' => PSet.remove x (free_vars A')
    | Adefined id => empty
    | Agdefined id => singleton id
    | Aalloc p => singleton p
    | (UPDATE p v h2)%assert => union (singleton p) (union (singleton v) (singleton h2))
    | Aexists_heap A' => free_vars A'
    | Aequal_heap xh => singleton xh
    | Aexpr_type e _ => empty
    | Agexpr_type ex _ => free_vars_expr ex
    | Aref_eq ex1 ex2 => union (free_vars_expr ex1) (free_vars_expr ex2)
    | Aeq ex1 ex2 => union (free_vars_expr ex1) (free_vars_expr ex2)
    end.

  Definition env_equiv_assert (P:assertion): relation genv:=
    fun e1 e2 =>
      forall x, PSet.In x (free_vars P) ->
           (find e1 x) = (find e2 x).

  Global Instance Equivalenc_env_equiv_assert:
    forall ass, Equivalence (env_equiv_assert ass).
  Proof.
    constructor.
    - constructor.
    - intros ? ? H ? ?. rewrite H; auto.
    - intros ??? H1 H2 ??. rewrite H1, <- H2; auto.
  Qed.

  Lemma env_equiv_equiv:
    forall e1 e2 ex,
      env_equiv e1 e2 ->
      env_equiv_assert ex e1 e2.
  Proof. intros ? ? ? H ? ?; apply H. Qed.

  Lemma free_vars_env_equiv_assert:
    forall P k e,
      ~ PSet.In k (free_vars P) ->
      forall ov,
        env_equiv_assert P (update_env e k ov) e.
  Proof.
    induction P; intros ? ? ? ? ? ?;
                        destruct (peq k x); subst;
      try tauto;
      rewrite gso; auto.
  Qed.

  Global Instance Proper_eval_assert_assert:
    forall ass, Proper (env_equiv ==> Logic.eq ==> env_equiv_assert ass ==> Logic.iff)
                  (eval_assert ass).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ?; subst.
    revert y0 x y H x1 y1 H1.
    induction ass; intros;
      try solve[split;auto];
      simpl; intros;
        try solve[
              repeat match goal with
                     | [ H: context[ _ <-> _ ] |- _ ] =>
                       rewrite H; clear H
                     end; eauto;
              try reflexivity;
              match goal with
              | [ H: env_equiv_assert _ _ _  |- env_equiv_assert _ _ _ ] =>
                intros ? ?; apply H;
                simpl; try rewrite PSet.union_spec; auto
              end];
        try (apply forall_exists_iff); intros. (*8 goals left*)
    - eapply IHass; auto; rewrite H; reflexivity.
    - eapply IHass; auto.
      intros x' ?; destruct (peq i x'); subst;
        try do 2 rewrite gss by auto;
        try do 2 rewrite gso by auto; auto.
      eapply H1. simpl.
      apply PSet.remove_spec; split; auto.
    - try rewrite H; try rewrite H1; reflexivity.
    - try rewrite H; try rewrite H1. reflexivity.
      apply singleton_spec; reflexivity.
    - try rewrite H; try rewrite H1. reflexivity.
      apply singleton_spec; reflexivity.
    - repeat (apply forall_exists_iff; intros).
      repeat rewrite H1; try reflexivity;
        clear; simpl;
          repeat (try rewrite union_spec; try rewrite singleton_spec); tauto.
    - apply IHass; auto.
    - rewrite H1; simpl; try apply singleton_spec; reflexivity.
    - rewrite H; reflexivity.
    - rewrite H; rewrite H1; reflexivity.

    - assert (HH: env_equiv_gexpr g x1 y1).
      { intros ? ?. eapply H1. simpl. apply PSet.union_spec; auto. }
      assert (HH': env_equiv_gexpr g0 x1 y1).
      { intros ? ?. eapply H1. simpl; apply PSet.union_spec; auto. }
      intros; f_equiv; rewrite H;
        try rewrite HH; try rewrite HH'; reflexivity.

    - assert (HH: env_equiv_gexpr g x1 y1).
      { intros ? ?. eapply H1. simpl. apply PSet.union_spec; auto. }
      assert (HH': env_equiv_gexpr g0 x1 y1).
      { intros ? ?. eapply H1. simpl; apply PSet.union_spec; auto. }
      
      intros; f_equiv; rewrite H;
        try rewrite HH; try rewrite HH'; reflexivity.

  Qed.

  Lemma fresh_var_spec:
    forall set_vars,
      ~ PSet.In (fresh_var set_vars) set_vars.
  Proof.
    intros.
    cbv delta[fresh_var] beta iota zeta; intros AA.
    destruct (max_elt set_vars) eqn:BB.
    - eapply PSet.max_elt_spec2 in BB; eauto.
      apply BB; eauto.
      simpl.
      unfold elt in *.
      clear.
      induction e; simpl ; auto.
    - apply PSet.max_elt_spec3 in BB.
      eapply BB; eauto.
  Qed.

  (*Usefull case for assignment case*)
  Lemma fresh_vars_spec_util:
    forall phi x ex,
      let temp:=
          fresh_var (union (free_vars phi)
                           (union (free_vars_expr ex) (singleton x)))  in
      ~ PSet.In temp (free_vars phi) /\
      ~ PSet.In temp (free_vars_expr ex) /\
      temp <> x.
  Proof.
    intros.
    pose proof (fresh_var_spec (union (free_vars phi) (union (free_vars_expr ex) (singleton x)))). 
    do 2 rewrite PSet.union_spec in H.
    apply Classical_Prop.not_or_and in H; destruct H as [A H].
    apply Classical_Prop.not_or_and in H; destruct H as [B C].
    split; auto.
    split; auto.
    intros HH; apply C.
    rewrite PSet.singleton_spec; auto.
  Qed.

  Lemma expr_type_update:
    forall k gex,
      ~ PSet.In k (free_vars_expr gex) -> 
      forall e h ghe ty v_ty, gexpr_type gex e h (update_env ghe k v_ty) ty <->
                         gexpr_type gex e h ghe ty.
  Proof.
    intros; eapply free_vars_env_equiv in H; rewrite H; reflexivity.
  Qed.

  Lemma eval_expr_update:
    forall k gex,
      ~ PSet.In k (free_vars_expr gex) -> 
      forall e h ghe v v', 
        eval_gexpr gex e h (update_env ghe k v') v <->
        eval_gexpr gex e h ghe v.
  Proof.
    intros; eapply free_vars_env_equiv in H; rewrite H; reflexivity.
  Qed.

  Lemma free_vars_update:
    forall k phi,
      ~ PSet.In k (free_vars phi) -> 
      forall e h ghe v, 
        eval_assert phi e h (update_env ghe k v) <->
        eval_assert phi e h ghe.
  Proof.
    intros; eapply free_vars_env_equiv_assert in H; rewrite H; reflexivity.
  Qed.

End FreeFreshVars.


(** *Tactics: simplifing and solving fresh/free variables goals/hypothesis*)

(* Solves goals of the form [fresh_var ?st <> _ ] *)
Ltac solve_fresh_var_neq':=
  match goal with
  | [ |- fresh_var ?st <> _ ] =>
    let HH := fresh "HH" in
    pose proof (fresh_var_spec st) as HH;
    simpl_set HH; assumption
  end.
Ltac solve_fresh_var_neq:=
  first [solve_fresh_var_neq' | symmetry; solve_fresh_var_neq'].

(* simplifies goal and hypothesis of the form [find _ _ = Some _] *)
(* It replaces subst_find*)
Ltac simpl_find :=
  repeat match goal with
         | [ H: find ?e ?x = Some _, H': find ?e ?x = Some _  |- _ ] =>
           rewrite H in H'; invert H'
         | [  |- find _ _ = _ ] =>
           first [ rewrite gss | rewrite gso by solve_fresh_var_neq]
         | [ H: find _ _ = Some _  |- _ ] =>
           first [ rewrite gss in H | rewrite gso in H by solve_fresh_var_neq]
         end.

(* solves goals of the forma [~ In (fresh_var s1) s2] when s2 < s1*)
Ltac fresh_var_subset:=
  match goal with
  | [ |- ~ PSet.In (fresh_var ?st) _ ] =>
    let HH := fresh "HH" in
    pose proof (fresh_var_spec st) as HH;
    simpl_set HH;
    reduce_in_set; assumption
  end.

(* solves goals of the form [~ In x s] *)
Ltac solve_in_set:=
  solve [ simpl; reduce_in_set;
          first[ apply empty_spec
               | solve[rewrite singleton_spec; solve_fresh_var_neq]
               | solve[apply fresh_var_spec]
               | fresh_var_subset] ].


(* Simplify the ghost environment in expressions   *)
Ltac simpl_free_vars_env_equiv:=
  progress (repeat
              first[ rewrite free_vars_env_equiv by solve_in_set |
                     rewrite update_comm by solve_fresh_var_neq;
                     rewrite free_vars_env_equiv by solve_in_set |
                     rewrite redundant_update ]).
Ltac simpl_free_vars_env_equiv_hyp H:=
  progress (repeat
              first[ rewrite free_vars_env_equiv in H by solve_in_set |
                     rewrite update_comm in H by solve_fresh_var_neq;
                     rewrite free_vars_env_equiv in H by solve_in_set |
                     rewrite redundant_update]).

(*will try to use commutativity once. *)
Ltac simpl_env_gexpr:=
  repeat match goal with
         | [  |- eval_gexpr _ _ _ _ _ ] =>
           simpl_free_vars_env_equiv
         | [  |- eval_glvalue _ _ _ _ _ ] => 
           simpl_free_vars_env_equiv
         | [ H: eval_gexpr _ _ _ _ _  |- _ ] => 
           simpl_free_vars_env_equiv_hyp H
         | [ H: eval_glvalue _ _ _ _ _  |- _ ] => 
           simpl_free_vars_env_equiv_hyp H
         end.

(* Simplify the ghost environment in assertions*)
Ltac simpl_free_vars_env_equiv_assert:=
  progress (repeat
              first[ rewrite free_vars_env_equiv_assert by solve_in_set |
                     rewrite update_comm by solve_fresh_var_neq;
                     rewrite free_vars_env_equiv_assert by solve_in_set |
                     rewrite redundant_update |
                     rewrite pointless_update by reflexivity ]).
Ltac simpl_free_vars_env_equiv_assert_hyp H:=
  progress (repeat
              first[ rewrite free_vars_env_equiv_assert in H by solve_in_set |
                     rewrite update_comm in H by solve_fresh_var_neq;
                     rewrite free_vars_env_equiv_assert in H by solve_in_set|
                     rewrite redundant_update in H |
                     rewrite pointless_update in H by reflexivity]).

(** * Some tactics (worth moving some) *)
Ltac simpl_env_assertion:=
  repeat match goal with
         | [  |- eval_assert _ _ _ _ ] =>
           simpl_free_vars_env_equiv_assert
         | [ H: eval_assert _ _ _ _ |- _ ] =>
           simpl_free_vars_env_equiv_assert_hyp H
         end.
Ltac solve_assertion_subgoal:=
  first [ assumption |
          solve[ simpl_env_gexpr; trivial] |
          solve [simpl_find; trivial] |
          solve [simpl_env_assertion; entailer] ].
Ltac solve_assertion:=
  first [ solve_assertion_subgoal |
          (* This second part should be replaced by gexpr_entailer*)
          try destruct_eval_gexpr;
          econstructor; solve_assertion_subgoal].