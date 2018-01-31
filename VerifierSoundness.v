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
Require Import VCC.Syntax.
Require Import VCC.Semantics.
Require Import VCC.Assertions.
Require Import VCC.ExpressionVerifier.
Require Import VCC.VerifierProgram.

Import Expressions.

(** *Verifier Soundness*)
(* Proof that verification implies safety*)
(* Final theorem is verifier_correctness*)

Lemma expr_type_wt:
  forall (ex : expr) (e : renv) (h : heap) ty,
    expr_type ex e h ty -> wt_expr ex ty.
Proof.
  induction ex; intros; destruct_expr_type; auto.
  split; auto.
  eapply IHex; eauto.
  (*binop*) subst; do 2 eexists; split; eauto.
Qed.

(*
  EVALex : eval_expr ex e h v
  BOOLval : bool_val v ty = Some b
  ============================
  [e, h, ghe]|= (if b then bool_true ex else bool_false ex)

 *)
Lemma eval_expr_bool_spec:
  forall (ex:expr) e h ghe (v:val) b,
    eval_expr ex e h v ->
    bool_val v = Some b ->
    [e, h, ghe]|= (if b then (bool_true ex) else (bool_false ex)) .
Proof.
  intros; simpl in *.
  destruct v; inversion H0.
  destruct (Int.eq i Int.zero) eqn:Niz.
  - apply int_eq_iff in Niz; subst.
    + eexists; split; econstructor; eauto. econstructor.
  - split.
    + intros [v []].
      destruct_eval_gexpr;
        destruct_eval_expr; subst.
      * eapply int_neq_iff; try reflexivity; eauto.
      * simpl_find; eapply int_neq_iff; try reflexivity; eauto.
      * (*binop*)
        pose proof (eval_expr_functional _ _ _ _ _ H0 H5) as HH';
          invert HH'.
        pose proof (eval_expr_functional _ _ _ _ _ H1 H6) as HH''; invert HH''.
        rewrite H7 in H3; invert H3.
        eapply int_neq_iff; try reflexivity; eauto.
      * pose proof (eval_expr_functional _ _ _ _ _ H1 H3) as HH';
          invert HH'.
        pose proof (deref_loc_functional _ _ _ _ H0 H2) as HH''; invert HH''.
        eapply int_neq_iff; try reflexivity; eauto.
        
      * assert (HH': (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
        invert HH'.
        eapply int_neq_iff in Niz; apply Niz.
        cut (Vint i = val_zero).
        { intros HH0; injection HH0; auto. }
        { eapply deref_loc_functional; eauto. }
    + (*Show that it evaluates to an int*)
      exists (Some (RV (Vint i))); split.
      * exists ((Vint i)); repeat split.
        simpl_find; auto.
      * exists ((Vint i)). split.
        -- econstructor. simpl_find; reflexivity.
        -- simpl_env_gexpr; constructor; auto.
Qed. 


(** The proof runs by induction on the program. 
    Through the execution we mantain the following 
    invariant, where the existentially quantified phi
    represents the knowledge about the current state. *)
Definition invariant (st:state):=
  match st with
  | State stm k e h ghe =>
    exists phi,
    eval_assert phi e h ghe /\
    list_entailment (weakest_precondition_stm phi stm (get_loop_invariants k))  /\
    list_entailment (weakest_precondition_cont (strongest_post phi stm) k)
  | GState stm k e h ghe => 
    exists phi,
    eval_assert phi e h ghe /\
    list_entailment (weakest_precondition_gstm phi stm)  /\
    list_entailment (weakest_precondition_cont (strongest_post_ghost phi stm) k)
  end.

(*Tactic for preservation of invariant *)
Ltac destruct_inv:=
  match goal with
  | [ H: invariant _ |- _ ] =>
    let phi := fresh "phi" in
    let phi_OK := fresh "phi_OK" in
    let stm_entail := fresh "stm_entail" in
    let cont_entail := fresh "cont_entail" in
    destruct H as [phi [phi_OK [stm_entailment cont_entailment]]];
    simpl in stm_entailment, cont_entailment;
    try rewrite  list_entailment_app in *;
    destruct_and; auto
  end.
Ltac trivial_invariant:=
  destruct_inv; eexists;
  cbn delta[weakest_precondition_cont weakest_precondition_stm list_entailment] iota beta;
  try rewrite list_entailment_app;
  split; [|split]; eauto.

Ltac easy_invariant I:=
  destruct_inv; exists I; entailer.

(** *Preservation *)
(*Begin with the hardest cases*)
(* 1) sequence *)
Lemma seq_preservation:
  forall e h ghe k s1 s2,
    invariant (State (Sseq s1 s2) k e h ghe) ->
    invariant (State s1 (Kseq s2 k) e h ghe).
Proof.
  intros.
  trivial_invariant.
Qed.

(* 2) Set *)
Ltac expr_entailer:=
  match goal with
  | _ => assumption
  | [ |- eval_expr (Etempvar ?x _) (update_env _ ?x' ?v) _ ?v' ] =>
    match x with
      x' =>
      (*should I check v' = Some v ?*)
      solve [econstructor; rewrite gss; auto]
    end
  | [ |- eval_expr (Etempvar ?x' _) (update_env _ ?temp' _) _ _ ] =>
    fail (* rewrite expr_equiv_tempvar by (first [assumption|symmetry; assumption])  *)
  | [  |- eval_expr ?ex ?e _ _ ] =>
    match goal with
    | [ H: ~ PSet.In ?temp (free_vars_gexpr ex) |- _ ] =>
      match e with
        context [update_env _ temp _] =>
        repeat (
            first[
                rewrite (update_comm _ temp) by (first [assumption|symmetry; assumption])|
                rewrite <- (update_comm _ _ temp) by  (first [assumption|symmetry; assumption])
              ]
          );
        rewrite free_vars_env_equiv by exact H
      end
    end
  | _ => rewrite redundant_update
  | _ => rewrite pointless_update by reflexivity
  end.

Ltac gexpr_entailer:=
  try simpl_env_gexpr;
  first [
      solve 
        [constructor; repeat expr_entailer] |
      solve   [econstructor; simpl_find; auto] |
      idtac  ].


(*Trying to depricate this. Might want to include parts of this in solve_assertions*)
Ltac solve_assert:=
  match goal with
  | _ => assumption
  | [  |- eval_assert ?P ?e _ ] =>
    match goal with
    | [ H: ~ PSet.In ?temp (free_vars P) |- _ ] =>
      match e with
        context [update_env _ temp _] =>
        repeat (
            first[
                rewrite (update_comm _ temp) by (first [assumption|symmetry; assumption])|
                rewrite <- (update_comm _ _ temp) by  (first [assumption|symmetry; assumption])
              ]
          ); rewrite free_vars_env_equiv_assert by exact H
      end
    end 
  | [  |- eval_assert Atrue _ _] => constructor
  | [  |- eval_assert (Aand _ _) _ _ ] => split
  | [  |- eval_assert (Aor _ _) _ _ ] => first[solve[left; solve_assert] | solve[right; solve_assert]]
  | [  |- eval_assert (Aexists _ _ _) _ _ ] => eexists; split
  | [  |- eval_assert (Aeq _ _) _ _] => eexists; split; solve[repeat expr_entailer]
  | _ => rewrite redundant_update
  | _ => rewrite pointless_update by reflexivity 
  end.


Lemma set_preservation:
  forall e h ghe x ex k v,
    invariant (State (Sset x ex) k e h ghe) ->
    (* get_type e x = Some ty \/ get_type e x = None -> *)
    eval_expr ex e h v ->
    invariant (State Sskip k (update_env e x (Some v)) h ghe).
Proof.
  intros ? ? ? ? ? ? ? H1 H2.
  destruct_inv.
  pose proof (fresh_vars_spec_util phi x ex) as HH;
    destruct HH as [Fresh1 [Fresh2 Fresh3]].
  remember (fresh_var (union (free_vars phi) (union (free_vars_gexpr ex) (singleton x))))
    as temp.
  exists (strongest_post phi (Sset x ex)).
  (*This should be reformulated and maybe turn into lemma*)
  split; [|split].
  - repeat (first [eexists | split]);
      gexpr_entailer.
    
    
    simpl_env_gexpr.

    solve_assertion.

  - simpl; tauto.
  - simpl in *. assumption.
Qed.

Lemma assign_preservation:
  forall e h ghe ex1 ex2 k v addr,
    invariant (State (Sassign ex1 ex2) k e h ghe) ->
    (* get_type e x = Some ty \/ get_type e x = None -> *)
    eval_lvalue ex1 e h addr ->
    eval_expr ex2 e h v ->
    invariant (State Sskip k e (upd_heap h addr v) ghe).
Proof.
  intros ? ? ? ? ? ? ? addr H H0 ?.
  destruct_inv.
  duplicate phi_OK.
  apply H in phi_OK.
  destruct phi_OK as (?&?&?&?).
  clear H H2.
  exists (strongest_post phi (Sassign ex1 ex2)).
  split; [|split].
  - repeat (first [eexists | split]);
      gexpr_entailer.
    + simpl_find; reflexivity.
      
    + simpl_find.
      unfold upd_heap.
      instantiate (2:=addr).
      replace (add_eq addr addr) with true.
      reflexivity.
      symmetry.
      eapply (add_deq_true addr addr); auto.
    + apply upd_heap_gss.
    + simpl_find; reflexivity.
    + apply lvalue_glvalue; eauto.
    + apply eval_expr_gexpr; eauto.
    + simpl_find; reflexivity.
    + simpl_find; reflexivity.
    + simpl_find; reflexivity.
    + solve_assertion.
      
  - simpl; tauto.
  - simpl in *. assumption.

Qed.


(* 4) Ifthenelse*)

Lemma ifthenelse_preservation:
  forall e h ghe k ex v s1 s2 b,
    invariant (State (Sifthenelse ex s1 s2) k e h ghe) ->
    eval_expr ex e h v ->
    (* expr_type ex e h Tint -> *)
    bool_val v = Some b ->
    invariant (State (if b then s1 else s2) k e h ghe).
Proof.
  intros until b;
    intros [phi [phi_OK [stm_entailments cont_entailments]]] EVALex BOOLval.
  unfold invariant.
  exists ((if b then (bool_true ex) else (bool_false ex)) /\ phi)%assert.
  split; [|split].
  - split; auto.
    destruct stm_entailments as [? HH];
      apply list_entailment_app in HH; destruct HH.
    pose proof (eval_expr_bool_spec ex e h ghe _ _ EVALex BOOLval);
      eauto.
  - simpl in stm_entailments.
    destruct stm_entailments as [? HH];
      apply list_entailment_app in HH; destruct HH.
    destruct b; auto.
  - simpl in cont_entailments.
    eapply list_entailment_weakening; eauto.
    clear.
    destruct b; entailer.
Qed.

(* 5) Ghost set*)
Lemma GSet_preservation:
  forall (ex : gexpr) (x : ident) (k : cont) (e : renv) (ghe : genv) (h : heap),
    invariant (GState (GSset x ex) k e h ghe) ->
    forall v : uval,
      eval_gexpr ex e h ghe v ->
      step (GState (GSset x ex) k e h ghe)
           (GState GSskip k e h (update_env ghe x (Some v))) ->
      invariant (GState GSskip k e h (update_env ghe x (Some v))).
Proof.
  intros until h.
  intros [phi [phi_OK [stm_entailments cont_entailments]]] VAL GEVAR STEP.
  unfold invariant.
  exists (strongest_post_ghost phi (GSset x ex)).
  split; [|split].
  - repeat (first [eexists | split]);
      gexpr_entailer.
    + rewrite pointless_update by reflexivity; assumption.
    + solve_assertion.
  - simpl; tauto.
  - simpl in *. assumption.
Qed.


Lemma step_preservation:
  forall st st',
    step st st' ->
    invariant st ->
    invariant st'.
Proof.
  intros.
  inversion H; subst; try solve [trivial_invariant].

  - trivial_invariant;
      eapply list_entailment_weakening; eauto; entailer.
  - trivial_invariant;
      eapply list_entailment_weakening; eauto; entailer.
  - eapply set_preservation; eauto.

  - (*Assign*)
    eapply assign_preservation; eauto.
    
  (*Conditional *)
  - eapply ifthenelse_preservation; eauto.
  (* destruct_inv. eapply H0 in phi_OK.
    destruct_and; auto.
    destruct phi_OK.
    rename e into ex. *)
    
  (*Loops *)
  - easy_invariant I1.
  - destruct H1; subst; easy_invariant I1.
  - easy_invariant I2.
  - easy_invariant I1.
  - easy_invariant I2.

  (*Pure logical steps*)
  - destruct_inv.
    exists (Aand P phi); entailer.
  - destruct_inv.
    exists (Aand P phi); entailer.
  - (*Ghost step *)
    eapply GSet_preservation; eassumption.
    
Qed.


Lemma star_preservation:
  forall st st',
    step_star st st' ->
    invariant st ->
    invariant st'.
Proof.
  intros ? ? STAR.
  dependent induction STAR; auto.
  intros IH; apply IHSTAR in IH; clear IHSTAR.
  eapply step_preservation; eauto.
Qed.

(*The following lemma is loosely the progress lemma*)
(*In some sense, safe states are the ones that can step*)
Lemma state_invariant_safety:
  forall stm k e h ghe,
    invariant (State stm k e h ghe) ->
    safe_state (State stm k e h ghe).
Proof.
  intros; destruct_inv.
  destruct stm; try solve[econstructor].
  - (*set*)
    simpl in stm_entailment.
    destruct stm_entailment as [? _].
    eapply H in phi_OK.
    (*    cbv delta[eval_assert] iota zeta beta in phi_OK;
      destruct_and; fold eval_assert in H. *)

    eapply expr_defined_safe in phi_OK; destruct phi_OK.
    econstructor; eauto.
  - (*Assign*)
    simpl in stm_entailment.
    destruct stm_entailment as [? _].
    eapply H in phi_OK.
    destruct phi_OK as (?&?&?&?).
    destruct e0; try solve[inversion H1].
    (*For leval e0*)
    simpl in H1, H2.
    destruct H1 as (? &?&?&?).
    destruct H2 as (? &?&?).
    invert H2.
    clear H cont_entailment.
    (*For eval_expr e1*)
    eapply expr_defined_safe in H0.
    destruct H0 as (?&H0).
    
    econstructor.
    + econstructor.
      repeat fold_eval_expr.
      eassumption.
    + eassumption.
      
  - (*Conditional*)
    simpl in stm_entailment.
    destruct_and; destruct_list_entailment.
    eapply H in phi_OK as (expr_OK&IS_BOOL).
    eapply expr_defined_safe in expr_OK as (?&?).

    (* simpl in IS_BOOL.
    destruct (tint_is_bool _ _ _ _ IS_BOOL H2).  *)
    destruct IS_BOOL as (ov & (v1 & ? & ?) & (v2 & ? & ?)).
    simpl_find.
    pose proof (eval_gexpr_functional _ _ _ _ _ x H6 ltac:(econstructor;assumption)); subst.
    clear H6.
    destruct_eval_gexpr; simpl_find.
    inversion H2; subst.
    destruct x; try solve[inversion H4].
    econstructor; try eassumption.
    simpl; reflexivity.
    
  - (* break *)
    simpl in *; destruct_and.
    destruct k; 
      simpl in cont_entailment;
      destruct_list_entailment; destruct_and;
        try solve[constructor].
    + apply H in phi_OK; contradiction.
    + (* Remember that break cannot appera inside a ghost statement *)
      (* GKseq happens only in the middle of executing ghost code   *)
      apply H in phi_OK; inversion phi_OK.
      
  - (* continue *)
    simpl in *; destruct_and.
    destruct k; 
      simpl in cont_entailment;
      destruct_and;
      destruct_list_entailment;
      try solve[constructor].
    + apply H in phi_OK; contradiction.
    + constructor; auto.
    +  apply H in phi_OK; contradiction.
    + (* Remember that continue cannot appera inside a ghost statement *)
      (* GKseq happens only in the middle of executing ghost code   *)
      apply H in phi_OK; inversion phi_OK.
  - simpl in stm_entailment.
    destruct stm_entailment; eauto.
    econstructor; eauto.
Qed.
Lemma gstate_invariant_safety:
  forall stm k e h ghe,
    invariant (GState stm k e h ghe) ->
    safe_state (GState stm k e h ghe).
Proof.
  intros; destruct_inv.
  destruct stm; try solve[econstructor].
  (*GSet*)
  simpl in stm_entailment.
  destruct stm_entailment as [? _].
  eapply H in phi_OK.
  apply gexpr_defined_safe in phi_OK as (?&?).
  econstructor; eassumption.
Qed.


Lemma star_safety:
  forall st, invariant st ->
        forall st', step_star st st' -> safe_state st'.
Proof.
  intros.
  destruct st'.
  - apply state_invariant_safety.
    apply star_preservation with st; auto.
  - apply gstate_invariant_safety.
    apply star_preservation with st; auto.

Qed.

Section VerificationSafety.
  
  Context (verified_program: cont)
          (program_obligations: obligations)
          ( Precondition: assertion)
          (program_verified: weakest_precondition_cont Atrue verified_program = program_obligations)
          (verifier_guaranty: list_entailment program_obligations).
  
  
  Lemma initial_invariant:
    invariant (State Sskip verified_program empty_env empty_heap empty_env).
  Proof.
    exists Atrue. repeat (split; auto).
    cbv [strongest_post].
    rewrite program_verified.
    apply verifier_guaranty.
  Qed.
  
  
  Theorem verifier_correctness:
    Safe (State Sskip verified_program empty_env empty_heap empty_env). 
  Proof.
    intros st' step.
    eapply star_safety with
        (State Sskip verified_program empty_env empty_heap empty_env); auto.
    apply initial_invariant.
  Qed.

End VerificationSafety.
