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
Require Import VCC.ExpressionVerifier.
Import Expressions.




    
(** * Sintactic evaluator*)
(* Evaluates a continuation and outputs the obligations necessary to verify the program*)
Section Evaluator.
  

(*The follwing determine if an expression is true or false*)
(*FIXEME: Resolve the missing cases (comparing pointers?) *)
Definition bool_true (ex:expr):assertion:=
  (~ Econst_int Int.zero  == ex /\ Aexpr_type ex Tint)%assert.
Definition bool_false (ex:expr):assertion:=
  (Econst_int Int.zero  == ex /\ Aexpr_type ex Tint)%assert.

(*Minimal weakest pre is the minimal requirements to take a step. *)
(*This is different to the weakes_pre that allows to continue execution.*)
Fixpoint ghost_minimal_weakest_pre (gstm:gstatement)(*Postcondition = True*) :assertion:= (*weakest liberal precondition*)
  match gstm with
  | GSskip => Atrue
  | GSset id ex => (assert_gexpr_defined ex)%assert
  | GSseq gs1 _ => ghost_minimal_weakest_pre gs1
  end.

(*weakest liberal precondition*)
Fixpoint minimal_weakest_pre_ghost (gstm:gstatement):assertion:=
  match gstm with
  | GSskip => Atrue
  | GSset _ ex => (assert_gexpr_defined ex)%assert
  | GSseq x _ => minimal_weakest_pre_ghost x
  end.

Fixpoint minimal_weakest_pre (stm:statement)(*Postcondition = True*) :assertion:= (*weakest liberal precondition*)
  match stm with
    Sskip => Atrue
  | Sset id ex => (assert_expr_defined ex)%assert
  | Sassign ex1 ex2 =>
    ( assert_expr_defined ex2 /\
      assert_lvalue_defined ex1 /\
      let p:= fresh_var (free_vars_expr ex1) in
      Aalloc p /\
      Agexists p (Aref_eq ex1 (GEtempvar p) )
     )%assert
  | Sseq x x0 => minimal_weakest_pre x
  | Sifthenelse ex s1 s2 =>
    (*Tint??!! should be bool?? *)
    ((assert_expr_defined ex) /\ Aexpr_type ex Tint)%assert  
  | Sloop  I1 I2  s1 s2 => I1
  | Sbreak => Atrue
  | Scontinue => Atrue
  | Sghost gstm => minimal_weakest_pre_ghost gstm
  | Sassert P => P
  | Sassume P => Atrue
  end.

Notation obligations:= (list (assertion * assertion)).

(* Equivalent to strongest_post *)
Fixpoint strongest_post_ghost (phi:assertion)(gstm:gstatement): assertion:=
  match gstm with
  | GSskip => phi
  | GSset x ex => 
    let temp:= fresh_var
                 (union (free_vars phi)
                        (union (free_vars_expr ex) (singleton x)))  in
    Agexists temp
             ((GEtempvar x == GEtempvar temp) /\
              (Agexists x ((GEtempvar temp == ex) /\
                           phi)))%assert
  | GSseq stm1 stm2 => strongest_post_ghost (strongest_post_ghost phi stm1) stm2
  end.

Fixpoint strongest_post (phi:assertion)(stm:statement): assertion:=
  match stm with
  | Sskip =>  phi
  | Sset x ex => (* id = expr*)
    (*Ex. temp. x=temp /\ Ex. x.  temp = e /\ P*)
    let temp:= fresh_var
                 (union (free_vars phi)
                        (union (free_vars_expr ex) (singleton x)))  in
    Agexists temp
             ((Etempvar x == GEtempvar temp) /\
              (Aexists x ((GEtempvar temp == ex) /\
                          phi)))%assert
  | Sassign ex1 ex2 =>
    let h_temp:= fresh_var (free_vars phi) in
    let v:= fresh_var
              (union (singleton h_temp)
                     (union (free_vars_expr ex2) (free_vars phi))) in
    let p:= fresh_var
              (union (singleton v)
                     (union (singleton h_temp)
                            (union (free_vars_expr ex1)
                                   (union (free_vars_expr ex2) (free_vars phi))))) in
    Agexists p
             (Alloc p /\ 
             (Agexists h_temp
                       (Aequal_heap h_temp /\
                        Aexists_heap
                          (Aref_eq ex1 (GEtempvar p) /\
                           Agexists v (GEtempvar v == ex2 /\
                           (UPDATE p v h_temp /\ phi))))))%assert
  | Sghost gstm => strongest_post_ghost phi gstm
  | Sseq stm1 stm2 => strongest_post (strongest_post phi stm1) stm2
  | Sifthenelse ex s1 s2 =>
    (* (ex == true /\ evaluate s1) \/ (ex == false /\ evaluate s2) /\ phi*)
    (* Equivalently*)
    (* (ex == true -> evaluate s1) /\ (ex == false ->  evaluate s2) /\ phi*)
    ( strongest_post (bool_true ex /\ phi) s1  \/ strongest_post (bool_false ex /\ phi) s2)%assert
  | Sloop  I1 I2 s1 s2 => I2
  | Sbreak => Afalse
  | Scontinue => Afalse
  | Sassert A => (Aand A phi)
  | Sassume A => (Aand A phi)
  end.

Fixpoint gstatement_obligations (phi:assertion)(gstm:gstatement): obligations:=
  match gstm with
  | GSskip => nil
  | GSset x ex => (phi, minimal_weakest_pre_ghost gstm)::nil
  | GSseq gstm1 gstm2 => gstatement_obligations phi gstm1 ++
                        gstatement_obligations (strongest_post_ghost phi gstm1) gstm2
end.

(* Equivalent to minimal_weakest_pre with True poscondition, 
   Done for EACH point in the statement*)
(*It's liberal because it doesn't require termineation*)
(* I1 and I2 are the most recent loop invariants *)
Fixpoint statement_obligations (phi:assertion)(stm:statement)(I: assertion * assertion): obligations:=
match stm with
| Sskip => nil
| Sset id ex => (phi, minimal_weakest_pre stm)::nil
| Sassign ex1 ex2 => (phi, minimal_weakest_pre stm)::nil
| Sghost gstm => gstatement_obligations phi gstm
| Sseq stm1 stm2 => statement_obligations phi stm1 I ++ statement_obligations (strongest_post phi stm1) stm2 I
| Sifthenelse ex s1 s2 =>
  (phi, minimal_weakest_pre stm)::(statement_obligations (bool_true ex /\ phi) s1) I ++
                        (statement_obligations (bool_false ex /\ phi) s2 I)
| Sloop I1 I2 s1 s2 => (phi, I1)::(strongest_post I1 s1, I1)::statement_obligations I1 s1 (I1,I2) ++
                               (strongest_post I1 s2, I1)::statement_obligations I1 s2 (Afalse,I2)
| Sbreak => (phi, snd I)::nil
| Scontinue => (phi, fst I)::nil
| Sassert A => (phi,A)::nil
| Sassume _ => nil
end.

(*  *)
Fixpoint get_loop_invariants (k:cont): assertion * assertion:=
  match k with
  | Kstop => (Afalse, Afalse)
  | Kseq stm k' => get_loop_invariants k'
  | Kloop1 I1 I2 s1 s2 k => (I1, I2)
  | Kloop2 I1 I2 s1 s2 k => (Afalse, I2) (* You can't continue in the second part of the loop *)
  | GKseq gstm k' =>
    (* A break cannot happen when executing ghost code *) 
    (Afalse, Afalse) 
  end.


Fixpoint skip_to_loop (k:cont): cont:=
  match k with
  | Kstop => k
  | Kloop1 _ _ _ _ _ => k
  | Kloop2 _ _ _ _ _ => k
  | Kseq _ k' => skip_to_loop k'
  | GKseq _ k' => skip_to_loop k'
  end.

Definition next_cont (stm:statement)(k:cont): cont:=
 match stm with
 | Sbreak | Scontinue => skip_to_loop k
 | _ => k
 end.

Fixpoint continuation_obligations (phi:assertion)(k:cont) {struct k}: obligations :=
  match k with
  | Kstop => nil
  | Kseq stm k' =>
    statement_obligations phi stm (get_loop_invariants k) ++
                          (continuation_obligations (strongest_post phi stm ) k')
  | Kloop1 I1 I2 s1 s2 k 
  | Kloop2 I1 I2 s1 s2 k =>
    (phi,I1)::(strongest_post I1 s1, I1)::statement_obligations I1 s1 (I1,I2)++
            (strongest_post I1 s2, I1)::statement_obligations I1 s2 (Afalse,I2) ++ continuation_obligations I2 k 
  | GKseq gstm k' =>
    gstatement_obligations phi gstm ++
    (continuation_obligations (strongest_post_ghost phi gstm) k')
  end.


(* All the evaluator functions are monotonic over assertions. *)
(* That is, a stronger precondition produces stronger obligations.*)
Lemma forall_exists_if:
  forall A (P Q: A -> Prop),
    (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof. firstorder. Qed.
Lemma forall_and_if:
  forall (A A' B B': Prop),
    (A -> A') -> (B -> B') -> (A /\ B) -> (A' /\ B').
Proof. tauto. Qed.

    Global Instance subrelation_env_equiv_assert:
      forall ass, subrelation env_equiv (env_equiv_assert ass).
    Proof. intros ? ? ?. apply env_equiv_equiv. Qed.
    

    
Lemma eval_statement_ghost_weakening:
  forall P Q, Q ||= P ->
         forall s, strongest_post_ghost Q s ||= strongest_post_ghost P s.
  Proof.
  intros.
  revert P Q H.
  induction s; intros; auto; try entailer.
  - intros ? ? ?.
    simpl; repeat (first [eapply forall_exists_if; intros ?| apply forall_and_if]);
      intros ?; try solve_assertion.
  - intros ? ? ?.
    simpl. eapply IHs2, IHs1; assumption.
  Qed.
    
      
Lemma eval_statement_weakening:
  forall P Q, Q ||= P ->
    forall s, strongest_post Q s ||= strongest_post P s.
Proof.
  intros.
  revert P Q H.
  induction s; intros; auto; try entailer.
  - (* Set  *)
    intros ? ? ?.
    simpl; repeat (first [eapply forall_exists_if; intros ?| apply forall_and_if]);
      intros ?; solve_assertion.
    
  - (* Assign *)
    intros ? ? ?.
    simpl; repeat (first [eapply forall_exists_if; intros ?| apply forall_and_if]);
      intros ?; solve_assertion.
      
  - (*Sseq *)
    eapply IHs2, IHs1; eassumption.

  - (* ghost*)
    apply eval_statement_ghost_weakening; assumption.

  - (* ifthenelse *)
    simpl; intros.
      specialize (IHs1 (bool_true e /\ P) (bool_true e /\ Q))%assert.
      specialize (IHs2 (bool_false e /\ P) (bool_false e /\ Q))%assert.
      assert (forall K:assertion, (K /\ Q) ||= (K /\ P))%assert by (intros K; entailer).
      specialize (IHs1 (H0 _)).
      specialize (IHs2 (H0 _)).
      entailer.
Qed.

Lemma list_entailment_gstatement_weakening:
  forall P Q,
    Q ||= P ->
    forall stm,
      list_entailment (gstatement_obligations P stm) ->
      list_entailment (gstatement_obligations Q stm).
Proof.
  intros P Q HH stm; revert P Q HH.
  induction stm; auto; simpl;
    try (intros; destruct_and; split; entailer).

  simpl; intros P Q HH.
    repeat rewrite list_entailment_app.
    apply forall_and_if; [apply IHstm1 | apply IHstm2]; auto.
    apply eval_statement_ghost_weakening; auto.
Qed.
  
Lemma list_entailment_statement_weakening:
  forall P Q,
    Q ||= P ->
    forall stm I,
      list_entailment (statement_obligations P stm I) ->
      list_entailment (statement_obligations Q stm I).
Proof.
  intros P Q HH k; revert P Q HH.
  induction k; auto;
    try (simpl; intros; split; entailer).
  - simpl; intros P Q HH I.
    repeat rewrite list_entailment_app.
    apply forall_and_if; [apply IHk1 | apply IHk2]; auto.
    apply eval_statement_weakening; auto.

  - intros; eapply list_entailment_gstatement_weakening;
    eassumption.
    
  - simpl; intros; split; try entailer.
    destruct_and.
    destruct_list_entailment.
    reduce_list_entailment; first [eapply IHk1| eapply IHk2]; eauto;
      entailer.
Qed.

Inductive cont_lt': cont -> cont -> Prop:=
| Loop1_lt: forall P1 P2 s1 s2 k,
    cont_lt' k (Kloop1 P1 P2 s1 s2 k)
| Loop2_lt: forall P1 P2 s1 s2 k,
    cont_lt' k (Kloop2 P1 P2 s1 s2 k)
| seq_lt: forall s k,
    cont_lt' k (Kseq s k).

Inductive cont_lt: cont -> cont -> Prop:=
| cont_step: forall k k',
    cont_lt' k k' ->
    cont_lt k k'
| cont_trans: forall k1 k2 k3,
    cont_lt k1 k2 ->
    cont_lt' k2 k3 ->
    cont_lt k1 k3.


Lemma continuation_strong_ind:
  forall P: cont -> Prop,
    (forall k2, (forall k1, cont_lt k1 k2 -> P k1)  -> P k2) ->
    forall k, P k.
Proof.
  intros P IH k.
  cut (forall K0 k0 : cont, cont_lt k0 K0 -> P k0).
  - intros HH. specialize (HH (Kseq Sskip k)).
    apply HH; do 2 constructor.
    
  - remember (fun K0 => forall k0 : cont, cont_lt k0 K0 -> P k0) as PP. 
    intros KK.
    cut (PP KK); try solve[subst; auto].
    induction KK.
    + subst. intros.
      inversion H; subst. inversion H0. inversion H1.
    + subst.
      assert (HH:=IHKK).
      eapply IH in IHKK.
      intros.
      inversion H; subst; auto.
      * inversion H0; subst.
        eapply IH; eauto.
      * inversion H1; subst.
        eapply HH; auto.
    + subst.
      assert (HH:=IHKK).
      eapply IH in IHKK.
      intros.
      inversion H; subst; auto.
      * inversion H0; subst.
        eapply IH; eauto.
      * inversion H1; subst.
        eapply HH; auto.
    + subst.
      assert (HH:=IHKK).
      eapply IH in IHKK.
      intros.
      inversion H; subst; auto.
      * inversion H0; subst.
        eapply IH; eauto.
      * inversion H1; subst.
        eapply HH; auto.
    +  subst.
       assert (HH:=IHKK).
       apply IH in IHKK.
       intros.
       inversion H; subst.
       * inversion H0; subst.
       * inversion H1; subst.      
Qed.
    
Lemma list_entailment_weakening:
  forall P Q,
    Q ||= P ->
    forall k,
      list_entailment (continuation_obligations P k) ->
      list_entailment (continuation_obligations Q k).
Proof.
  intros P Q HH k; revert P Q HH.
  induction k; try (intros; entailer).
  - simpl; intros ? ? ?;
           repeat rewrite list_entailment_app; intros.
    destruct_and.
    split; try entailer.
    eapply list_entailment_statement_weakening; eauto.
    eapply eval_statement_weakening with (s:=s) in HH.
    eapply IHk; eauto.
  - simpl; intros ? ? ?;
           repeat rewrite list_entailment_app; intros.
    destruct_and.
    split; try entailer.
    eapply list_entailment_gstatement_weakening; eauto.
    eapply eval_statement_ghost_weakening in HH.
    eapply IHk; eauto.
Qed.

End Evaluator.


(** *Verifier Guarantee*)
(* Proof that verification implies safety*)

(*
  EVALex : eval_expr ex e h v
  BOOLval : bool_val v ty = Some b
  ============================
  [e, h, ghe]|= (if b then bool_true ex else bool_false ex)

*)


Lemma eval_expr_bool_spec:
  forall (ex:expr) e h ghe (v:val) ty b,
    eval_expr ex e h v ->
    bool_val v ty = Some b ->
    [e, h, ghe]|= (if b then  (bool_true ex) else (bool_false ex)) .
Proof.
  intros; simpl in *.
  destruct v; destruct ty; inversion H0.
  destruct (Int.eq i Int.zero) eqn:Niz; simpl.
  - apply int_eq_iff in Niz; subst.
    split.
    + eexists; split; econstructor; eauto. econstructor.
    + eapply eval_expr_type; eauto.
      simpl; trivial.
    
  - split.
    + intros [v []].
      destruct_eval_gexpr;
      destruct_eval_expr; subst.
    * eapply int_neq_iff; try reflexivity; eauto.
    * simpl_find; eapply int_neq_iff; try reflexivity; eauto.
    * pose proof (eval_expr_functional _ _ _ _ _ H1 H2) as HH;
        invert HH.
      pose proof (deref_loc_functional _ _ _ _ H0 H3) as HH'; invert HH'.
      eapply int_neq_iff; try reflexivity; eauto.
      
    * assert (HH: (Vptr adr) = (Vptr adr0)) by (eapply eval_expr_functional; eauto).
      invert HH.
      eapply int_neq_iff in Niz; apply Niz.
      cut (Vint i = val_zero).
      { intros HH0; injection HH0; auto. }
      { eapply deref_loc_functional; eauto. }
    + eapply eval_expr_type; eauto.
      simpl; trivial.
Qed.

Definition invariant (st:state):=
  match st with
  | State stm k e h ghe =>
    exists phi,
    eval_assert phi e h ghe /\
    list_entailment (statement_obligations phi stm (get_loop_invariants k))  /\
    list_entailment (continuation_obligations (strongest_post phi stm) k)
  | GState stm k e h ghe => 
    exists phi,
    eval_assert phi e h ghe /\
    list_entailment (gstatement_obligations phi stm)  /\
    list_entailment (continuation_obligations (strongest_post_ghost phi stm) k)
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
  cbn delta[continuation_obligations statement_obligations list_entailment] iota beta;
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

(*
Lemma expr_equiv_tempvar:
  forall (x : ident) (ty : type) (v : option val) (temp : positive),
    temp <> x -> forall e : env, env_equiv_gexpr (Etempvar x) (update_env e temp v) e.
Proof.
  intros ? ? ? ? ? ? ?; cbv [free_vars_expr].
  rewrite PSet.singleton_spec; intros ?; subst x.
  rewrite gso; auto.
Qed.
 *)


Ltac expr_entailer:=
  match goal with
  | _ => assumption
  | [ |- eval_expr (Etempvar ?x) (update_env _ ?x' ?v) _ ?v' ] =>
    match x with
      x' =>
      (*should I check v' = Some v ?*)
      solve [econstructor; rewrite gss; auto]
    end
  | [ |- eval_expr (Etempvar ?x') (update_env _ ?temp' _) _ _ ] =>
    fail (* rewrite expr_equiv_tempvar by (first [assumption|symmetry; assumption])  *)
  | [  |- eval_expr ?ex ?e _ _ ] =>
    match goal with
    | [ H: ~ PSet.In ?temp (free_vars_expr ex) |- _ ] =>
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
  remember (fresh_var (union (free_vars phi) (union (free_vars_expr ex) (singleton x))))
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
    + instantiate (1:=addr); simpl.
      clear cont_entailment.
      apply upd_heap_gss.
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
  forall e h ghe k ex v ty s1 s2 b,
    invariant (State (Sifthenelse ex s1 s2) k e h ghe) ->
    eval_expr ex e h v ->
    bool_val v ty = Some b ->
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
    pose proof (eval_expr_bool_spec ex e h ghe _ _ _ EVALex BOOLval);
      clear -H2; destruct b; auto.
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
    simpl in H1, H3.
    destruct H1 as (? &?&?&?).
    destruct H3 as (? &?&?&?).
    invert H3.
    clear H cont_entailment.
    (*For eval_expr e1*)
    eapply expr_defined_safe in H1.
    destruct H1 as (?&H1).
    
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

    simpl in IS_BOOL.
    destruct (tint_is_bool _ _ _ _ IS_BOOL H2). 
    econstructor; try eassumption.

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
          (program_verified: continuation_obligations Atrue verified_program = program_obligations)
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

(*Delete later:

Inductive Safe': state -> Prop:=
| Safe_Stop: forall e, Safe' (State Sskip Kstop e)
| Safe_Step:
    forall st st',
      Safe' st' ->
      step st st' ->
      Safe' st.


       (** * Examples *)

       (*
  "a" = 1
  "b" = 2
  \\ assert "a" == 1
  \\ assert "b" == 2

 *)
 *)