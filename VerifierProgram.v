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
Import Expressions.

(** * Verifier*)

Section Evaluator.

  (*Minimal weakest pre is the minimal requirements to take a step. *)
  (*This is different to the weakes_pre that allows to continue execution.*)

  (** Computes the Weakest Precondition for the first ghost expression in 
      the ghost statement *)
  Fixpoint first_gexpr_weakest_pre  (gstm:gstatement):assertion:=
    match gstm with
    | GSskip => Atrue
    | GSset _ ex => (assert_gexpr_defined ex)%assert
    | GSseq x _ => first_gexpr_weakest_pre x
    end.

  Definition evaluates_to_bool (ex:expr): assertion :=
    let x:= fresh_var (free_vars_gexpr ex) in
    Agexists x 
             (Agexpr_type (GEtempvar x Tint) Tint /\ (GEtempvar x Tint) == ex)%assert.

  (*The follwing determine if an expression is true or false*)
  Definition bool_true (ex:expr):assertion:=
    (~ Econst_int Int.zero Tint  == ex /\ evaluates_to_bool ex)%assert.
  Definition bool_false (ex:expr):assertion:=
    (Econst_int Int.zero Tint  == ex)%assert.

  (** Computes the Weakest Precondition for the first expression in 
      the statement *)
  Fixpoint first_expr_weakest_pre (stm:statement): assertion :=
    match stm with
      Sskip => Atrue
    | Sset id ex => (assert_expr_defined ex)%assert
    | Sassign ex1 ex2 =>
      ( assert_expr_defined ex2 /\
        assert_lvalue_defined ex1 /\
        let p:= fresh_var (free_vars_gexpr ex1) in
        (* Aalloc p /\ *) (*This seems useless*)
        Agexists p (Aref_eq ex1 (GEtempvar p (type_of_expr ex1)) )
      )%assert
    | Sseq x x0 => first_expr_weakest_pre x
    | Sifthenelse ex s1 s2 =>
      (assert_expr_defined ex /\
       evaluates_to_bool ex)%assert  
    | Sloop  I1 I2  s1 s2 => I1
    | Sbreak => Atrue
    | Scontinue => Atrue
    | Sghost gstm => first_gexpr_weakest_pre gstm
    | Sassert P => P
    | Sassume P => Atrue
    end.

  Notation obligations:= (list (assertion * assertion)).

  (* Computes the strongest postcondition for ghost statements. *)
  Fixpoint strongest_post_ghost (phi:assertion)(gstm:gstatement): assertion:=
    match gstm with
    | GSskip => phi
    | GSset x ex =>
      let ty':=type_of_gexpr ex in
      let temp:= fresh_var
                   (union (free_vars phi)
                          (union (free_vars_gexpr ex) (singleton x)))  in
      Agexists temp
               ((GEtempvar x ty' == GEtempvar temp ty') /\
                (Agexists x ((GEtempvar temp ty' == ex) /\
                             phi)))%assert
    | GSseq stm1 stm2 => strongest_post_ghost (strongest_post_ghost phi stm1) stm2
    end.

  (*pointer is allocated*)
  Definition Aallocated (p:ident): assertion := 
    let x:= fresh_var (singleton p) in
    Agexists x (Aalloc p x).

  
  (* Computes the strongest postcondition for statements. *)
  Fixpoint strongest_post (phi:assertion)(stm:statement): assertion:=
    match stm with
    | Sskip =>  phi
    | Sset x ex => (* id = expr*)
      (*Ex. temp. x=temp /\ Ex. x.  temp = e /\ P*)
      let ty':=type_of_gexpr ex in
      let temp:= fresh_var
                   (union (free_vars phi)
                          (union (free_vars_gexpr ex) (singleton x)))  in
      Agexists temp
               ((Etempvar x ty' == GEtempvar temp ty') /\
                (Aexists x ((GEtempvar temp ty' == ex) /\
                            phi)))%assert
    | Sassign ex1 ex2 =>
      let ty1:= type_of_expr ex1 in
      let ty2:= type_of_expr ex2 in
      let h_temp:= fresh_var (free_vars phi) in
      let v:= fresh_var
                (union (singleton h_temp)
                       (union (free_vars_gexpr ex2) (free_vars phi))) in
      let p:= fresh_var
                (union (singleton v)
                       (union (singleton h_temp)
                              (union (free_vars_gexpr ex1)
                                     (union (free_vars_gexpr ex2) (free_vars phi))))) in
      Agexists p
               (Aallocated p /\  
                (Agexists h_temp
                          (Aequal_heap h_temp /\
                           Aexists_heap
                             (Aref_eq ex1 (GEtempvar p ty1) /\
                              Agexists v (GEtempvar v ty2 == ex2 /\
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

  (* Liberal Weakest precondition for ghost statement*)
  Fixpoint weakest_precondition_gstm (phi:assertion)(gstm:gstatement): obligations:=
    match gstm with
    | GSskip => nil
    | GSset x ex => (phi, first_gexpr_weakest_pre gstm)::nil
    | GSseq gstm1 gstm2 => weakest_precondition_gstm phi gstm1 ++
                          weakest_precondition_gstm (strongest_post_ghost phi gstm1) gstm2
    end.

  (* Liberal Weakest precondition for statement*)
  (*It's liberal because it doesn't require termineation*)
  (* I1 and I2 are the most recent loop invariants *)
  Fixpoint weakest_precondition_stm (phi:assertion)(stm:statement)(I: assertion * assertion): obligations:=
    match stm with
    | Sskip => nil
    | Sset id ex => (phi, first_expr_weakest_pre stm)::nil
    | Sassign ex1 ex2 => (phi, first_expr_weakest_pre stm)::nil
    | Sghost gstm => weakest_precondition_gstm phi gstm
    | Sseq stm1 stm2 =>
      weakest_precondition_stm phi stm1 I ++
      weakest_precondition_stm (strongest_post phi stm1) stm2 I
    | Sifthenelse ex s1 s2 =>
      (phi, first_expr_weakest_pre stm)::(weakest_precondition_stm (bool_true ex /\ phi) s1) I ++
      (weakest_precondition_stm (bool_false ex /\ phi) s2 I)
    | Sloop I1 I2 s1 s2 => (phi, I1)::(strongest_post I1 s1, I1)::weakest_precondition_stm I1 s1 (I1,I2) ++
                                   (strongest_post I1 s2, I1)::weakest_precondition_stm I1 s2 (Afalse,I2)
    | Sbreak => (phi, snd I)::nil
    | Scontinue => (phi, fst I)::nil
    | Sassert A => (phi,A)::nil
    | Sassume _ => nil
    end.

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

  (* Liberal Weakest precondition for continuations *)
  Fixpoint weakest_precondition_cont (phi:assertion)(k:cont) {struct k}: obligations :=
    match k with
    | Kstop => nil
    | Kseq stm k' =>
      weakest_precondition_stm phi stm (get_loop_invariants k) ++
                            (weakest_precondition_cont (strongest_post phi stm ) k')
    | Kloop1 I1 I2 s1 s2 k 
    | Kloop2 I1 I2 s1 s2 k =>
      (phi,I1)::(strongest_post I1 s1, I1)::weakest_precondition_stm I1 s1 (I1,I2)++
              (strongest_post I1 s2, I1)::weakest_precondition_stm I1 s2 (Afalse,I2) ++ weakest_precondition_cont I2 k 
    | GKseq gstm k' =>
      weakest_precondition_gstm phi gstm ++
                             (weakest_precondition_cont (strongest_post_ghost phi gstm) k')
    end.

  Global Instance subrelation_env_equiv_assert:
    forall ass, subrelation env_equiv (env_equiv_assert ass).
  Proof. intros ? ? ?. apply env_equiv_equiv. Qed.
  
  (* All the evaluator functions are monotonic over assertions. *)
  (* That is, a stronger precondition produces stronger obligations.*)
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
      intros ? ? ?; simpl.
      simpl; repeat (first [eapply forall_exists_if; intros ?| apply forall_and_if]);
        intros ?; try solve[solve_assertion].
      remember (fresh_var
                  (union
                     (singleton
                        (fresh_var
                           (union (singleton (fresh_var (free_vars Q))) (free_vars Q))))
                     (union (singleton (fresh_var (free_vars Q))) (free_vars Q)))) as X1.
      remember (fresh_var
                  (union
                     (singleton
                        (fresh_var (union (singleton (fresh_var (free_vars P))) (free_vars P))))
                     (union (singleton (fresh_var (free_vars P))) (free_vars P)))) as X2.
      rewrite H0.
      simpl_find. reflexivity.
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
        list_entailment (weakest_precondition_gstm P stm) ->
        list_entailment (weakest_precondition_gstm Q stm).
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
        list_entailment (weakest_precondition_stm P stm I) ->
        list_entailment (weakest_precondition_stm Q stm I).
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
        list_entailment (weakest_precondition_cont P k) ->
        list_entailment (weakest_precondition_cont Q k).
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
