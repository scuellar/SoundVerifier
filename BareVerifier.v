Require Import compcert.lib.Coqlib.

Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 
Require Import FSets.FMapPositive.
Import PositiveMap. Module PMap:= PositiveMap. (*For positive-indexed maps*)
Require Import FSets.FMapFacts.

Module PMapsFacts:=  (WFacts_fun OrderedTypeEx.PositiveOrderedTypeBits PMap).
Import PMapsFacts.

(*+ First step: bearest of verifiers *)

(** * 1)Values *)
Inductive val: Type :=
| Vundef 
  | Vint: int -> val. (*int is a machine *)

(** * 2) Types *)
Inductive type : Type :=
| Tint: type    (**r integer types *).

(** * 3) Expressions *)
Definition ident := positive.

Inductive expr : Type :=
  | Eval (v: val) (ty: type)  (**r constant *)
  | Evar (id: ident) (ty: type)  (**r constant *).

Definition type_of (e:expr): type:=
  match e with
    Eval _ ty => ty
  | Evar _ ty => ty
  end.

Fixpoint free_vars_expr (e:expr): PositiveSet.t:=
  match e with
    Eval _ _ => PositiveSet.empty
  | Evar id _ => singleton id
  end.

(** * 8) Environment *)
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Definition env:Type := PMap.t (val * type).
Definition find  (e:env) (k:ident) := PMap.find k e.
Definition env_fun_equiv: relation (positive -> option (val * type)) := pointwise_relation _ Logic.eq.
Global Instance Equivalenc_env_fun_equiv: Equivalence env_fun_equiv:= _.
Definition env_equiv: relation env := (fun x y => env_fun_equiv (find x) (find y)).
Global Instance Equivalenc_env_equiv: Equivalence env_equiv.
Proof.
  pose proof (Relations.inverse_image_of_equivalence _ _  find env_fun_equiv).
  destruct H; auto.
  constructor;
    destruct (Equivalenc_env_fun_equiv); eauto.
Qed.

Definition empty_env: env:= PMap.empty _.
Definition update_env (e:env) (k:ident) (ty:type) (v:val): env:=
  PMap.add k (v, ty) e.

Global Instance Proper_update_env: Proper ( env_equiv ==> Logic.eq ==>Logic.eq ==>Logic.eq ==> env_equiv) update_env.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? id; subst.
  cbv delta [update_env] beta.
  destruct (Pos.eq_dec y0 id); auto.
  - subst. cbv [find]; repeat rewrite add_eq_o; eauto.
  - cbv [find]; repeat rewrite add_neq_o; eauto.
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

Definition get_var_error (e:env) (k:ident) : val:=
  match find e k with
  | Some (v, _) => v
  | None => Vundef
  end.
Definition get_type (e:env) (k:ident): option type:=
  match find e k with
    None => None
  | Some (_, ty) => Some ty
  end.
Global Instance Proper_get_type: Proper ( env_equiv ==> Logic.eq ==> Logic.eq) get_type.
Proof.
  intros ? ? ? ? ? ?; subst.
  cbv [get_type]; rewrite H; reflexivity.
Qed.

Definition eval_expr (e:env) (ex:expr): option (val*type) :=
  match ex with
  | Eval v ty => Some (v,ty)
  | Evar id ty => (find e id) 
  end.
Global Instance Proper_eval_expr: Proper ( env_equiv ==> Logic.eq ==> Logic.eq) eval_expr.
Proof.
  intros ? ? ? ? ? ?; subst.
  induction y0; simpl.
  - reflexivity.
  - rewrite H; reflexivity.
Qed.

(** * 4) Assertions *)
Inductive assertion:=
| Atrue : assertion
| Afalse : assertion
| Aand : assertion -> assertion -> assertion
| Aor : assertion -> assertion -> assertion
| Anot : assertion -> assertion
| Aexists : ident -> type -> assertion -> assertion
| Adefined : ident -> assertion
| Aexpr_type : expr -> type -> assertion
| Avar_type: ident -> type -> assertion
| Aeq: ident -> expr -> assertion. (* x == 5 *)

Fixpoint free_vars (A: assertion): PSet.t:= (*returns a set od positives*)
  match A with
  | Atrue | Afalse=> PSet.empty
  | Aand A1 A2 => union (free_vars A1) (free_vars A2)
  | Aor A1 A2 => union (free_vars A1) (free_vars A2)
  | Anot A' => free_vars A'
  | Aexists id _ A' => PSet.remove id (free_vars A')
  | Adefined id => singleton id
  | Aexpr_type e _ => free_vars_expr e
  | Avar_type id _ => singleton id
  | Aeq id e => PSet.add id (free_vars_expr e)
  end.

Definition fresh_var (A:assertion): positive:=
  match (max_elt (free_vars A)) with
  | Some x => x+1
  | None => 1
  end.

Definition expr_type (e:env)(ex:expr)(ty:type):=
  match ex with
  | Eval v ty' => ty = ty'
  | Evar id ty' => ty = ty' /\ get_type e id = Some ty
  end.

Global Instance Proper_expr_type: Proper ( env_equiv ==> Logic.eq ==>  Logic.eq ==> Logic.iff) expr_type.
Proof.
  intros ? ? ? ? ? ? ? ? ?; subst.
  induction y0; simpl.
  - reflexivity.
  - f_equiv. rewrite H; reflexivity.
Qed.


Fixpoint eval_assert (e: env) (P:assertion): Prop:=
  match P with
  | Atrue => True
  | Afalse => False
  | Aand P1 P2 => eval_assert e P1 /\ eval_assert e P2
  | Aor  P1 P2 => eval_assert e P1 \/ eval_assert e P2
  | Anot P => ~ eval_assert e P
  | Aexists id ty P => exists v, eval_assert (update_env e id ty v) P  
  | Adefined id =>  ~ find e id = None 
  | Aexpr_type ex ty => expr_type e ex ty
  | Avar_type id ty => get_type e id = Some ty
  | Aeq id ex2 => find e id = eval_expr e ex2 
  end.

Global Instance Proper_eval_assert: Proper ( env_equiv ==> Logic.eq ==> Logic.iff) eval_assert.
Proof.
  intros ? ? ? ? ? ?.
  subst. generalize x y H. clear.
  induction y0;
    try solve[intros; split;auto];
    simpl; intros;
    try solve[rewrite H; reflexivity]. 
  - rewrite IHy0_1, IHy0_2; eauto; reflexivity.
  - rewrite IHy0_1, IHy0_2; eauto; reflexivity.
  - rewrite IHy0; eauto; reflexivity.
  - split; (
    intros HH; destruct HH as [v HH]; exists v;
    rewrite IHy0; eauto; f_equiv; auto; symmetry; auto ).
  - repeat rewrite H; tauto.
Qed.

  
(** * 5) Statements *)

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : ident -> type -> expr -> statement   
  | Sassert : assertion -> statement
  | Sassume : assertion -> statement
.

(** * 6) Continuations*)
Inductive cont: Type:=
| Kstop
| Kseq: statement -> cont -> cont.

(** * 7) Knowledge*)
Definition knowledge:= assertion.

(** * 10) State *)

Inductive state : Type :=
  State : env ->
          statement ->
          cont -> state.

(** * 11)Smallstep semantics *)
Inductive step: state -> state-> Prop:=
| step_skip: forall e s c,
    step (State e Sskip (Kseq s c)) (State e s c)
| step_assign: forall e ex2 k ty v c,
    get_type e k = Some ty \/ get_type e k = None ->
    eval_expr e ex2 = Some (v, ty) ->
    step (State e (Sassign k ty ex2) c)
         (State (update_env e k ty v) Sskip c) 
| step_assume: forall e P c,
    eval_assert e P ->
    step (State e (Sassert P) c)
         (State e  Sskip c)
| step_assert_pass: forall e P c s,
    eval_assert e P ->
    step (State e (Sassert P) (Kseq s c))
         (State e s c).

Inductive step_star: state -> state -> Prop:=
| stutter : forall st, step_star st st
| Star_step : forall st st' st'', step_star st st' ->
                             step st' st'' ->
                             step_star st st''.

Inductive safe_state:
  state-> Prop:=
| safe_skip: forall e k,
    safe_state (State e Sskip k)
| safe_assign: forall e ex2 k ty v c,
    get_type e k = Some ty \/ get_type e k = None ->
    eval_expr e ex2 = Some (v, ty) ->
    safe_state (State e (Sassign k ty ex2) c)
| safe_assume: forall e P c,
    safe_state (State e (Sassume P) c)
| safe_assert_pass: forall e P c,
    eval_assert e P ->
    safe_state (State e (Sassert P) c).

(** * 11) Safety *)
Definition Safe (st:state):Prop:=
  forall st', step_star st st' ->
         safe_state st'.

(** *Obligations and proofs*)
Notation obligations:= (list (assertion * assertion)). (*list (assertion |- assertion )*)

Definition assertion_entailment (entailment:assertion * assertion): Prop :=
  let (P,Q):= entailment in
  forall e, eval_assert e P -> eval_assert e Q.

Fixpoint list_entailment (entailments: list (assertion * assertion)): Prop :=
  match entailments with
    nil => True
  | ent::ents => assertion_entailment ent /\ list_entailment ents
  end.


(** *Predicate evaluator*)
Definition assert_expr_defined (e:expr): assertion:=
  match e with
    Eval v ty => Atrue
   | Evar id ty => Adefined id
  end.

(* kge' := x = v /\ exists x, kge *)
(* kge' := x = temp /\ exists temp, temp = ex2 /\ exists x, kge *)
Definition weakest_pre (stm:statement)(*Postcondition = True*) :assertion:= (*weakest liberal precondition*)
  match stm with
    Sskip => Atrue
  | Sassign id ty e2 => Aand (Aand (Aexpr_type e2 ty) (assert_expr_defined e2)) (Aor (Avar_type id ty) (Anot (Adefined id)))
  | Sassert P => P
  | Sassume P => Atrue
  end.

Definition evaluate_statements (phi:assertion)(stm:statement): assertion:=
  match stm with
  | Sskip =>  phi
  | Sassign id ty ex => (* id = expr*)
    (*Ex. temp. x=temp /\ Ex. x.  temp = e /\ P*)
    let temp:= fresh_var phi in
    Aexists temp ty (Aand (Aeq id (Evar temp ty)) (Aexists id ty (Aand (Aeq temp ex) phi)))
  | Sassert A => (Aand A phi)
  | Sassume A => (Aand A phi)
  end.

Fixpoint evaluate_continuation (phi:assertion)(k:cont): obligations :=
  match k with
  | Kstop => nil
  | Kseq stm k' =>
    (phi, weakest_pre stm):: (evaluate_continuation (evaluate_statements phi stm) k')
  end.

(** *Verifier Guarantee*)
(* Proof that verification implies safety*)

Lemma expre_eval_safe:
  forall e ex ty,
    expr_type e ex ty ->
    eval_assert e (assert_expr_defined ex) ->
    exists v,  eval_expr e ex = Some (v, ty).
Proof.
  intros.
  destruct ex; simpl.
  - econstructor; simpl in H;
      inversion H; subst; reflexivity.
  - cbn in H0. 
    simpl in H. 
    cbv [get_type] in H.
    destruct (find e id);
      try solve [contradiction; eapply H0; eauto].
    simpl in H; destruct H.
    destruct p; inversion H1; subst.
    clear H0.
    Set Keep Proof Equalities.
    injection H1; intros; subst.
    econstructor; reflexivity.
Qed.

Lemma wealest_pre_safe_st:
  forall e stm k,
    eval_assert e (weakest_pre stm) ->
    safe_state (State e stm k).
Proof.
  intros.
  destruct stm; try solve[ constructor; auto].
  simpl in H.
  destruct H as [[H1 H2] H3].
  destruct (expre_eval_safe _ _ _ H1 H2). 
  econstructor; eauto.
  destruct H3; [left|right]; auto.
  cbv [get_type].
  destruct (find e i); auto.
  contradict H0; intros HH; discriminate.
Qed.


Definition invariant (st:state):=
  match st with
  | State e stm k =>
    exists phi,
    eval_assert e phi /\
    eval_assert e (weakest_pre stm) /\
    list_entailment (evaluate_continuation (evaluate_statements phi stm) k)
  end.

Lemma step_preservation:
  forall st st',
    step st st' ->
    invariant st ->
    invariant st'.
Proof.
  intros.
  inversion H; subst.
  - cbv delta[invariant] beta iota in H0;
      destruct H0 as [phi [phi_OK [stm_OK entailments]]].
    
    cbv delta [evaluate_statements] beta iota.
    exists phi.
    split; auto.
    cbv delta [list_entailment evaluate_continuation] beta iota in entailments.
    destruct entailments as [A B].
    apply A in phi_OK.
    split; auto.
  - destruct H0 as [phi [phi_OK [stm_OK entailments]]].
    cbv [evaluate_statements] in entailments.
    exists (evaluate_statements phi (Sassign k ty ex2)).
    split.
    +


      Lemma redundant_update:
        forall e i ty v ty' v',
          env_equiv (update_env (update_env e i ty v) i ty' v')
                    (update_env e i ty' v').
      Proof.
        intros ? ? ? ? ? ? id.
        cbv delta[update_env find] beta.
        destruct (peq i id).
        - repeat rewrite add_eq_o; auto.
        - repeat rewrite add_neq_o; auto.
      Qed.
      Lemma add_eq_o' : forall m x e,
          @PMap.find (val*type) x (PMap.add x e m) = Some e.
      Proof.
        intros; apply add_eq_o; reflexivity.
      Qed.
      Lemma update_comm:
        forall e i j ty v ty' v',
          i <> j ->
          env_equiv (update_env (update_env e i ty v) j ty' v')
                    (update_env (update_env e j ty' v') i ty v).
      Proof.
        intros ? ? ? ? ? ? ? NEQ id.
        cbv delta[update_env find] beta.
        destruct (peq i id); destruct (peq j id); subst;
          try solve[contradiction NEQ; auto];
          repeat (repeat rewrite add_eq_o';
                  rewrite add_neq_o;
                  repeat rewrite add_eq_o'); auto.
      Qed.
      Lemma expr_type_update:
        forall k ex,
          ~ PSet.In k (free_vars_expr ex) -> 
          forall e ty ty' v, expr_type (update_env e k ty' v) ex ty <->
                        expr_type e ex ty.
      Proof.
        intros; destruct ex; try tauto.
        simpl in *. f_equiv.
        rewrite PSet.singleton_spec in H.
        cbv delta[get_type update_env find] beta.
        rewrite add_neq_o; auto. reflexivity.
      Qed.
      Lemma get_type_update:
        forall k i,
          k <> i -> 
          forall e ty' v, get_type (update_env e k ty' v) i =
                     get_type e i.
      Proof.
        intros; try tauto.
        cbv delta[get_type update_env find] beta.
        rewrite add_neq_o; auto.
      Qed.
      Lemma eval_expr_update:
        forall k ex,
          ~ PSet.In k (free_vars_expr ex) -> 
          forall e ty v, 
            eval_expr (update_env e k ty v) ex =
            eval_expr e ex.
      Proof.
        intros.
        destruct ex; simpl in *; auto.
        rewrite PSet.singleton_spec in H.
        cbv [find update_env]. rewrite add_neq_o; auto.
      Qed.
      Lemma free_vars_update:
        forall k phi,
          ~ PSet.In k (free_vars phi) -> 
          forall e ty v, 
            eval_assert (update_env e k ty v) phi <->
            eval_assert e phi.
      Proof.
        intros ? ? ?. induction phi; eauto; try reflexivity.
        - intros; simpl; f_equiv; first [apply IHphi1 | apply IHphi2];
            auto; intros HH; apply H; simpl; apply union_spec;
              [left| right]; assumption.
        - intros; simpl; f_equiv; [ apply IHphi1|  apply IHphi2]; auto;
            intros HH; apply H; simpl; apply union_spec;
              [left| right]; assumption.
        - intros; simpl; f_equiv.
          apply IHphi; assumption.
        - intros; simpl.
          split; intros [v' HH]; exists v'.
          + destruct (E.eq_dec k i).
            * subst.
              
              pose proof (redundant_update e i ty v t0 v').
              rewrite <- H0; auto.
            * idtac.
              
              rewrite update_comm in HH; auto.
              rewrite <- IHphi; eauto.
              intros IN.
              apply H.
              eapply remove_spec; split; auto.
          + destruct (E.eq_dec k i).
            * subst; rewrite redundant_update; eauto.
            * rewrite update_comm; auto.
              rewrite IHphi; eauto.
              intros IN.
              apply H.
              eapply remove_spec; split; auto.
        - intros.
          simpl in *.
          rewrite singleton_spec in H.
          cbv delta[update_env find] beta.
          rewrite add_neq_o; tauto.
        - intros.
          simpl in *.

          
          

          rewrite expr_type_update; eauto; reflexivity.

        - intros.
          simpl in *.

          
          
          

          rewrite PSet.singleton_spec in H.
          
          rewrite get_type_update; eauto; reflexivity.
        - intros.
          simpl in *.
          rewrite PSet.add_spec in H.
          apply Classical_Prop.not_or_and in H; destruct H.

          f_equiv. cbv [find update_env]; rewrite add_neq_o; auto.

          

          apply eval_expr_update; auto.

          
      Qed.
      Lemma fresh_var_spec:
        forall phi,
          ~ PSet.In (fresh_var phi) (free_vars phi).
      Proof.
        intros.
        cbv delta[fresh_var] beta iota zeta; intros AA.
        destruct (max_elt (free_vars phi)) eqn:BB.
        - eapply PSet.max_elt_spec2 in BB; eauto.
          apply BB; eauto.
          simpl.
          unfold elt in *.
          clear.
          admit. (*positive arithmetic*)
        - apply PSet.max_elt_spec3 in BB.
          eapply BB; eauto.
      Admitted.
      Lemma assertion_assignment_ok:
        forall e k v ty ex2 phi,
          eval_assert e phi ->
          eval_assert e (weakest_pre (Sassign k ty ex2)) ->
          eval_assert (update_env e k ty v) (evaluate_statements phi (Sassign k ty ex2)).
      Proof.
        intros.
        destruct H0 as [[EXtype EXdef] Kdef].
        repeat econstructor.
        
        - simpl.
          destruct (peq (fresh_var phi) k).
          + simpl.
            cbv delta[find update_env] beta.
            repeat rewrite add_eq_o; auto.
          + simpl.
            cbv delta[find update_env] beta.
            rewrite add_neq_o; auto.
            rewrite add_eq_o; auto.
            rewrite add_eq_o; auto.
        -  simpl.
           instantiate (1:= get_var_error e k).
           simpl in EXtype.
           admit.
        - destruct (peq (fresh_var phi) k).
          + rewrite <- e0.
            subst; repeat rewrite free_vars_update;
              eauto.
            apply fresh_var_spec.
            apply fresh_var_spec.
            apply fresh_var_spec.
          + rewrite update_comm; auto.
            rewrite free_vars_update;
              try apply fresh_var_spec.
            rewrite redundant_update.
            unfold get_var_error.
            destruct Kdef.
            * simpl in H0; unfold get_type in H0.
              destruct (find e k) eqn:HH; try congruence.
              destruct p. inversion H0; subst.
              
              Lemma pointless_update:
                forall e k v ty,
                  find e k = Some (v, ty) ->
                  env_equiv (update_env e k ty v)
                            e.
              Proof.
                intros ? ? ? ? ? id.
                unfold update_env, find.
                destruct (peq k id).
                - rewrite add_eq_o; symmetry; subst; auto.
                - rewrite add_neq_o; auto.
              Qed.

              rewrite pointless_update; auto.
            * simpl in *. destruct (find e k) eqn:HH.
              contradict H0. intros ?; congruence.
              admit.
      Admitted.


        (*The following lemma is loosely the progress lemms*)
        (*In some sense, safe states are the once that can step*)
        Lemma invariant_safety:
          forall st,
            invariant st ->
            safe_state st.
        Proof.
          cbv [invariant]; destruct st as [e s k].
          intros INV; destruct INV as [phi [phi_OK [stm_OK entailments]]].
          destruct s; try solve[econstructor].
          - cbv [weakest_pre eval_assert assert_expr_defined] in stm_OK.
            destruct stm_OK as [[E_ty HH] DEFINED].
            destruct e0.
            + econstructor.
              * destruct DEFINED; eauto.
                right. cbv [get_type].
                destruct (find e i); try reflexivity.
                contradict H; discriminate.
              * simpl in *; subst ty; reflexivity.
            + simpl in *. destruct E_ty; subst ty.
              cbv [get_type] in H0. destruct (e id) eqn:Eid; try discriminate.
              destruct p. inversion H0; subst t1.
              econstructor.
              * destruct DEFINED; eauto.
                right. cbv [get_type].
                destruct (e i); try reflexivity.
                contradict H; discriminate.
              * simpl in *. eassumption.
          - constructor.
            assumption.

        Qed.

        Lemma star_preservation:
          forall st st',
            step_star st st' ->
            invariant st ->
            invariant st'.
        Proof.
          intros ? ? STAR.
          Require Import  Program.Equality.
          dependent induction STAR; auto.
          intros IH; apply IHSTAR in IH; clear IHSTAR.
          eapply step_preservation; eauto.
        Qed.
        
        Lemma star_safety:
          forall st,
            invariant st ->
            forall st',
              step_star st st' ->
              safe_state st'.
        Proof.
          intros.
          apply invariant_safety.
          apply star_preservation with st; auto.
        Qed.

        Section VerificationSafety.
          
          Context (verified_program: cont)
                  (program_obligations: obligations)
                  ( Precondition: assertion)
                  (program_verified: evaluate_continuation Atrue verified_program = program_obligations)
                  (verifier_guaranty: list_entailment program_obligations).
          
          
          Lemma initial_invariant:
            invariant (State empty_env Sskip verified_program).
          Proof.
            exists Atrue. repeat (split; auto).
            cbv [evaluate_statements].
            rewrite program_verified.
            apply verifier_guaranty.
          Qed.
          
          
          
          Theorem verifier_correctness:
            Safe (State empty_env Sskip verified_program). 
          Proof.
            intros st' step.
            eapply star_safety with (State empty_env Sskip verified_program); auto.
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