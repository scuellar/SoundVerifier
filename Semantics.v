Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 
Require Import Coq.Classes.Morphisms.

Require Import VCC.Tactics.
Require Import VCC.Basics.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import VCC.AssertionSemantics.
Require Import VCC.Expressions.


(** * 5) Statements *)

Inductive gstatement: Type :=
(*Ghost statements*)
| GSskip : gstatement
| GSset : ident -> gexpr -> gstatement                             (* x=i         *)
| GSseq :   gstatement -> gstatement -> gstatement                         (* sequence    *).

Inductive statement : Type :=
| Sskip : statement                                                  (* do nothing  *)
| Sset : ident -> expr -> statement                                    (* x=i         *)
| Sassign : expr -> expr -> statement                                  (* x*=i         *)
| Sseq :   statement -> statement -> statement                         (* sequence    *)
| Sghost :   gstatement -> statement                                  (* sequence    *)
| Sifthenelse : expr -> statement -> statement -> statement             (* conditional *)
| Sloop: assertion ->  assertion ->  statement -> statement -> statement (* infinite loop *)
| Sbreak : statement                                                 (* break statement *)
| Scontinue : statement                                              (* continue statement *)   
| Sassert : assertion -> statement                                    (* assert P    *)
| Sassume : assertion -> statement                                    (* assume P    *).


(** The C loops are derived forms. *)

Definition Swhile (inv:assertion) (e: expr) (s: statement) :=
  Sloop inv (inv /\ (Rexpr expr_zero) == (Rexpr e))%assert (Sseq (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (inv:assertion)(s: statement) (e: expr) :=
  Sloop inv (inv /\ Rexpr expr_zero == Rexpr e)%assert s (Sifthenelse e Sskip Sbreak).

Definition Sfor (inv:assertion)(s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Sseq s1 (Sloop inv (inv /\ Rexpr expr_zero == Rexpr e2)%assert (Sseq (Sifthenelse e2 Sskip Sbreak) s3) s4).


(** * 6) Continuations*)
Inductive cont: Type:=
| Kstop
| Kloop1: assertion -> assertion -> statement -> statement -> cont -> cont
| Kloop2: assertion -> assertion -> statement -> statement -> cont -> cont 
| Kseq: statement -> cont -> cont
| GKseq: gstatement -> cont -> cont.

(** * 10) State *)

Inductive state : Type :=
| State : statement ->
          cont ->
          renv ->
          heap ->
          genv ->
          state
| GState : gstatement ->
           cont ->
           renv ->
           heap ->
           genv ->
           state.

(** * 11)Smallstep semantics *)
Definition bool_val (v:val)(ty:type): option bool:=
  match v,ty with
  | Vint n, Tint =>
    Some  (negb (Int.eq n Int.zero)) 
  | _, _ => None
  end.
Lemma tint_is_bool:
  forall (e0 : expr) (e : renv) (h : heap) x,
    expr_type e0 e h Tint ->
    eval_expr e0 e h x ->
    exists b, bool_val x Tint = Some b.
Proof.
  intros.
  induction e0.
  + destruct_eval_expr.
    simpl. eexists; reflexivity.
  + destruct H as (?&?&?).
    destruct_eval_expr; simpl_find.
    destruct x0; invert H2.
    eexists; reflexivity.
  + simpl in H.
    clear IHe0; invert H0.
    pose proof (expr_type_eval_pointers _ _ _ _ _ H0 H2).
    destruct x; invert H3.
    eexists; reflexivity.
Qed.

Inductive step: state -> state-> Prop:=
| step_skip: forall e ghe h s c,
    step (State Sskip (Kseq s c) e h ghe) (State s c e h ghe)
| step_seq: forall s1 s2 k e ghe h,
    step (State (Sseq s1 s2) k e h ghe)
         (State s1 (Kseq s2 k) e h ghe)
| step_continue_seq: forall s k e ghe h,
    step (State Scontinue (Kseq s k) e h ghe)
         (State Scontinue k e h ghe)
| step_break_seq: forall s k e ghe h,
    step (State Sbreak (Kseq s k) e h ghe)
         (State Sbreak k e h ghe)
| step_set: forall e ghe h ex k v c,
    eval_expr ex e h v ->
    step (State (Sset k ex) c e h ghe)
         (State Sskip c (update_env e k (Some v))  h ghe)
| step_assign:
    forall e ghe h ex1 ex2 v c addr,
    eval_lvalue ex1 e h addr ->
    eval_expr ex2 e h v ->
    step (State (Sassign ex1 ex2) c e h ghe)
         (State Sskip c e (upd_heap h addr v) ghe)
         
(*Conditionals*)         
| step_ifthenelse: forall e ghe h a v ty s1 s2 k b,
    eval_expr a e h v ->
    bool_val v ty = Some b ->
    step (State (Sifthenelse a s1 s2) k e h ghe)
         (State (if b then s1 else s2) k e h ghe)
         
(*Loops*)         
| steploop: forall I1 I2 s1 s2 k e ghe h,
      step (State (Sloop I1 I2 s1 s2) k e h ghe)
         (State s1 (Kloop1 I1 I2 s1 s2 k) e h ghe)
| step_skip_or_continue_loop1: forall I1 I2 s1 s2 k e ghe h x,
    x = Sskip \/ x = Scontinue ->
    step (State x (Kloop1  I1 I2 s1 s2 k) e h ghe)
          (State s2 (Kloop2  I1 I2  s1 s2 k) e h ghe)
| step_break_loop1: forall  I1 I2  s1 s2 k e ghe h,
    step (State Sbreak (Kloop1  I1 I2  s1 s2 k) e h ghe)
          (State Sskip k e h ghe)
| step_skip_loop2: forall  I1 I2  s1 s2 k e ghe h,
    step (State Sskip (Kloop2  I1 I2 s1 s2 k) e h ghe)
          (State (Sloop I1 I2  s1 s2) k e h ghe)
| step_break_loop2: forall  I1 I2 s1 s2 k e ghe h,
    step (State Sbreak (Kloop2  I1 I2  s1 s2 k) e h ghe)
          (State Sskip k e h ghe)
         
(*Pure Logical*)
| step_assume: forall e ghe h P c,
    eval_assert P e h  ghe ->
    step (State (Sassert P) c e h ghe)
         (State  Sskip c e h ghe)
| step_assert_pass: forall e ghe h P c,
    eval_assert P e h ghe ->
    step (State (Sassert P) c e h ghe)
         (State Sskip c e h ghe)

(* Ghost steps *)
| step_ghost: forall gs k e ghe h,
    step (State (Sghost gs) k e h ghe)
         (GState gs k e h ghe)
| step_gskip: forall k e ghe h,
    step (GState GSskip k e h ghe)
         (State Sskip k e h ghe)
| step_gset: forall ex x v k e ghe h,
    eval_gexpr ex e h ghe v ->
    step (GState (GSset x ex)  k e h ghe)
         (GState GSskip k e h (update_env ghe x (Some v)))
| step_gseq: forall gs1 gs2 k e ghe h,
    step (GState (GSseq gs1 gs2) k e h ghe)
         (GState gs1 (GKseq gs2 k) e h ghe).

Inductive step_star: state -> state -> Prop:=
| stutter : forall st, step_star st st
| Star_step : forall st st' st'', step_star st st' ->
                             step st' st'' ->
                             step_star st st''.

Inductive safe_state:
  state-> Prop:=
| safe_skip: forall e ghe h k,
    safe_state (State Sskip k e h ghe)
| safe_seq: forall e ghe h s1 s2 k,
    safe_state (State (Sseq s1 s2) k e h ghe)
| safe_continue_seq: forall s k e ghe h,
    safe_state (State Scontinue (Kseq s k) e h ghe)
| safe_break_seq: forall s k e ghe h,
    safe_state (State Sbreak (Kseq s k) e h ghe)
| safe_set: forall e ghe h ex2 k v c,
    eval_expr ex2 e h v ->
    safe_state (State (Sset k ex2) c e h ghe)
| safe_assign:
    forall e ghe h ex1 ex2 v c addr,
    eval_lvalue ex1 e h addr ->
    eval_expr ex2 e h v ->
    safe_state (State (Sassign ex1 ex2) c e h ghe)
               
| safe_ifthenelse1: forall e ghe h a v ty s1 s2 k b,
    eval_expr a e h v ->
    bool_val v ty = Some b ->
    safe_state (State (Sifthenelse a s1 s2) k e h ghe)
        
| safe_steploop: forall  I1 I2 s1 s2 k e ghe h,
      safe_state (State (Sloop  I1 I2  s1 s2) k e h ghe)
| safe_step_skip_or_continue_loop1:
    forall I1 I2 s1 s2 k e ghe h x,
    x = Sskip \/ x = Scontinue ->
    safe_state (State x (Kloop1  I1 I2 s1 s2 k) e h ghe)
| safe_step_break_loop1: forall  I1 I2  s1 s2 k e ghe h,
    safe_state (State Sbreak (Kloop1  I1 I2 s1 s2 k) e h ghe)
| safe_step_skip_loop2: forall  I1 I2  s1 s2 k e ghe h,
    safe_state (State Sskip (Kloop2  I1 I2  s1 s2 k) e h ghe)
| safe_step_break_loop2: forall  I1 I2  s1 s2 k e ghe h,
    safe_state (State Sbreak (Kloop2  I1 I2 s1 s2 k) e h ghe)
         
| safe_assume: forall e ghe h P c,
    safe_state (State (Sassume P) c e h ghe)
| safe_assert_pass: forall e ghe h P c,
    eval_assert P e h ghe ->
    safe_state (State (Sassert P) c e h ghe)

(* Ghost steps *)
| safe_ghost: forall gs k e ghe h,
    safe_state (State (Sghost gs) k e h ghe)
| safe_gskip: forall k e ghe h,
    safe_state (GState GSskip k e h ghe)
| safe_gset: forall ex x v k e ghe h,
    eval_gexpr ex e h ghe v ->
    safe_state (GState (GSset x ex)  k e h ghe)
| safe_gseq: forall gs1 gs2 k e ghe h,
    safe_state (GState (GSseq gs1 gs2) k e h ghe).

(** * 11) Safety *)
Definition Safe (st:state):Prop:=
  forall st', step_star st st' ->
         safe_state st'.