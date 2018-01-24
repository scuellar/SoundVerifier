Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 
Require Import Coq.Classes.Morphisms.

Require Import VCC.Tactics.
Require Import VCC.Basics.
Require Import VCC.Environment.
Require Import VCC.Heap.
Require Import VCC.Assertions.
Require Import VCC.Expressions.
Require Import VCC.Syntax.



(** * 11)Smallstep semantics *)


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
| step_ifthenelse: forall e ghe h a v s1 s2 k b,
    eval_expr a e h v ->
    bool_val v = Some b ->
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
               
| safe_ifthenelse1: forall e ghe h a v s1 s2 k b,
    eval_expr a e h v ->
    bool_val v = Some b ->
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