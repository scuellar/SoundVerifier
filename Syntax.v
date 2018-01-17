Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)

Require Import VCC.Expressions.

(*+ Syntax *)


Require Import VCC.Basics.
Require Import VCC.Expressions.
Require Import VCC.AssertionSemantics.

(** * 5) Statements *)

Inductive statement : Type :=
| Sskip : statement                                                  (* do nothing  *)
| Sset : ident -> type -> expr -> statement                             (* x=i         *) (*
| Sassign : expr -> expr -> statement                                  (* x*=i         *) *)
| Sseq :   statement -> statement -> statement                         (* sequence    *)
| Sifthenelse : expr -> statement -> statement -> statement             (* conditional *)
| Sloop: assertion ->  assertion ->  statement -> statement -> statement (* infinite loop *)
| Sbreak : statement                                                 (* break statement *)
| Scontinue : statement                                              (* continue statement *)   
| Sassert : assertion -> statement                                    (* assert P    *)
| Sassume : assertion -> statement                                    (* assume P    *).



(** The C loops are derived forms. *)

Definition Swhile (inv:assertion) (e: expr) (s: statement) :=
  Sloop inv (inv /\ expr_zero == e)%assert (Sseq (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (inv:assertion)(s: statement) (e: expr) :=
  Sloop inv (inv /\ expr_zero == e)%assert s (Sifthenelse e Sskip Sbreak).

Definition Sfor (inv:assertion)(s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Sseq s1 (Sloop inv (inv /\ expr_zero == e2)%assert (Sseq (Sifthenelse e2 Sskip Sbreak) s3) s4).
