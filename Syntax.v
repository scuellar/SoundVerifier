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


(** *Syntax*)

(** * Statements *)

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


(** * Continuations*)
Inductive cont: Type:=
| Kstop
| Kloop1: assertion -> assertion -> statement -> statement -> cont -> cont
| Kloop2: assertion -> assertion -> statement -> statement -> cont -> cont 
| Kseq: statement -> cont -> cont
| GKseq: gstatement -> cont -> cont.

(** * State *)

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
