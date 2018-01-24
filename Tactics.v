
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.


(* neq is reflexive. *)
Definition neq_rel (A:Type): relation A:=
  fun (x y:A) => x <> y.
Global Instance Symmetric_neq: forall A, @Symmetric A (neq_rel A).
Proof. intros ? ? ? H ?. apply H; auto. Qed.

(* Duplicate hypothesis *)
Ltac duplicate H:= let HH := fresh "HH" in assert (HH:=H).

(* "Normal form"  hypothesis*)
Ltac normal_form_not_or:=
  repeat match goal with
         | [ H: ~ ( _ \/ _ ) |- _ ] =>
           apply Classical_Prop.not_or_and in H; destruct H
         end.
Ltac destruct_and:=
  repeat match goal with
         | [ H: _ /\ _  |- _ ] => destruct H
         end.
Ltac reduce_and:=
  repeat match goal with
         | [ |- _ /\ _  ] => split
         end.

(* Stronger form of inversion *)
(* It inverts and rewrites every *new* equality*)
(* NOTE!!: This changes the names of hypothesis!!! *)
(* I considere good practice to not depend on names*)
Ltac revert_but HH:=
  repeat match goal with
         | [ H: _ |- _ ] =>
           progress
             match H with
             | HH => idtac
             | _ => revert H
             end
         end.
Ltac invert HH:=
  revert_but HH;
  inversion HH; subst;
  intros.


(** I find this lemma very useful. 
    Particularly to prove Proper with iff.*)
Lemma forall_exists_iff: forall A (P Q: A -> Prop),
    (forall x, P x <-> Q x) -> (exists x, P x) <-> (exists x, Q x).
Proof.
  intros ? ? ? H1; split; intros [v H2]; eexists; eapply H1; eassumption.
Qed.