(*For finite sets*)
Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)
Require Import Coq.Classes.Morphisms.

Require Import compcert.lib.Coqlib.

Require Import VCC.Tactics.

(** *Fresh Vars*)



(* Most lemmas and tactics are in Expression.v and Assertionsemantics.v 
   Relating Free_vars/free_vars_expr with fresh_var *)
(* For example free_vars_spec in AssertionSemantics.v *)


(*Computes the a variable outside the set of free variables set_vars*)
Definition fresh_var (set_vars:PSet.t): positive:=
  match (max_elt set_vars) with
  | Some x => x~1
  | None => 1
  end.


(** * Tactics *)
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