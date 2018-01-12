(*For finite sets*)
Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)
Require Import Coq.Classes.Morphisms.

Definition fresh_var (set_vars:PSet.t): positive:=
  match (max_elt set_vars) with
  | Some x => x~1
  | None => 1
  end.