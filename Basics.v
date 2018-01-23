Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 

Require Import VCC.Heap.


(* Variables are represented as positives *)
Definition ident := positive.

(** * Values *)

(* Real Values*)
Inductive val: Type :=
| Vundef: val                       (*Undefined*)
| Vint: int -> val                   (*Unsigned integers*)
| Vptr: (positive * Int.int) -> val. (*Pointers*)
                                 
(* Ghost Values *)
Inductive gval: Type :=
| GVptr: (positive * Int.int)  -> gval
| GVnat: nat -> gval
| GVbool: bool -> gval
| GVheap: @heap val -> gval.

(* Values*)
Inductive uval:= | RV: val -> uval | GV: gval -> uval.
Coercion RV : val >-> uval.
Coercion GV : gval >-> uval.
Notation heap:= (@heap val).

Notation val_zero:= (Vint Int.zero).

(** * Types *)

(*Real Types*)
Inductive type : Type :=
| Tvoid: type                        (* oid type *)
| Tint:  type                        (* Unsigned integer types *)
| Tpointer: type -> type.             (* Pointer type *)

(*Ghost Types*)
Inductive gtype : Type :=
| GTnat: gtype
| GTbool: gtype
| GTheap: gtype
| GTpointer: type -> gtype.

Definition sizeof (t:type): Z:=
  match t with
  | Tvoid => 1
  | Tint => 4 (*only 32 int for now*)
  | Tpointer _ => 4 (*hardcoded 32 for now*)
  end.

Inductive utype:= | RT: type -> utype | GT: gtype -> utype.
Coercion RT : type >-> utype.
Coercion GT : gtype >-> utype.
