Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.


Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*) 

Require Import VCC.Heap.

(** *(0 Variables *)
(* Variables are represented as positives *)
Definition ident := positive.

(** * 1)Values *)
(*The memory model has to be expanded on*)
(*Blocks and ptrofs, should come from there*)
Definition block:=positive.
Definition ptrofs:=int.


Inductive val: Type :=
| Vundef: val
| Vint: int -> val
| Vptr: (positive * Int.int) -> val.
                                 
(* Ghost Values *)
                                 
Inductive gval: Type :=
| GVptr: (positive * Int.int)  -> gval
| GVnat: nat -> gval
| GVbool: bool -> gval
| GVheap: @heap val -> gval.

(* Union values*)
Inductive uval:= | RV: val -> uval | GV: gval -> uval.
Coercion RV : val >-> uval.
Coercion GV : gval >-> uval.
Notation heap:= (@heap val).

Notation val_zero:= (Vint Int.zero).

(** * 2) Types *)

Inductive type : Type :=
| Tvoid: type                                            (* the void type *)
| Tint: (*intsize -> signedness -> attr ->*) type               (* integer types *)
| Tpointer: type -> type.

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
