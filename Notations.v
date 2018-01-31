Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import VCC.Basics. Import Basics.
Require Import VCC.Expressions.
Require Import VCC.Syntax.

(** Types *)

Notation "'Tv'":= (Tvoid) (at level 20).
Notation "'Tptr'":= Tpointer (at level 20).

(* Expressions *)

Notation "'var' a ty ":= (Etempvar a ty) (at level 100).
Notation "'const' a ty ":= (Econst_int a ty) (at level 100).

Notation " *( ex ty )":= (Ederef ex ty) (at level 50, format "'['  *( ex  ty ) ']'").
Notation " a ( + ty ) b ":= (Ebinop Oadd a b ty) (at level 80, format "'['  a  ( +  ty )  b ']'").
Notation " a ( - ty ) b ":= (Ebinop Osub a b ty) (at level 80, format "'['  a  ( -  ty )  b ']'").
Notation " a ( * ty ) b ":= (Ebinop Omul a b ty) (at level 80, format "'['  a  ( *  ty )  b ']'").
Notation " a ( / ty ) b ":= (Ebinop Odiv a b ty) (at level 80, format "'['  a  ( /  ty )  b ']'").
Notation " a ( % ty ) b ":= (Ebinop Omod a b ty) (at level 80, format "'['  a  ( %  ty )  b ']'").
Notation " a ( & ty ) b ":= (Ebinop Oand a b ty) (at level 80, format "'['  a  ( &  ty )  b ']'").
Notation " a ( | ty ) b ":= (Ebinop Oor a b ty) (at level 80, format "'['  a  ( |  ty )  b ']'").
Notation " a ( || ty ) b ":= (Ebinop Oxor a b ty) (at level 80, format "'['  a  ( ||  ty )  b ']'").
Notation " a ( == ty ) b ":= (Ebinop Oeq a b ty) (at level 80, format "'['  a  ( ==  ty )  b ']'").
Notation " a ( != ty ) b ":= (Ebinop One a b ty) (at level 80, format "'['  a  ( !=  ty )  b ']'").
Notation " a ( < ty ) b ":= (Ebinop Olt a b ty) (at level 80, format "'['  a  ( <  ty )  b ']'").
Notation " a ( > ty ) b ":= (Ebinop Ogt a b ty) (at level 80, format "'['  a  ( >  ty )  b ']'").
Notation " a ( <= ty ) b ":= (Ebinop Ole a b ty) (at level 80, format "'['  a  ( <=  ty )  b ']'").
Notation " a ( >= ty ) b ":= (Ebinop Oge a b ty) (at level 80, format "'['  a  ( >=  ty )  b ']'").

(* Ghost Expressions *)

Delimit Scope ghost_scope with ghost.
Notation "'gvar' a ty ":= (GEtempvar a ty) (at level 100) : ghost_scope.
Notation "'gconst_p' a ty ":= (GEconst_ptr a ty) (at level 100) : ghost_scope.
Notation "'gconst_n' a ty ":= (GEconst_nat a ty) (at level 100) : ghost_scope.
Notation "'gconst_b' a ty ":= (GEconst_bool a ty) (at level 100) : ghost_scope.

Notation " *g( ex ty )":= (GEderef ex ty) (at level 50, format "'['  *g( ex  ty ) ']'") : ghost_scope.
Notation " a ( g+ ty ) b ":= (GEbinop Oadd a b ty) (at level 80, format "'['  a  ( g+  ty )  b ']'") : ghost_scope.
Notation " a ( g- ty ) b ":= (GEbinop Osub a b ty) (at level 80, format "'['  a  ( g-  ty )  b ']'") : ghost_scope.
Notation " a ( g* ty ) b ":= (GEbinop Omul a b ty) (at level 80, format "'['  a  ( g*  ty )  b ']'") : ghost_scope.
Notation " a ( g/ ty ) b ":= (GEbinop Odiv a b ty) (at level 80, format "'['  a  ( g/  ty )  b ']'") : ghost_scope.
Notation " a ( g% ty ) b ":= (GEbinop Omod a b ty) (at level 80, format "'['  a  ( g%  ty )  b ']'") : ghost_scope.
Notation " a ( g& ty ) b ":= (GEbinop Oand a b ty) (at level 80, format "'['  a  ( g&  ty )  b ']'") : ghost_scope.
Notation " a ( g| ty ) b ":= (GEbinop Oor a b ty) (at level 80, format "'['  a  ( g|  ty )  b ']'") : ghost_scope.
Notation " a ( g|| ty ) b ":= (GEbinop Oxor a b ty) (at level 80, format "'['  a  ( g||  ty )  b ']'") : ghost_scope.
Notation " a ( g== ty ) b ":= (GEbinop Oeq a b ty) (at level 80, format "'['  a  ( g==  ty )  b ']'") : ghost_scope.
Notation " a ( g!= ty ) b ":= (GEbinop One a b ty) (at level 80, format "'['  a  ( g!=  ty )  b ']'") : ghost_scope.
Notation " a ( g< ty ) b ":= (GEbinop Olt a b ty) (at level 80, format "'['  a  ( g<  ty )  b ']'") : ghost_scope.
Notation " a ( g> ty ) b ":= (GEbinop Ogt a b ty) (at level 80, format "'['  a  ( g>  ty )  b ']'") : ghost_scope.
Notation " a ( g<= ty ) b ":= (GEbinop Ole a b ty) (at level 80, format "'['  a  ( g<=  ty )  b ']'") : ghost_scope.
Notation " a ( g>= ty ) b ":= (GEbinop Oge a b ty) (at level 80, format "'['  a  ( g>=  ty )  b ']'") : ghost_scope.



(* statements *)

Notation " s1 ; s2 ":= (Sseq s1 s2) (at level 99, format "'[' s1 ; '/' s2 ']'").
Notation " a ::= ex":= (Sset a ex) (at level 50, format "'[' a ::= ex ']'" ). 
Notation " '( 'GH' s ) ":= (Sghost s) (at level 50 ).
Notation " ex1 :-> ex2":= (Sassign ex1 ex2) (at level 50, format "'[' ex1 :-> ex2 ']'").
Notation "'IF' ex 'THEN' s1 'ELSE' s2":=
  (Sifthenelse ex s1 s2)
    (at level 98, format "'[v '  'IF' ex '/' 'THEN' s1 '/' 'ELSE' s2 ']'").
Notation "'WHILE' ( ex ) {| inv |} {{ stm }}":=
  (Swhile inv ex stm)
    (at level 98, format "'[v '  'WHILE' ( ex ) '/' {| inv |} '/' {{ '/  ' stm '/' }} ']'").

(* Assertions *)


(* INTS *)

Definition nine := Int.repr 9. (*9 as an int*)
Definition ten := Int.repr 10. (*10 as an int*)