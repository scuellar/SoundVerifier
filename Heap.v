Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.

Require Import MSets.MSetPositive.
Import PositiveSet. Module PSet:= PositiveSet. (*For positive-indexed sets*)

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import Coq.Classes.RelationClasses.


(*+ HEAP *)

Section ParametricInVal.
  Context {val:Type}.
Definition address:= (positive * Int.int)%type.
Lemma address_dec: forall ad1 ad2: address, {ad1 = ad2} + {ad1 <> ad2}.
Proof.
  destruct ad1 as [b1 ofs1];
    destruct ad2 as [b2 ofs2].
  destruct (AST.ident_eq b1 b2);
    destruct (Int.eq_dec ofs1 ofs2);
    subst; auto; right;
      intros HH; inversion HH; subst;
        congruence.
Qed.
Definition add_eq (a1 a2:address):bool:=
  match a1, a2 with 
  | (b1, ofs1), (b2, ofs2) =>
    Pos.eqb b1 b2 &&  Int.eq ofs1 ofs2
  end.

  
Definition heap:= address -> option val.
Definition empty_heap:heap := fun _ => None.

Definition heap_equiv: relation (address -> option val) := pointwise_relation _ Logic.eq.
Global Instance Equivalenc_heap_equiv: Equivalence heap_equiv:= _.

Definition remove_heap (h:heap) (add:address): heap:=
  fun add' =>  if add_eq add add' then None else h add'.

Global Instance Proper_remove_heap: Proper ( heap_equiv ==> Logic.eq ==> heap_equiv) remove_heap.
Proof.
  intros ? ? ? ? ? ? id; subst.
  cbv delta [remove_heap] beta.
  destruct (add_eq y0 id); auto.
Qed.


Definition upd_heap (h:heap) (add:address) (v:val) : heap:=
  fun add' =>  if add_eq add add' then Some v else h add'.

Definition update_heap (h:heap) (add:address) (value:option val) : heap:=
  match value with
    | None => remove_heap h add
    | Some v =>  upd_heap h add v
  end.

Global Instance Proper_update_heap: Proper ( heap_equiv ==> Logic.eq ==> Logic.eq ==> heap_equiv) update_heap.
Proof.
  intros ? ? ? ? ? ? ? ? ? id; subst.
  destruct y1 as [v_ty|]; simpl.
  - cbv delta [update_heap upd_heap] beta.
    destruct (add_eq y0 id); auto.
  - eapply Proper_remove_heap; auto.
Qed.

Lemma int_eq_iff:
  forall i i0,
    Int.eq i i0 = true <-> i = i0.
  intros; split;
    intros; subst;
      try apply Int.eq_true; auto.
  pose proof (Int.eq_spec i i0).
  rewrite H in H0; auto.
Qed.
Lemma int_neq_iff:
  forall i i0,
    Int.eq i i0 = false <-> i <> i0.
  intros; split;
    intros; subst;
      try apply Int.eq_false; auto.
  pose proof (Int.eq_spec i i0).
  rewrite H in H0; auto.
Qed.
  
Lemma add_deq_true: forall a1 a2,
    a1 = a2 <->
    add_eq a1 a2 = true.
Proof.
  intros a1 a2; destruct a1, a2.
  unfold add_eq.
  rewrite andb_true_iff,Pos.eqb_eq, int_eq_iff.
  split; intros H; inversion H; subst; auto.
Qed.

Lemma upd_heap_gss:
  forall (h : heap) (v : val) (addr : address),
    upd_heap h addr v addr <> None.
Proof. intros.
       unfold upd_heap; simpl.
       assert (HH:addr = addr) by reflexivity.
       apply (add_deq_true) in HH.
       rewrite HH. intros; discriminate.
Qed.

Lemma add_deq_false: forall a1 a2,
    a1 <> a2 <->
    add_eq a1 a2 = false.
Proof.
  intros a1 a2; destruct a1, a2.
  unfold add_eq.
  rewrite andb_false_iff, Pos.eqb_neq, int_neq_iff.
  split; intros H.
  - apply Classical_Prop.not_and_or; intros []; subst.
    apply H; auto.
  - apply Classical_Prop.or_not_and in H.
    intros HH; apply H; inversion HH; auto.
Qed.

Ltac destruct_add_dec:=
  match goal with
  | [ |- context [add_eq ?a1 ?a2] ] =>
    match goal with
    | [ H: a1 = a2 |- _ ] =>
      let H0 := fresh "HH" in
      assert (H0:=H);
      apply add_deq_true in H0; rewrite H0; clear H0 
    | [ H: a2 = a1 |- _ ] =>
      symmetry in H;
      let H0 := fresh "HH" in
      assert (H0:=H);
      apply add_deq_true in H0; rewrite H0; clear H0 
    | [ H: a1 <> a2 |- _ ] =>
      let H0 := fresh "HH" in
      assert (H0:=H);
      apply add_deq_false in H0; rewrite H0; clear H0
    | [ H: a2 <> a1 |- _ ] =>
      let H0 := fresh "HH" in
      assert (H0: a1 <> a2) by
          (let H1 := fresh "H" in intros H1; apply H; auto);      
      apply add_deq_false in H0; rewrite H0; clear H0
    | _ =>
      let H := fresh "H" in
      let H0 := fresh "HH" in
      destruct (address_dec a1 a2) as [H | H];
      assert (H0:=H);
      [apply (add_deq_true) in H0| apply (add_deq_false) in H0];
      rewrite H0; clear H0
    end
  end.

Lemma heap_gro:
  forall id h id',
    id <> id' ->
    (remove_heap h id') id = h id.
Proof.
  cbv delta[find remove_heap] beta; intros.
  let H0 := fresh "HH" in
    assert (H0:=H).
  apply add_deq_false in HH.
  destruct_add_dec; auto.
Qed.
Lemma heap_grs:
  forall id e,
    (remove_heap e id) id = None.
Proof.
  cbv delta[find remove_heap] beta; intros.
  destruct_add_dec; auto.
  congruence.
Qed.
Lemma heap_gss:
  forall e id v_ty,
    (update_heap e id v_ty) id = v_ty.
Proof.
  intros.
  destruct v_ty; simpl.
  - cbv delta[upd_heap] beta.
    destruct_add_dec; auto.
    congruence.
  - rewrite heap_grs; reflexivity.
Qed.
Lemma heap_gso:
  forall e id id' v_ty,
    id <> id' ->
    (update_heap e id v_ty) id' = e id'.
Proof.
  intros.
  destruct v_ty; simpl.
  - cbv delta[upd_heap] beta.
    destruct_add_dec; auto.
  - rewrite heap_gro; auto.
Qed.

Lemma heap_redundant_update:
  forall e i v_ty v_ty',
    heap_equiv (update_heap (update_heap e i v_ty) i v_ty')
              (update_heap e i v_ty').
Proof.
  intros ? ? ? ? id.
  destruct v_ty', v_ty; simpl;
  unfold update_heap, upd_heap, remove_heap;
  destruct_add_dec; auto.
Qed.
Lemma heap_update_comm:
  forall e i j v_ty v_ty',
    i <> j ->
    heap_equiv (update_heap (update_heap e i v_ty) j v_ty')
              (update_heap (update_heap e j v_ty') i v_ty).
Proof.
  intros ? ? ? ? ? NEQ id.
  destruct v_ty', v_ty; simpl;
    unfold update_heap, upd_heap, remove_heap;
  repeat destruct_add_dec; subst; auto.
  contradict NEQ; auto.
  contradict NEQ; auto.
  contradict NEQ; auto.
Qed.

Lemma heap_pointless_update:
  forall e k v_ty,
    e k = v_ty ->
    heap_equiv (update_heap e k v_ty) e.
Proof.
  intros ? ? ? ? id.
  destruct v_ty; simpl;
    unfold update_heap, upd_heap, remove_heap;
  repeat destruct_add_dec; subst; auto.
Qed.

End ParametricInVal.
