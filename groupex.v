From GRP Require Export group.
From Coq Require Import Lists.List.
From Coq Require Import Omega.

Record finite_evid (X : Type) : Type := mk_fin_evid {
  fin_enum : list X;
  is_enum : forall x, In x fin_enum;
  is_unique : NoDup fin_enum
  }.

Record fin_ord (n : nat) : Type := {
  fin_ord_m : nat;
  fin_ord_le : fin_ord_m < S n
}.

Theorem fin_ord_eq (n : nat) :
  forall m1 m2 (H1:m1 < S n) (H2:m2 < S n),
  m1 = m2 ->
  {|fin_ord_m:=m1;fin_ord_le:=H1|} = {|fin_ord_m:=m2;fin_ord_le:=H2|}.
Proof.
  intros. subst. assert (H1 = H2). apply proof_irrelevance.
  rewrite H. reflexivity. Qed.

Section finite_cyclic_group.
(* To eliminate considering Z_0, we use have fin_ord n = Z_{n+1}. *)

Definition cycle_fin_ord_add (n : nat) : fin_ord n -> fin_ord n -> fin_ord n.
Proof.
  intros. destruct H. destruct H0.
  exists (Nat.modulo (fin_ord_m0 + fin_ord_m1) (S n)).
  apply PeanoNat.Nat.mod_upper_bound.
  intro. subst. inversion fin_ord_le1; discriminate.
  Defined.

Definition cycle_fin_ord_id (n : nat) : fin_ord n.
  exists 0. omega.
  Defined.

Definition cycle_fin_ord_inv (n : nat) : fin_ord n -> fin_ord n.
  intros. destruct H.
  exists (Nat.modulo (S n - fin_ord_m0) (S n)).
  apply PeanoNat.Nat.mod_upper_bound.
  intro; discriminate.
  Defined.

Definition fin_grp (n : nat) : group.
  exists (fin_ord n) (cycle_fin_ord_add n) (cycle_fin_ord_id n) (cycle_fin_ord_inv n).
  - intros. destruct x; destruct y; destruct z. apply fin_ord_eq.
    rewrite Nat.add_mod_idemp_l. rewrite Nat.add_mod_idemp_r. rewrite plus_assoc.
    reflexivity. all : intro; discriminate.
  - intros. destruct x. apply fin_ord_eq. rewrite Nat.add_0_l.
    apply Nat.mod_small. assumption.
  - intros. destruct x. apply fin_ord_eq. rewrite Nat.add_0_r.
    apply Nat.mod_small. assumption.
  - intros. destruct x. apply fin_ord_eq.
    rewrite Nat.add_mod_idemp_l. rewrite Nat.sub_add.
    apply Nat.mod_same.
    2 : omega. all : intro; discriminate.
  - intros. destruct x. apply fin_ord_eq.
    rewrite Nat.add_mod_idemp_r. rewrite Nat.add_sub_assoc.
    rewrite minus_plus. apply Nat.mod_same. 2 : omega. all : intro; discriminate.
  Defined.

End finite_cyclic_group.

Section symmetric_group.
(* The main hard point here is to construct inverse of function.
   In specific, we require axiom of dependent choice which is not compuatble.
   If we restrict our viewpoint to symmetric group over Z_n, it is a lot simpler,
   we have library that allows finite choice.
 *)



End symmetric_group.





