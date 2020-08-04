From GRP Require Export group.
From Coq Require Import Omega.

Record fin_ord (n : nat) : Type := {
  fin_ord_m : nat;
  fin_ord_le : fin_ord_m < S n
}.

Definition fin_ord_add (n : nat) : fin_ord n -> fin_ord n -> fin_ord n.
Proof.
  intros. destruct H. destruct H0.
  exists (Nat.modulo (fin_ord_m0 + fin_ord_m1) (S n)).
  apply PeanoNat.Nat.mod_upper_bound.
  intro. subst. inversion fin_ord_le1; discriminate.
  Defined.

Definition fin_ord_id (n : nat) : fin_ord n.
  exists 0. omega.
  Defined.

Definition fin_ord_inv (n : nat) : fin_ord n -> fin_ord n.
  intros. destruct H.
  exists (Nat.modulo (S n - fin_ord_m0) (S n)).
  apply PeanoNat.Nat.mod_upper_bound.
  intro; discriminate.
  Defined.

Definition fin_grp (n : nat) : group.
  exists (fin_ord n) (fin_ord_add n) (fin_ord_id n) (fin_ord_inv n).
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  Admitted.