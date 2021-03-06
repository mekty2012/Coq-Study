From GRP Require Export group.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ProofIrrelevance.
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

Section dihedral_group.

Inductive dihedral_els (n : nat) : Type :=
| clockwise (o : fin_ord n) : dihedral_els n
| counterclockwise (o : fin_ord n) : dihedral_els n.



End dihedral_group.

Section symmetric_group.
(* 
   The main hard point here is to construct inverse of function.
   In specific, we require axiom of dependent choice which is not compuatble.
   If we restrict our viewpoint to symmetric group over Z_n, it is a lot simpler,
   we have library that allows finite choice (which is computable).
 *)

Record invertible_function (A : Type) : Type := mk_invert {
  invert_f : A -> A;
  invert_g : A -> A;
  left_inv : forall a, invert_f (invert_g a) = a;
  right_inv : forall a, invert_g (invert_f a) = a
}.

Lemma invertible_function_eq (A : Type) :
  forall (f1 f2 g1 g2 : A -> A) 
         (Hl1 : forall a, f1 (g1 a) = a)
         (Hl2 : forall a, f2 (g2 a) = a)
         (Hr1 : forall a, g1 (f1 a) = a)
         (Hr2 : forall a, g2 (f2 a) = a),
    f1 = f2 -> g1 = g2 -> 
    mk_invert A f1 g1 Hl1 Hr1 = mk_invert A f2 g2 Hl2 Hr2.
Proof.
  intros. subst. assert (Hl1 = Hl2) by apply proof_irrelevance.
  assert (Hr1 = Hr2) by apply proof_irrelevance. subst.
  reflexivity. Defined.

Definition compose_invertible_function (A : Type) 
   : invertible_function A -> invertible_function A -> invertible_function A.
Proof.
  intros. destruct X. destruct X0.
  exists (fun a => invert_f1 (invert_f0 a)) (fun a => invert_g0 (invert_g1 a)).
  - intros. rewrite left_inv0. rewrite left_inv1. reflexivity.
  - intros. rewrite right_inv1. rewrite right_inv0. reflexivity.
  Defined.

Definition id_invertible_function (A : Type) : invertible_function A.
Proof.
  exists (fun a => a) (fun a => a).
  all : reflexivity. Defined.

Definition inv_invertible_function (A : Type) (a : invertible_function A) 
                                   : invertible_function A.
Proof.
  exists (invert_g A a) (invert_f A a).
  - apply (right_inv A a).
  - apply (left_inv A a).
  Defined.

Definition symmetric_group (A : Type) : group.
  exists (invertible_function A) (compose_invertible_function A)
  (id_invertible_function A) (inv_invertible_function A).
  - intros. destruct x. destruct y. destruct z. simpl in *.
    apply invertible_function_eq.
    + reflexivity.
    + reflexivity.
  - intros. destruct x. simpl in *. apply invertible_function_eq.
    + apply functional_extensionality. reflexivity.
    + apply functional_extensionality. reflexivity.
  - intros. destruct x. simpl in *. apply invertible_function_eq.
    + apply functional_extensionality. reflexivity.
    + apply functional_extensionality. reflexivity.
  - intros. destruct x. simpl in *. apply invertible_function_eq.
    + apply functional_extensionality. assumption.
    + apply functional_extensionality. assumption.
  - intros. destruct x. simpl in *. apply invertible_function_eq.
    + apply functional_extensionality. assumption.
    + apply functional_extensionality. assumption.
  Defined.

End symmetric_group.

Section quaternion_group.

Inductive quat : Type :=
  | quat_one
  | quat_i
  | quat_j
  | quat_k
  | M_quat_one
  | M_quat_i
  | M_quat_j
  | M_quat_k
  .

Definition quat_op (q1 q2 : quat) : quat :=
  match q1 with
  | quat_one=> q2
  | quat_i=> match q2 with
          | quat_one=> quat_i
          | quat_i=> M_quat_one
          | quat_j=> quat_k
          | quat_k=> M_quat_j
          | M_quat_one=> M_quat_i
          | M_quat_i=> quat_one
          | M_quat_j=> M_quat_k
          | M_quat_k=> quat_j
         end
  | quat_j=> match q2 with 
          | quat_one=> quat_j
          | quat_i=> M_quat_k
          | quat_j=> M_quat_one
          | quat_k=> quat_i
          | M_quat_one=> M_quat_j
          | M_quat_i=> quat_k
          | M_quat_j=> quat_one
          | M_quat_k=> M_quat_i
         end
  | quat_k=> match q2 with 
          | quat_one=> quat_k
          | quat_i=> quat_j
          | quat_j=> M_quat_i
          | quat_k=> M_quat_one
          | M_quat_one=> M_quat_k
          | M_quat_i=> M_quat_j
          | M_quat_j=> quat_i
          | M_quat_k=> quat_one
         end
  | M_quat_one=> match q2 with 
          | quat_one=> M_quat_one
          | quat_i=> M_quat_i
          | quat_j=> M_quat_j
          | quat_k=> M_quat_k
          | M_quat_one=> quat_one
          | M_quat_i=> quat_i
          | M_quat_j=> quat_j
          | M_quat_k=> quat_k
         end
  | M_quat_i=> match q2 with
          | quat_one=> M_quat_i
          | quat_i=> quat_one
          | quat_j=> M_quat_k
          | quat_k=> quat_j
          | M_quat_one=> quat_i
          | M_quat_i=> M_quat_one
          | M_quat_j=> quat_k
          | M_quat_k=> M_quat_j
         end
  | M_quat_j=> match q2 with 
          | quat_one=> M_quat_j
          | quat_i=> quat_k
          | quat_j=> quat_one
          | quat_k=> M_quat_i
          | M_quat_one=> quat_j
          | M_quat_i=> M_quat_k
          | M_quat_j=> M_quat_one
          | M_quat_k=> quat_i
         end
  | M_quat_k=> match q2 with 
          | quat_one=> M_quat_k
          | quat_i=> M_quat_j
          | quat_j=> quat_i
          | quat_k=> quat_one
          | M_quat_one=> quat_k
          | M_quat_i=> quat_j
          | M_quat_j=> M_quat_i
          | M_quat_k=> M_quat_one
         end
  end.

Definition quat_inv (q:quat) : quat :=
  match q with
  | quat_one=> quat_one
  | quat_i=> M_quat_i
  | quat_j=> M_quat_j
  | quat_k=> M_quat_k
  | M_quat_one=> M_quat_one
  | M_quat_i=> quat_i
  | M_quat_j=> quat_j
  | M_quat_k=> quat_k
  end.

Definition quaternion_group : group.
  exists quat (quat_op) quat_one(quat_inv).
  - intros [] [] []. all : reflexivity.
  - intros []. all : reflexivity.
  - intros []. all : reflexivity.
  - intros []. all : reflexivity.
  - intros []. all : reflexivity.
Defined.
End quaternion_group.


Section permutation_group.

Definition perm_grp_act (G : group) (g : G) (A : Type) (sig : group_action G A): A -> A :=
(fun (a : A) => (grp_act G A sig g a)).

Record perms (A : Type) : Type := mk_perm {
  perm :> A -> A;
  perm_inj : forall x y, perm x = perm y -> x = y;
  perm_sur : forall y, exists x, y = perm x;
}.

Record perm_grp (G : group) (A: Type) (sig : group_action G A) : Type := mk_grp_perm {
  grp_perm :> G -> A -> A;
  is_action : exists g : G, grp_perm g = perm_grp_act G g A sig;
}.

Definition perm_grp_inverse {G : group} {A : Type} {sig : group_action G A} (p : perm_grp G A sig) : perm_grp G A sig.
Proof. destruct p. destruct is_action0.




Definition perm_group (G : group) (A: Type) (sig : group_action G A) : group.
  exists perm_grp_act (perm_grp_act G (gr_id G) A sig) 

Definition grp_perm_homo (G : group) (A : Type) (sig : group action G A): grp_homo G 