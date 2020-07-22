From Coq Require Import Arith.Arith.

Fail Fixpoint false_proof (p : nat) : False := false_proof p.

Fixpoint sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + (sum n')
  end.

Theorem summation :
  forall n, sum n + sum n = n * (n + 1).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. apply eq_S. rewrite <- plus_assoc. rewrite <- plus_assoc.
    apply f_equal2_plus. reflexivity.
    simpl. rewrite Nat.add_succ_r.
    apply eq_S. rewrite plus_comm. rewrite <- plus_assoc.
    rewrite IHn. rewrite Nat.mul_succ_r. rewrite plus_comm. reflexivity.
  Qed.

From Coq Require Import Omega.

Theorem summation_ring :
  forall n, sum n + sum n = n * (n + 1).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    replace (n + sum n + S (n + sum n)) with ((sum n + sum n) + n + S n).
    rewrite IHn. ring. ring. Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Definition injective {A B} (f : A -> B) : Prop :=
  forall a b, f a = f b -> a = b.

Definition FiniteType (A : Type) :=
  exists f : A -> nat, injective f /\ exists n, forall a, f a <= n.

Theorem FiniteBool : FiniteType bool.
Proof.
  unfold FiniteType. exists (fun b : bool => if b then 0 else 1).
  split.
  - unfold injective. intros.
    destruct a; destruct b; auto.
    + inversion H.
    + inversion H.
  - exists 1. intros. destruct a; omega.
  Qed.

Definition InfiniteType (A : Type) : Prop :=
  exists f : nat -> A, injective f.

Theorem InfiniteNat : InfiniteType nat.
Proof.
  exists (fun x => x). repeat intro. assumption. Qed.
