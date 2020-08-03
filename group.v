From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Omega.

Record group : Type := mk_grp {
  gr_els :> Type;
  gr_op : gr_els -> gr_els -> gr_els;
  gr_id : gr_els;
  gr_inv : gr_els -> gr_els;
  gr_op_assoc : forall x y z, gr_op (gr_op x y) z = gr_op x (gr_op y z);
  gr_id_l : forall x, gr_op gr_id x = x;
  gr_id_r : forall x, gr_op x gr_id = x;
  gr_inv_l : forall x, gr_op (gr_inv x) x = gr_id;
  gr_inv_r : forall x, gr_op x (gr_inv x) = gr_id
  }.

Record abel_group : Type := mk_abl_grp {
  ab_gr : group;
  ab_abelian : forall x y, gr_op ab_gr x y = gr_op ab_gr y x
  }.

Record finite_evid (X : Type) : Type := mk_fin_evid {
  fin_enum : list X;
  is_enum : forall x, In x fin_enum;
  is_unique : NoDup fin_enum
  }.

Record subgroup_bool (G : group) : Type := mk_subgrp_b {
  subgr_mem_b :> G -> bool;
  subgr_id_b : subgr_mem_b (gr_id G) = true;
  subgr_op_closed_b : forall a b,
    subgr_mem_b a = true -> subgr_mem_b b = true -> subgr_mem_b (gr_op G a b) = true;
  subgr_inv_closed_b : forall a,
    subgr_mem_b a = true -> subgr_mem_b (gr_inv G a) = true
  }.

Record subgroup_bool_els (G : group) (H : subgroup_bool G) : Type := {
  g :> G; H : H g = true }.

Definition subgroup_bool_op (G : group) (H : subgroup_bool G) :
  (subgroup_bool_els G H) ->
  (subgroup_bool_els G H) ->
  (subgroup_bool_els G H).
Proof.
  intros. destruct H. simpl. destruct X. destruct X0.
  exists (gr_op G g0 g1). apply subgr_op_closed_b0.
  apply H0. apply H1. Defined.

Definition subgroup_bool_id (G : group) (H : subgroup_bool G) :
  subgroup_bool_els G H.
Proof.
  exists (gr_id G). destruct H. apply subgr_id_b0. Defined.

Definition subgroup_bool_inv (G : group) (H : subgroup_bool G) :
  subgroup_bool_els G H ->
  subgroup_bool_els G H.
Proof.
  intros. destruct X. destruct H. exists (gr_inv G g0).
  apply subgr_inv_closed_b0. apply H0. Defined.

Definition subgroup_bool_group (G : group) (H : subgroup_bool G): group.
Proof.
  exists (subgroup_bool_els G H) (subgroup_bool_op G H)
         (subgroup_bool_id G H) (subgroup_bool_inv G H).
  - (* Associativity *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  Admitted.

Record subgroup_prop (G : group) : Type := mk_subgrp_p {
  subgr_mem_p :> G -> Prop;
  subgr_id_p : subgr_mem_p (gr_id G);
  subgr_op_closed_p : forall a b,
    subgr_mem_p a -> subgr_mem_p b -> subgr_mem_p (gr_op G a b);
  subgr_inv_closed_p : forall a,
    subgr_mem_p a -> subgr_mem_p (gr_inv G a)
  }.

(* Instead of G->Prop, we can choose G->bool. In this case,
   Our proof that subgroup is group is simpler. However,
   this is incorrect definition, since G -> bool is implementation
   of decidable subsets of G, not any subset of G.
   
   If we take G->Prop, another problem happens. If we let our
   elements for subgroup as (x, subgr_mem x), if we have two different
   proof for subgr_mem x, we will have duplicate x.
   
   By adding proof_irrevalence axiom
   https://github.com/coq/coq/wiki/CoqAndAxioms
   we can resolve this. Or, we can restrict subgr_mem to be mere
   proposition, which is proposition that
   p q : P -> p = q.
   I'm not sure on whether this will reduce our choice for subset.
   
   Another choice is using truncation. Truncation is operator that
   receives proposition, and return mere proposition that is logically
   equivalent to original one. However, it seems this is not easy to
   use.
   https://hott.github.io/HoTT/coqdoc-html/HoTT.Truncations.Core.html
 *)

Record grp_homo (G1 G2 : group) : Type := mk_grp_homo {
  grp_homo_f :> G1 -> G2;
  is_homo : forall x y, grp_homo_f (gr_op G1 x y) = gr_op G2 (grp_homo_f x) (grp_homo_f y)
  }.

Record grp_iso (G1 G2 : group) : Type := mk_grp_iso {
  grp_iso_f :> grp_homo G1 G2;
  grp_iso_inj : forall x y, grp_iso_f x = grp_iso_f y -> x = y;
  grp_iso_sur : forall y, exists x, grp_iso_f x = y
  }.







