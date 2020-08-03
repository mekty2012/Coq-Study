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

Record subgroup (G : group) : Type := mk_subgrp {
  subgr_mem :> G -> Prop;
  subgr_id : subgr_mem (gr_id G);
  subgr_op_closed : forall a b,
    subgr_mem a -> subgr_mem b -> subgr_mem (gr_op G a b);
  subgr_inv_closed : forall a,
    subgr_mem a -> subgr_mem (gr_inv G a)
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
