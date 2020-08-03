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
  gr : group;
  abelian : forall x y, gr_op gr x y = gr_op gr y x
  }.

Record finite_evid (X : Type) : Type := mk_fin_evid {
  fin_enum : list X;
  is_enum : forall x, In x fin_enum;
  is_unique : NoDup fin_enum
  }.

