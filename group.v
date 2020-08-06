From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Omega.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Section group_def.
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

End group_def.

Section subgroup.
Record subgroup_bool (G : group) : Type := mk_subgrp_b {
  subgr_mem_b :> G -> bool;
  subgr_id_b : subgr_mem_b (gr_id G) = true;
  subgr_op_closed_b : forall a b,
    subgr_mem_b a = true -> subgr_mem_b b = true -> subgr_mem_b (gr_op G a b) = true;
  subgr_inv_closed_b : forall a,
    subgr_mem_b a = true -> subgr_mem_b (gr_inv G a) = true
  }.

Record subgroup_bool_els (G : group) (H : subgroup_bool G) : Type := {
  subgr_b_g :> G; subgr_b_H : H subgr_b_g = true }.

Lemma subgrp_bool_els_eq (G : group) (g1 g2 : G) (H : subgroup_bool G)
                         (H1 : H g1 = true) (H2 : H g2 = true) :
  g1 = g2 -> {|subgr_b_g:=g1; subgr_b_H:=H1|} = {|subgr_b_g:=g2; subgr_b_H:=H2|}.
Proof.
  intro. subst. assert (H1 = H2). { apply proof_irrelevance. }
  subst. reflexivity. Qed.

Definition subgroup_bool_op (G : group) (H : subgroup_bool G) :
  (subgroup_bool_els G H) ->
  (subgroup_bool_els G H) ->
  (subgroup_bool_els G H).
Proof.
  intros. destruct H. simpl. destruct X. destruct X0.
  exists (gr_op G subgr_b_g0 subgr_b_g1). apply subgr_op_closed_b0.
  apply subgr_b_H0. apply subgr_b_H1. Defined.

Definition subgroup_bool_id (G : group) (H : subgroup_bool G) :
  subgroup_bool_els G H.
Proof.
  exists (gr_id G). destruct H. apply subgr_id_b0. Defined.

Definition subgroup_bool_inv (G : group) (H : subgroup_bool G) :
  subgroup_bool_els G H ->
  subgroup_bool_els G H.
Proof.
  intros. destruct X. destruct H. exists (gr_inv G subgr_b_g0).
  apply subgr_inv_closed_b0. apply subgr_b_H0. Defined.

Lemma bool_eq_refl :
  forall (b1 b2 : bool) (p q : b1 = b2), p = q.
Proof.
  intros b1 b2. destruct p. intro. symmetry. 
  apply Eqdep_dec.UIP_refl_bool. Qed.

Definition subgroup_bool_group (G : group) (H : subgroup_bool G): group.
Proof.
  exists (subgroup_bool_els G H) (subgroup_bool_op G H)
         (subgroup_bool_id G H) (subgroup_bool_inv G H).
  - (* Associativity *)
    intros. destruct x. destruct y. destruct z.
    destruct G; destruct H; simpl in *.
    apply subgrp_bool_els_eq. apply gr_op_assoc0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_bool_els_eq. apply gr_id_l0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_bool_els_eq. apply gr_id_r0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_bool_els_eq. simpl. apply gr_inv_l0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_bool_els_eq. simpl. apply gr_inv_r0.
  Qed.

Record subgroup_prop (G : group) : Type := mk_subgrp_p {
  subgr_mem_p :> G -> Prop;
  subgr_id_p : subgr_mem_p (gr_id G);
  subgr_op_closed_p : forall a b,
    subgr_mem_p a -> subgr_mem_p b -> subgr_mem_p (gr_op G a b);
  subgr_inv_closed_p : forall a,
    subgr_mem_p a -> subgr_mem_p (gr_inv G a)
  }.

Record subgroup_prop_els (G : group) (H : subgroup_prop G) : Type := {
  subgr_p_g :> G; subgr_p_H : H subgr_p_g }.

Lemma subgrp_prop_els_eq (G : group) (g1 g2 : G) (H : subgroup_prop G)
                         (H1 : H g1) (H2 : H g2) :
  g1 = g2 -> {|subgr_p_g:=g1; subgr_p_H:=H1|} = {|subgr_p_g:=g2; subgr_p_H:=H2|}.
Proof.
  intro. subst. assert (H1 = H2). { apply proof_irrelevance. }
  subst. reflexivity. Qed.

Definition subgroup_prop_op (G : group) (H : subgroup_prop G) :
  (subgroup_prop_els G H) ->
  (subgroup_prop_els G H) ->
  (subgroup_prop_els G H).
Proof.
  intros. destruct H. simpl. destruct X. destruct X0.
  exists (gr_op G subgr_p_g0 subgr_p_g1). apply subgr_op_closed_p0.
  apply subgr_p_H0. apply subgr_p_H1. Defined.

Definition subgroup_prop_id (G : group) (H : subgroup_prop G) :
  subgroup_prop_els G H.
Proof.
  exists (gr_id G). destruct H. apply subgr_id_p0. Defined.

Definition subgroup_prop_inv (G : group) (H : subgroup_prop G) :
  subgroup_prop_els G H ->
  subgroup_prop_els G H.
Proof.
  intros. destruct X. destruct H. exists (gr_inv G subgr_p_g0).
  apply subgr_inv_closed_p0. apply subgr_p_H0. Defined.

Definition subgroup_prop_group (G : group) (H : subgroup_prop G): group.
Proof.
  exists (subgroup_prop_els G H) (subgroup_prop_op G H)
         (subgroup_prop_id G H) (subgroup_prop_inv G H).
  - (* Associativity *)
    intros. destruct x. destruct y. destruct z.
    destruct G; destruct H; simpl in *.
    apply subgrp_prop_els_eq. apply gr_op_assoc0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_prop_els_eq. apply gr_id_l0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_prop_els_eq. apply gr_id_r0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_prop_els_eq. simpl. apply gr_inv_l0.
  - intros. destruct x. destruct G; destruct H; simpl in *.
    apply subgrp_prop_els_eq. simpl. apply gr_inv_r0.
  Qed.
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

Inductive subgrp_gen (G : group) (S : G -> Prop) : G -> Prop :=
| subgrp_gen_base (g : G) (H : S g) : subgrp_gen G S g
| subgrp_gen_add (g1 g2 : G) (H1 : subgrp_gen G S g1) (H2 : subgrp_gen G S g2) :
                 subgrp_gen G S (gr_op G g1 g2)
| subgrp_gen_inv (g : G) (H : subgrp_gen G S g) : subgrp_gen G S (gr_inv G g).

Definition subgrp_generate (G : group) (S : G -> Prop) (g : G) (H : S g) : subgroup_prop G.
  exists (subgrp_gen G S).
  - pose proof (subgrp_gen_base G S g H).
    pose proof (subgrp_gen_inv G S g H0).
    pose proof (subgrp_gen_add G S g (gr_inv G g) H0 H1).
    destruct G; simpl in *.
    replace (gr_op0 g (gr_inv0 g)) with (gr_id0) in H2.
    apply H2. auto.
  - intros. apply subgrp_gen_add; assumption.
  - intros. apply subgrp_gen_inv; assumption.
  Defined.

Lemma subgrp_generate_correct (G : group) :
  forall (S : G -> Prop) (H : subgroup_prop G),
  (forall g, S g -> H g) -> (forall g, subgrp_gen G S g -> H g).
Proof.
  intros. induction H1.
  - apply H0. apply H1.
  - destruct H; simpl in *. apply subgr_op_closed_p0.
    assumption. assumption.
  - destruct H; simpl in *. apply subgr_inv_closed_p0.
    assumption.
  Qed.
End subgroup.

Section homomorphism.
Record grp_homo (G1 G2 : group) : Type := mk_grp_homo {
  grp_homo_f :> G1 -> G2;
  is_homo : forall x y, grp_homo_f (gr_op G1 x y) = gr_op G2 (grp_homo_f x) (grp_homo_f y)
  }.

Record grp_iso (G1 G2 : group) : Type := mk_grp_iso {
  grp_iso_f :> grp_homo G1 G2;
  grp_iso_inj : forall x y, grp_iso_f x = grp_iso_f y -> x = y;
  grp_iso_sur : forall y, exists x, grp_iso_f x = y
  }.
End homomorphism.

Section construction.

Definition direct_product (A : group) (B : group) : group.
  exists (prod A B) 
         (fun p1 => fun p2 =>
           match p1 with
           | pair a1 b1 =>
             match p2 with
             | pair a2 b2 =>
               pair (gr_op A a1 a2) (gr_op B b1 b2)
             end
           end)
         (pair (gr_id A) (gr_id B))
         (fun p =>
           match p with
           | pair a b => pair (gr_inv A a) (gr_inv B b)
           end).
  - intros. destruct x. destruct y. destruct z.
    rewrite (gr_op_assoc A). rewrite (gr_op_assoc B).
    reflexivity.
  - intros. destruct x. rewrite (gr_id_l A). rewrite (gr_id_l B).
    reflexivity.
  - intros. destruct x. rewrite (gr_id_r A). rewrite (gr_id_r B).
    reflexivity.
  - intros. destruct x. rewrite (gr_inv_l A). rewrite (gr_inv_l B).
    reflexivity.
  - intros. destruct x. rewrite (gr_inv_r A). rewrite (gr_inv_r B).
    reflexivity.
  Defined.

(* Prove universal properties of direct product. *)

Theorem direct_product_univ :
  forall (G1 G2 : group),
  (forall (G : group), forall (f1 : grp_homo G G1) (f2 : grp_homo G G2),
    exists (f : grp_homo G (direct_product G1 G2)),
      forall (g : G),
        pair (f1 g) (f2 g) = f g).
Proof.
  Admitted.

Definition indexed_direct_product {A : Type} (ind : A -> group) : group.
  exists (forall (a : A), ind a)
         (fun f1 => fun f2 =>
           fun a => (gr_op (ind a) (f1 a) (f2 a)))
         (fun a => (gr_id (ind a)))
         (fun f => fun a => (gr_inv (ind a) (f a)))
  .
  - intros. apply functional_extensionality_dep.
    intro. apply (gr_op_assoc (ind x0)).
  - intros. apply functional_extensionality_dep.
    intro. apply (gr_id_l (ind x0)).
  - intros. apply functional_extensionality_dep.
    intro. apply (gr_id_r (ind x0)).
  - intros. apply functional_extensionality_dep.
    intro. apply (gr_inv_l (ind x0)).
  - intros. apply functional_extensionality_dep.
    intro. apply (gr_inv_r (ind x0)).
  Defined.

Theorem indexed_direct_product_univ :
  forall (A : Type) (ind : A -> group),
  (forall (G : group), forall (fun_fam : forall (a : A), grp_homo G (ind a)),
    exists (f : grp_homo G (indexed_direct_product ind)),
      forall (g : G),
        forall (a : A), (f g) a = (fun_fam a) g).
Proof.
  Admitted.

End construction.


