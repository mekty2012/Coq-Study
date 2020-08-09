From GRP Require Export group.
From GRP Require Export groupop.

Theorem homo_preserves_id :
  forall (G1 G2 : group) (f : grp_homo G1 G2),
    f (gr_id G1) = gr_id G2.
Proof.
  intros.
  replace (gr_id G1) with (gr_op G1 (gr_id G1) (gr_inv G1 (gr_id G1))).
  rewrite preserves_op. rewrite preserves_inv.
  rewrite gr_inv_r. reflexivity.
  rewrite gr_inv_r. reflexivity.
  Qed.

Definition kernel (G1 G2 : group) (f : grp_homo G1 G2) : subgroup_prop G1.
Proof.
  exists (fun g1 => f g1 = gr_id G2).
  - apply homo_preserves_id.
  - intros. rewrite preserves_op.
    rewrite H. rewrite H0. rewrite gr_id_l. reflexivity.
  - intros. rewrite preserves_inv. rewrite H.
    apply grp_id_inv_id.
  Defined.

Definition image (G1 G2 : group) (f : grp_homo G1 G2) : subgroup_prop G2.
Proof.
  exists (fun g2 => exists g1, f g1 = g2).
  - exists (gr_id G1). apply homo_preserves_id.
  - intros. destruct H; destruct H0.
    exists (gr_op G1 x x0). subst. apply preserves_op.
  - intros. destruct H. exists (gr_inv G1 x).
    subst. apply preserves_inv.
  Defined.