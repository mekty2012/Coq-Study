From GRP Require Export group.

Lemma grp_identity_unique :
  forall G g0, (forall g, gr_op G g g0 = g) -> (forall g, gr_op G g0 g = g) -> g0 = gr_id G.
Proof.
  intros.
  pose proof (H (gr_id G)).
  rewrite (gr_id_l G) in H1. apply H1.
  Qed.

Lemma grp_inv_unique :
  forall G g g', (gr_op G g g') = gr_id G -> (gr_op G g' g) = gr_id G -> g' = gr_inv G g.
Proof.
  intros.
  assert (g' = gr_op G g' (gr_id G)).
  { rewrite (gr_id_r G). reflexivity. }
  rewrite H1.
  replace (gr_id G) with (gr_op G g (gr_inv G g)).
  rewrite <- (gr_op_assoc G). rewrite H0.
  rewrite (gr_id_l G). reflexivity.
  apply gr_inv_r.
  Qed.

Lemma grp_inv_involutive :
  forall G g, gr_inv G (gr_inv G g) = g.
Proof.
  intros.
  symmetry. apply grp_inv_unique.
  - apply gr_inv_l.
  - apply gr_inv_r.
  Qed.

Lemma grp_inv_op :
  forall G g1 g2, gr_inv G (gr_op G g1 g2) = gr_op G (gr_inv G g2) (gr_inv G g1).
Proof.
  intros. symmetry. apply grp_inv_unique.
  - rewrite gr_op_assoc.
    rewrite <- (gr_op_assoc G g2 (gr_inv G g2) (gr_inv G g1)).
    rewrite gr_inv_r. rewrite gr_id_l. rewrite gr_inv_r. reflexivity.
  - rewrite gr_op_assoc.
    rewrite <- (gr_op_assoc G (gr_inv G g1) g1 g2).
    rewrite gr_inv_l. rewrite gr_id_l. rewrite gr_inv_l. reflexivity.
  Qed.

Lemma grp_id_inv_id :
  forall G, gr_inv G (gr_id G) = gr_id G.
Proof.
  intros. symmetry. apply grp_inv_unique.
  - apply gr_id_l.
  - apply gr_id_l.
  Qed.

Lemma grp_right_cancel :
  forall G g1 g2 x, gr_op G g1 x = gr_op G g2 x -> g1 = g2.
Proof.
  intros.
  assert (gr_op G (gr_op G g1 x) (gr_inv G x) = gr_op G (gr_op G g2 x) (gr_inv G x)).
  { rewrite H. reflexivity. }
  rewrite gr_op_assoc in H0. rewrite gr_inv_r in H0.
  rewrite gr_op_assoc in H0. rewrite gr_inv_r in H0.
  rewrite gr_id_r in H0. rewrite gr_id_r in H0.
  apply H0.
  Qed.

Lemma grp_left_cancel :
  forall G g1 g2 x, gr_op G x g1 = gr_op G x g2 -> g1 = g2.
Proof.
  intros.
  assert (gr_op G (gr_inv G x) (gr_op G x g1) = gr_op G (gr_inv G x) (gr_op G x g2)).
  { rewrite H. reflexivity. }
  rewrite <- gr_op_assoc in H0. rewrite gr_inv_l in H0.
  rewrite <- gr_op_assoc in H0. rewrite gr_inv_l in H0.
  rewrite gr_id_l in H0. rewrite gr_id_l in H0.
  apply H0.
  Qed.

Fixpoint mult {G : group} (g : G) (n : nat) : G :=
  match n with
  | 0 => gr_id G
  | S n' => gr_op G g (mult g n')
  end.


