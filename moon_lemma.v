Require Import Reals.

Definition I (n : nat) : R :=
  if eq_nat_dec (n mod 3) 0 then Rpower 3 ((INR n) / 3)
  else if eq_nat_dec (n mod 3) 1 then 4 * (Rpower 3 ((INR n - 4)/3))
  else 2 * (Rpower 3 ((INR (n - 2)) / 3)).

Lemma n_q' : forall (n : nat),
  3 <= n -> (1 <= (Rpower 3 ((INR (S n))/3)) - (Rpower 3 ((INR n)/3)))%R.
Proof.
  intros. induction H.
  { unfold Rdiv. assert (INR 3 = 3)%R. simpl. Rcompute.
    rewrite H; clear H. rewrite Rinv_r. rewrite Rpower_1.
    unfold Rminus. apply (Rplus_le_reg_r 3 _ _).
    rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
    assert (1+3 = 4)%R. Rcompute. rewrite H; clear H.
    rewrite <- Rpower_mult. rewrite Rpower_pow.
    assert (3^4 = 81)%R. simpl. Rcompute. rewrite H; clear H.
    assert (4 = Rpower 64 (/3))%R. assert (64 = Rpower 4 3)%R.
    assert (3 = INR 3)%R. simpl. Rcompute. rewrite H; clear H.
    rewrite Rpower_pow. simpl. Rcompute. prove_sup. rewrite H; clear H.
    rewrite Rpower_mult. rewrite Rinv_r. rewrite Rpower_1. reflexivity.
    prove_sup. discrR. rewrite H at 1. apply Rle_Rpower_l.
    left. apply Rinv_0_lt_compat. prove_sup. split; [|left]; prove_sup. 
    prove_sup. prove_sup. discrR.
  } rewrite S_INR. rewrite S_INR at 2. unfold Rdiv.
  repeat rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
  repeat rewrite Rpower_plus. unfold Rminus.
  rewrite Ropp_mult_distr_l. rewrite <- Rmult_plus_distr_r.
  assert (1 <= (Rpower 3 (/3)))%R. assert (1 = Rpower 1 (/3))%R.
  assert (1 = (Rpower 1 3))%R. assert (3 = INR 3)%R. simpl. Rcompute.
  rewrite H0. rewrite Rpower_pow. simpl. Rcompute. prove_sup.
  rewrite H0 at 2. rewrite Rpower_mult. rewrite Rinv_r.
  rewrite Rpower_1. reflexivity. prove_sup. discrR.
  rewrite H0 at 1. apply Rle_Rpower_l. left. apply Rinv_0_lt_compat.
  prove_sup. split; [|left]; prove_sup. rewrite <- Rmult_1_r at 1.
  apply Rmult_le_compat; try (left; prove_sup; fail); assumption. Qed.

Theorem n_q : forall (n : nat),
  (INR n <= Rpower 3 ((INR n)/3))%R.
Proof.
  induction n.
  { simpl. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O. apply Rle_0_1. prove_sup.
  } destruct n eqn:H. {
    simpl. unfold Rdiv. rewrite Rmult_1_l.
    assert (1 = Rpower 1 (/3))%R. assert (1 = Rpower 1 3)%R.
    assert (3 = INR 3)%R. simpl; Rcompute. rewrite H0.
    rewrite Rpower_pow. simpl; Rcompute. prove_sup.
    rewrite H0 at 2. rewrite Rpower_mult. rewrite Rinv_r.
    rewrite Rpower_1. reflexivity. prove_sup. discrR.
    rewrite H0 at 1. apply Rle_Rpower_l. left. apply Rinv_0_lt_compat.
    prove_sup. split; [|left]; prove_sup.
  } destruct n0 eqn:H0. subst. {
    unfold Rdiv. rewrite <- Rpower_mult. rewrite Rpower_pow.
    assert (3^2 = 9)%R. simpl; Rcompute. rewrite H; clear H.
    assert (2 = Rpower 8 (/3))%R. assert (8 = Rpower 2 3)%R.
    assert (3 = INR 3)%R. simpl; Rcompute. rewrite H; clear H.
    rewrite Rpower_pow. simpl; Rcompute. prove_sup.
    rewrite H. rewrite Rpower_mult. rewrite Rinv_r.
    rewrite Rpower_1. reflexivity. prove_sup. discrR.
    simpl. rewrite H at 1. apply Rle_Rpower_l. left. apply Rinv_0_lt_compat.
    prove_sup. split; [|left]; prove_sup. prove_sup.
  } destruct n1 eqn:H1. subst. {
    simpl. assert (2 + 1 = 3)%R. Rcompute.
    rewrite H. unfold Rdiv. rewrite Rinv_r.
    rewrite Rpower_1. apply Rle_refl. prove_sup. discrR.
  } subst. remember (S (S (S n2))) as n.
  rewrite S_INR. rewrite Rplus_comm.
  simpl. apply Rle_minus in IHn.
  apply (Rplus_le_reg_r (Ropp (Rpower 3 ((INR n)/3))) _ _).
  rewrite Rplus_assoc. fold (Rminus (INR n) (Rpower 3 ((INR n)/3))).
  rewrite (Rplus_comm 1 (INR n)). rewrite <- S_INR.
  fold (Rminus (Rpower 3 ((INR (S n))/3)) (Rpower 3 ((INR n)/3))).
  assert (1 + ((INR n) - (Rpower 3 ((INR n)/3))) <= 1)%R.
  apply Ropp_le_cancel. apply Ropp_le_contravar in IHn. rewrite Ropp_0 in IHn.
  apply (Rplus_le_reg_pos_r _ (Ropp ((INR n) - (Rpower 3 ((INR n)/3)))) _ IHn).
  rewrite Ropp_plus_distr. apply Rle_refl.
  assert (3 <= n). rewrite Heqn. repeat apply le_n_S. apply Nat.le_0_l.
  apply (Rle_trans _ _ _ H (n_q' n H0)). Qed.

Lemma strongind_aux : forall (P : nat -> Prop),
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert (m <= n' \/ m = S n'). inversion H1. right. reflexivity.
    left. subst. apply H3.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'). assumption.
Qed.

Lemma weaken : forall (P : nat -> Prop),
  (forall n, (forall m, ((m <= n) -> P m))) -> (forall n, P n).
Proof.
  intros.
  apply (H n n).
  apply le_n.
Qed.

Theorem strong_induction : forall (P : nat -> Prop),
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.

Lemma mod_b_eq : forall (a b : nat),
  0 < b -> b <= a -> a mod b = (a - b) mod b.
Proof.
  intros. SearchAbout Nat.modulo. rewrite <- (Nat.mod_add (a - b) 1 b).
  rewrite Nat.mul_1_l. rewrite Nat.sub_add. reflexivity. apply H0.
  unfold not. intros. subst. inversion H. Qed.

Lemma mod_lt_gt : forall (a b c : nat),
  0 < b -> a mod b = c -> c < a -> b <= a.
Proof.
  intros. assert (H2 := lt_eq_lt_dec a b). inversion H2.
  inversion H3. apply Nat.mod_small in H4. rewrite H4 in H0.
  subst. assert (False). apply (Nat.lt_irrefl _ H1). inversion H0.
  rewrite H4. reflexivity. unfold lt in H3.
  apply le_Sn_le. apply H3. Qed.

Lemma mod3_eq_2 : forall (a : nat),
  a mod 3 <> 0 -> a mod 3 <> 1 -> a mod 3 = 2.
Proof.
  intros. assert (3 <> 0). auto.
  assert (H2 := Nat.mod_upper_bound a 3 H1).
  destruct (a mod 3). exfalso. apply H; reflexivity.
  destruct n. exfalso. apply H0; reflexivity.
  destruct n. reflexivity. unfold lt in H2.
  repeat apply le_S_n in H2. apply le_n_0_eq in H2.
  inversion H2. Qed.

Theorem I_n_q : forall (n : nat),
  (I n <= Rpower 3 ((INR n)/3))%R.
Proof.
  intros n. induction n using strong_induction.
  { unfold I; simpl. apply Rle_refl.
  } unfold I. destruct (eq_nat_dec (S n mod 3) 0). apply Rle_refl.
  destruct (eq_nat_dec (S n mod 3) 1).
  {
    assert (S n = 1 \/ 1 < S n). destruct n. left. reflexivity.
    right. unfold lt. repeat apply le_n_S. apply Peano.le_0_n.
    inversion H0.
    { inversion H1. subst. clear; simpl.
      assert (1 - 4 = -3)%R. Rcompute. rewrite H; clear.
      unfold Rdiv. rewrite <- Ropp_mult_distr_l. rewrite Rinv_r.
      rewrite Rpower_Ropp. rewrite Rpower_1. fold (Rdiv 4 3).
      rewrite Rmult_1_l. assert (4/3 = Rpower (64/27) (/3))%R.
      assert (3 = INR 3)%R. simpl; Rcompute.
      assert (64 = Rpower 4 3)%R. rewrite H. rewrite Rpower_pow.
      simpl; Rcompute. prove_sup. rewrite H0; clear H0.
      assert (27 = Rpower 3 3)%R. rewrite H at 3. rewrite Rpower_pow.
      simpl; Rcompute. prove_sup. rewrite H0. unfold Rdiv.
      rewrite <- Rpower_Ropp. rewrite <- Rpower_mult_distr. 
      repeat rewrite Rpower_mult. rewrite <- Ropp_mult_distr_l.
      repeat rewrite Rinv_r. rewrite Rpower_Ropp.
      repeat rewrite Rpower_1. reflexivity. prove_sup. prove_sup.
      discrR. rewrite H. rewrite Rpower_pow. simpl; prove_sup.
      prove_sup. rewrite Rpower_Ropp. rewrite <- H0.
      apply Rinv_0_lt_compat. prove_sup. rewrite H.
      apply Rle_Rpower_l. left; apply Rinv_0_lt_compat; prove_sup.
      split. prove_sup. apply Rinv_0_lt_compat. prove_sup.
      left. apply (Rmult_lt_reg_l 27). prove_sup. unfold Rdiv.
      rewrite <- Rmult_comm. rewrite Rmult_assoc. rewrite Rinv_l.
      rewrite Rmult_1_r. prove_sup. discrR. prove_sup. discrR.
    }
    clear H0. assert (exists n', S n = 4 + n'). exists (n - 3).
    assert (n >= 3). assert (0 < 3). auto.
    assert (H2 := mod_lt_gt (S n) 3 1 H0 e H1).
    assert (S n <> 3). unfold not. intros. rewrite H3 in e.
    simpl in e; inversion e. unfold ge. assert (H4 := le_lt_or_eq _ _ H2).
    inversion H4. unfold lt in H5. apply (le_S_n _ _ H5). symmetry in H5;
    apply H3 in H5; inversion H5. assert (S n - 4 = n - 3). reflexivity.
    rewrite <- H2. clear H2. rewrite plus_comm. rewrite Nat.sub_add.
    reflexivity. unfold ge in H0. apply (le_n_S _ _ H0).
    destruct H0 as [n' H0]. rewrite H0.
    assert (1 + n' <= n). assert (n = 3 + n'). inversion H0. reflexivity.
    rewrite H2. simpl. auto. assert (H3 := H (1 + n') H2).
    assert ((1 + n') mod 3 = 1). assert (1 + n' = S n - 3).
    rewrite H0. reflexivity. rewrite H4. rewrite <- mod_b_eq.
    apply e. auto. apply (mod_lt_gt _ _ 1). auto. apply e. apply H1.
    unfold I in H3. rewrite H4 in H3. simpl in H3.
    assert (INR (1 + n') =  match n' with | 0%nat => 1%R | S _ => (INR n') + 1%R end)%R.
    reflexivity. rewrite <- H5 in H3; clear H5.
    assert (INR (4 + n') = (INR 3) + (INR (1 + n')))%R. simpl.
    rewrite Rplus_assoc. rewrite Rplus_assoc.
    assert (1 + 1 + 1 = 3)%R. Rcompute. rewrite H5; clear H5. rewrite Rplus_comm. reflexivity.
    rewrite H5; clear H5.
    assert (Rpower 3 (((INR 3) + (INR (1 + n')) - 4)/3) = 3 * Rpower 3 (((INR (1+n')) -4)/3))%R.
    unfold Rminus. unfold Rdiv. rewrite Rmult_plus_distr_r. rewrite Rmult_plus_distr_r.
    assert (INR 3 = 3)%R. simpl; Rcompute. rewrite H5; clear H5. rewrite Rinv_r.
    rewrite Rplus_assoc. rewrite <- Rmult_plus_distr_r. rewrite Rpower_plus.
    rewrite Rpower_1. reflexivity. prove_sup. discrR. rewrite H5; clear H5.
    rewrite Rmult_comm. rewrite Rmult_comm in H3. rewrite Rmult_assoc.
    assert (Rpower 3 (((INR 3) + (INR (1 + n')))/3) = 3 * Rpower 3 ((INR (1 + n'))/3))%R.
    unfold Rdiv. rewrite Rmult_plus_distr_r. assert (INR 3 = 3)%R. simpl; Rcompute.
    rewrite H5; clear H5. rewrite Rinv_r. rewrite Rpower_plus. rewrite Rpower_1.
    reflexivity. prove_sup. discrR. rewrite H5. apply Rmult_le_compat_l. left; prove_sup. apply H3.
  } assert (H0 := mod3_eq_2 (S n) n0 n1); clear n0; clear n1.
  assert (S n = 2 \/ 2 < S n). destruct n. inversion H0. destruct n. left; reflexivity.
  right. unfold lt. repeat apply le_n_S. apply Peano.le_0_n. inversion H1.
  { rewrite H2; clear. simpl. unfold Rdiv. rewrite Rmult_0_l. rewrite Rpower_O.
    rewrite Rmult_1_r. assert (2 = Rpower 8 (/3))%R. assert (8 = Rpower 2 3)%R.
    assert (3 = INR 3)%R. simpl; Rcompute. rewrite H. rewrite Rpower_pow.
    simpl; Rcompute. prove_sup. rewrite H; clear H. rewrite Rpower_mult. rewrite Rinv_r.
    rewrite Rpower_1. reflexivity. prove_sup. discrR. rewrite <- Rpower_mult.
    assert (2 = INR 2)%R. simpl; Rcompute. rewrite H0 at 3; clear H0.
    rewrite Rpower_pow. assert (3 ^ 2 = 9)%R. simpl; Rcompute. rewrite H0; clear H0.
    rewrite H at 1; clear. apply Rle_Rpower_l. left; apply Rinv_0_lt_compat. prove_sup.
    split; [|left]; prove_sup. prove_sup. prove_sup.
  } clear H1. assert (exists n', S n = 3 + n'). exists ((S n) - 3).
  unfold lt in H2. rewrite (le_plus_minus_r _ _ H2). reflexivity. destruct H1 as [n' H1].
  assert (n' <= n). apply le_S_n. rewrite H1. simpl. auto.
  assert (H4 := H n' H3). assert (0 < 3). auto. unfold lt in H2.
  assert (H6 := mod_b_eq (S n) 3 H5 H2). rewrite H1 in H6 at 2. rewrite H0 in H6.
  symmetry in H6. rewrite minus_plus in H6. unfold I in H4. rewrite H6 in H4. simpl in H4.
  rewrite H1. assert (3 + n' - 2 = 3 + (n' -2)).
  assert (2 <= n'). destruct n'. inversion H6. destruct n'. inversion H6.
  repeat apply le_n_S. apply Peano.le_0_n. simpl. rewrite (minus_Sn_m _ _ H7).
  simpl. assert (1 <= n'). apply le_Sn_le. apply H7. rewrite (minus_Sn_m _ _ H8).
  simpl. rewrite <- minus_n_O. reflexivity. rewrite H7.
  repeat rewrite plus_INR. unfold Rdiv. rewrite Rmult_plus_distr_r. rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r. assert (INR 3 = 3)%R. simpl; Rcompute. rewrite H8; clear H8.
  rewrite Rinv_r. rewrite <- Rmult_plus_distr_r. repeat rewrite Rpower_plus.
  repeat rewrite Rpower_1. rewrite Rmult_comm. rewrite Rmult_assoc. rewrite
  Rmult_comm in H4. unfold Rdiv in H4. apply Rmult_le_compat_l. left. prove_sup. apply H4.
  prove_sup. discrR. Qed.

Definition sum (l : list nat) : nat := List.fold_right plus 0 l.
Definition prod (l : list nat): nat := List.fold_right mult 1 l.

Lemma ex1_help: forall (n a : nat),
  (n + a) mod 3 = n mod 3 -> (I (n + a) = (Rpower 3 ((INR a) / 3)) * (I n))%R.
Proof.
  intros. unfold I. rewrite H. destruct (eq_nat_dec (n mod 3) 0).
  { rewrite <- Rpower_plus. unfold Rdiv. rewrite <- Rmult_plus_distr_r.
    rewrite plus_comm. rewrite plus_INR. reflexivity.
  } destruct (eq_nat_dec (n mod 3) 1).
  { rewrite (Rmult_comm _ (4 * _)). rewrite (Rmult_assoc 4 _ _).
    rewrite <- Rpower_plus. unfold Rdiv. rewrite <- Rmult_plus_distr_r.
    unfold Rminus. rewrite (Rplus_comm (_ + -4) _).
    rewrite <- (Rplus_assoc _ _ (-4)). rewrite plus_comm.
    rewrite plus_INR. reflexivity.
  } assert (n - 2 + a = n + a -2). assert (2 <= n). destruct n.
  exfalso. apply n0. reflexivity. destruct n. exfalso.
  apply n1. reflexivity. repeat apply le_n_S. apply Peano.le_0_n.
  rewrite (plus_comm n a). rewrite <- Nat.add_sub_assoc.
  apply plus_comm. apply H0. rewrite <- H0. rewrite plus_INR.
  unfold Rdiv. rewrite (Rmult_plus_distr_r _ _ (/3)).
  rewrite Rpower_plus. rewrite (Rmult_comm _ (2 * _)).
  rewrite (Rmult_assoc 2 _ _). reflexivity. Qed.

Lemma ex1_help1 : forall (n a : nat),
  a mod 3 = 1 -> ((4/3) * (Rpower 3 ((INR (a -1))/3)) * (I n) <= I (n + a))%R.
Proof.
  intros. assert (exists b, a = 3 * b + 1). exists (a / 3).
  rewrite <- H at 3. apply Nat.div_mod. auto. destruct H0 as [b H0].
  subst. assert (3 * b + 1 - 1 = 3 * b). rewrite plus_comm.
  apply minus_plus. rewrite H0; clear H0. rewrite mult_comm.
  rewrite mult_INR. unfold Rdiv at 2. rewrite (Rmult_assoc _ _ (/3)).
  assert (INR 3 = 3)%R. simpl; Rcompute. rewrite H0.
  rewrite Rinv_r. rewrite Rmult_1_r. rewrite (plus_comm _ 1).
  rewrite mult_comm in H. rewrite (plus_comm 1 _).
  induction n using strong_induction.
  { simpl. unfold I; rewrite H; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O. rewrite Rmult_1_r.
    rewrite plus_INR. simpl. unfold Rminus. rewrite Rplus_assoc.
    assert (1 + -4 = -3)%R. Rcompute. rewrite H1.
    rewrite (Rmult_plus_distr_r _ _ (/3)). rewrite mult_INR.
    rewrite (Rmult_assoc _ (INR 3) (/3)). rewrite H0. rewrite Rinv_r.
    rewrite Rmult_1_r. rewrite <- Ropp_mult_distr_l.
    rewrite (Rplus_comm (INR b) _). rewrite Rpower_plus.
    rewrite Rpower_Ropp. rewrite Rinv_r. rewrite Rpower_1.
    rewrite <- Rmult_assoc. apply Rle_refl. prove_sup.
    discrR. discrR. prove_sup.
  } destruct (eq_nat_dec ((S n) mod 3) 0).
  { assert ((S n + (b * 3 + 1)) mod 3 = 1). rewrite <- Nat.add_mod_idemp_l.
    rewrite e. simpl. apply H. auto. assert (exists m, S n = 3 * m + 3).
    exists ((S n) / 3 - 1). rewrite Nat.mul_sub_distr_l.
    rewrite mult_1_r. rewrite (plus_n_O (3 * _ )). rewrite <- e at 3.
    rewrite <- Nat.div_mod. rewrite plus_comm. assert (3 <= S n).
    destruct n. simpl in e; inversion e. destruct n. simpl in e; inversion e.
    repeat apply le_n_S. apply Peano.le_0_n. apply (le_plus_minus _ _ H3). auto.
    destruct H3 as [m H3]; rewrite H3. rewrite H3 in e. rewrite H3 in H2.
    unfold I; rewrite e; rewrite H2. simpl. fold (3 * m).
    assert (3 * m <= n). apply le_S_n. rewrite H3. rewrite plus_comm.
    apply le_n_S. auto. apply H1 in H4. assert (3 <= 3 * m + 3).
    rewrite plus_comm. repeat apply le_n_S. apply Peano.le_0_n.
    assert (3 <= 3 * m + 3 + (b * 3 + 1)). rewrite (plus_comm _ 3).
    repeat apply le_n_S. apply Peano.le_0_n. assert (0 < 3). auto.
    apply (mod_b_eq _ _ H7) in H5. apply (mod_b_eq _ _ H7) in H6.
    clear H3; clear H1. clear H. clear H7. rewrite H5 in e.
    rewrite H6 in H2. clear H5; clear H6. rewrite plus_comm in e.
    rewrite minus_plus in e. rewrite (plus_comm _ 3) in H2.
    rewrite <- plus_assoc in H2. rewrite minus_plus in H2.
    unfold I in H4; rewrite e in H4; rewrite H2 in H4;
    simpl in H4; fold (3 * m) in H4. clear e; clear H2.
    assert ((INR (3 * m + 3 + (b * 3 + 1)) - 4) = (INR (3 * m + ((b * 3) + 1)) - 4 + 3))%R.
    rewrite plus_comm. rewrite plus_assoc. rewrite plus_INR.
    rewrite plus_comm. rewrite H0. unfold Rminus. rewrite Rplus_assoc.
    rewrite (Rplus_comm 3 _). rewrite <- Rplus_assoc. reflexivity.
    rewrite H; clear H. rewrite plus_INR. rewrite H0.
    unfold Rdiv. unfold Rdiv in H4. repeat rewrite (Rmult_plus_distr_r _ 3 (/3)).
    repeat rewrite Rpower_plus. repeat rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r. rewrite Rinv_r. rewrite Rpower_1. left; prove_sup.
    prove_sup. discrR. apply H4.
  } destruct (eq_nat_dec ((S n) mod 3) 1). assert (S n = 1 \/ 1 < S n).
  destruct n. left. reflexivity. right. repeat apply le_n_S. apply Peano.le_0_n.
  inversion H2; clear H2.
  { rewrite H3. assert ((1 + (b * 3 + 1)) mod 3 = 2). rewrite <- Nat.add_mod_idemp_r.
    rewrite H. reflexivity. auto. unfold I; rewrite H2; simpl.
    rewrite plus_comm. rewrite minus_plus. assert (1 - 4 = -3)%R. Rcompute.
    rewrite H4; clear H4. unfold Rdiv. rewrite <- Ropp_mult_distr_l.
    rewrite Rpower_Ropp. rewrite Rinv_r. rewrite Rpower_1.
    rewrite Rmult_comm. rewrite <- Rmult_assoc. rewrite mult_INR.
    rewrite H0. rewrite (Rmult_assoc _ 3). rewrite Rinv_r. rewrite Rmult_1_r.
    apply Rmult_le_compat_r. rewrite Rpower_pow. apply pow_le.
    left; prove_sup. prove_sup. rewrite Rmult_assoc.
    rewrite (Rmult_comm (/3)). rewrite <- Rmult_assoc. rewrite <- Rmult_assoc.
    assert (4 * 4 = 16)%R. Rcompute. rewrite H4; clear H4. rewrite Rmult_assoc.
    rewrite <- Rinv_mult_distr. assert (3 * 3 = 9)%R. Rcompute. rewrite H4; clear H4.
    apply (Rmult_le_reg_r 9). prove_sup. rewrite Rmult_assoc. rewrite Rinv_l.
    rewrite Rmult_1_r. left; prove_sup. discrR. discrR. discrR. discrR. prove_sup. discrR.
  }
  { assert (0 < 3). auto. assert (H4 := (mod_b_eq _ _ H2 (mod_lt_gt _ _ _ H2 e H3))).
    assert (exists m, S n = 3 * m + 1 + 3). assert (exists m, S n = 3 * m + 1).
    exists ((S n) / 3). rewrite <- e at 3. apply Nat.div_mod. auto.
    destruct H5 as [m H5]. rewrite H5. exists (m - 1). destruct m. simpl in H5.
    rewrite H5 in H3. apply lt_not_le in H3. exfalso. apply H3. reflexivity.
    rewrite <- mult_n_Sm. rewrite <- plus_assoc. rewrite (plus_comm 3 1).
    rewrite plus_assoc. simpl; rewrite <- minus_n_O; reflexivity.
    destruct H5 as [m H5]. rewrite H5. rewrite H5 in H4.
    rewrite plus_comm in H4 at 2. rewrite minus_plus in H4.
    assert ((3 * m + 1 + 3 + (b * 3 + 1)) mod 3 =  (3 * m + 1 + (b * 3 + 1)) mod 3).
    repeat rewrite <- (Nat.add_mod_idemp_l (_ +  _ ) (b * 3 + 1)). rewrite H4.
    reflexivity. auto. auto. assert ((3 * m + 1 + (b * 3 + 1)) mod 3 = 2).
    rewrite <- Nat.add_mod_idemp_l. rewrite <- H4. rewrite <- H5. rewrite e.
    rewrite <- Nat.add_mod_idemp_r. rewrite H. reflexivity. auto. auto.
    unfold I; rewrite H6. rewrite H7. rewrite H5 in e. rewrite e. simpl.
    fold (3 * m). assert (3 * m + 1 <= n). apply le_S_n. rewrite H5.
    rewrite (plus_comm _ 3). apply le_n_S. auto. apply H1 in H8.
    unfold I in H8; rewrite H7 in H8; rewrite <- H4 in H8; rewrite e in H8;
    simpl in H8; fold (3 * m) in H8.
    assert ((INR (3 * m + 1 + 3)) - 4 = (INR (3 * m + 1)) - 4 + 3)%R.
    rewrite plus_INR. unfold Rminus. rewrite Rplus_assoc. rewrite H0.
    rewrite (Rplus_comm 3). rewrite <- Rplus_assoc. reflexivity.
    rewrite H9; clear H9.
    assert (INR (3 * m + 1 + 3 + (b * 3 + 1) - 2) = (INR (3 * m + 1 + (b * 3 + 1) - 2)) + 3)%R.
    assert (3 * m + 1 + 3 = 3 + 3 * m + 1). rewrite <- (plus_assoc 3). apply plus_comm.
    rewrite H9; clear H9. repeat rewrite <- plus_assoc.
    assert (3 * m + (1 + (b * 3 + 1)) = 2 + 3 * m + b * 3). rewrite (plus_comm (b * 3) 1).
    rewrite (plus_assoc 1). assert (1 + 1 = 2). auto. rewrite H9; clear H9.
    rewrite plus_assoc. rewrite (plus_comm _ 2). reflexivity. rewrite H9; clear H9.
    rewrite plus_comm. repeat rewrite <- plus_assoc. repeat rewrite minus_plus.
    rewrite plus_assoc. rewrite plus_INR. rewrite H0. reflexivity.
    rewrite H9; clear -H8 H0. unfold Rdiv. unfold Rdiv in H8.
    repeat rewrite (Rmult_plus_distr_r _ 3). repeat rewrite Rpower_plus.
    repeat rewrite <- Rmult_assoc. apply Rmult_le_compat_r. rewrite Rinv_r.
    rewrite Rpower_1. left; prove_sup. prove_sup. discrR.
    repeat rewrite <- Rmult_assoc in H8. apply H8.
  } assert (e := mod3_eq_2 _ n0 n1). assert (S n = 2 \/ 2 < S n).
  destruct n. simpl in e; inversion e. destruct n. left; reflexivity.
  right. repeat apply le_n_S. apply Peano.le_0_n. inversion H2.
  { rewrite H3. assert ((2 + (b * 3 + 1)) mod 3 = 0). rewrite  <- Nat.add_mod_idemp_r.
    rewrite H. reflexivity. auto. rewrite plus_comm. rewrite plus_comm in H4.
    unfold I; rewrite H4; simpl. rewrite <- plus_assoc. simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O. rewrite Rmult_1_r. rewrite Rmult_comm.
    repeat rewrite <- Rmult_assoc. assert (4 * 2 = 8)%R. Rcompute. rewrite H5; clear H5.
    rewrite plus_INR. rewrite H0. rewrite (Rmult_plus_distr_r _ 3). rewrite Rpower_plus.
    rewrite Rinv_r. rewrite Rpower_1. rewrite Rmult_comm. rewrite mult_INR.
    rewrite H0. rewrite (Rmult_assoc _ 3). rewrite Rinv_r. rewrite Rmult_1_r.
    apply Rmult_le_compat_l. rewrite Rpower_pow. apply pow_le. left; prove_sup.
    prove_sup. apply (Rmult_le_reg_r 3). prove_sup. rewrite Rmult_assoc.
    rewrite Rinv_l. rewrite Rmult_1_r. assert (3 * 3 = 9)%R. Rcompute.
    rewrite H5. left; prove_sup. discrR. discrR. prove_sup. discrR. prove_sup.
  } clear H2 n0 n1. assert (exists m, S n = 3 * m + 2 + 3).
  assert (exists m, S n = 3 * m + 2). exists ((S n) / 3). rewrite <- e at 3.
  apply Nat.div_mod. auto. destruct H2 as [m H2]. exists (m - 1).
  destruct m. simpl in H2. rewrite H2 in H3. apply lt_not_le in H3. exfalso.
  apply H3. reflexivity. rewrite H2. rewrite <- mult_n_Sm. rewrite plus_comm.
  rewrite plus_assoc. rewrite (plus_comm 2). simpl; repeat rewrite <- minus_n_O.
  reflexivity. destruct H2 as [m H2]. assert (0 < 3). auto.
  assert (H5 := mod_b_eq _ _ H4 (mod_lt_gt _ _ _ H4 e H3)).
  assert ((S n + (b * 3 + 1)) mod 3 = 0). rewrite <- Nat.add_mod_idemp_l.
  rewrite e. rewrite <- Nat.add_mod_idemp_r. rewrite H. reflexivity. auto. auto.
  assert (((S n) + (b * 3 + 1)) mod 3 = ((S n) - 3 + (b * 3 + 1)) mod 3).
  rewrite <- Nat.add_mod_idemp_l. rewrite <- (Nat.add_mod_idemp_l (S n - 3)).
  rewrite H5. reflexivity. auto. auto. rewrite H2 in H5, H6, H7, e. rewrite H2.
  assert (3 * m + 2 + 3 - 3 = 3 * m + 2). rewrite plus_comm. apply minus_plus.
  rewrite H8 in H5, H7; clear H8. assert (3 * m + 2 <= n). apply le_S_n.
  rewrite H2. rewrite (plus_comm _ 3). apply le_n_S. auto. apply H1 in H8.
  unfold I; rewrite e; rewrite H6; simpl; fold (3 * m).
  unfold I in H8; rewrite <- H5 in H8; rewrite e in H8;
  rewrite <- H7 in H8; rewrite H6 in H8; simpl in H8; fold (3 * m) in H8.
  clear -H8 H0. rewrite (plus_comm _ 2). rewrite (plus_comm _ 2) in H8.
  rewrite <- plus_assoc at 1. rewrite minus_plus. rewrite minus_plus in H8.
  assert (2 + 3 * m + 3 + (b * 3 + 1) = 2 + 3 * m + (b * 3 + 1) + 3).
  repeat rewrite <- plus_assoc. rewrite (plus_assoc _ 1 3).
  rewrite (plus_comm _ 3). reflexivity. rewrite H; clear H.
  repeat rewrite (plus_INR _ 3). unfold Rdiv. unfold Rdiv in H8.
  rewrite H0. repeat rewrite (Rmult_plus_distr_r _ 3). repeat rewrite Rpower_plus.
  repeat rewrite <- Rmult_assoc. apply Rmult_le_compat_r. rewrite Rinv_r.
  rewrite Rpower_1. left; prove_sup. prove_sup. discrR.
  repeat rewrite <- Rmult_assoc in H8. apply H8. discrR. Qed.

Lemma ex1_help1': forall (n : nat),
  n mod 3 = 1 ->
  ((INR n) <= 4/3 * Rpower 3 ((INR (n - 1))/3))%R.
Proof.
  intros. assert (exists m, n = 3*m + 1).
  exists (n / 3). rewrite <- H at 3.
  apply Nat.div_mod. auto. destruct H0 as [m H0].
  rewrite H0. assert (3 * m  + 1 - 1 = 3 * m).
  rewrite plus_comm. apply minus_plus. subst. rewrite H1; clear H1.
  induction m.
  { simpl. unfold Rdiv. rewrite Rmult_0_l. rewrite Rpower_O.
    rewrite Rmult_1_r. left. apply (Rmult_lt_reg_r 3). prove_sup.
    rewrite Rmult_1_l. rewrite Rmult_assoc. rewrite Rinv_l.
    rewrite Rmult_1_r. prove_sup. discrR. prove_sup.
  } rewrite mod_b_eq in H.
  assert (3 * (S m) + 1 - 3 = 3 * m + 1). rewrite <- mult_n_Sm.
  rewrite <- plus_assoc. rewrite plus_comm. rewrite <- plus_assoc.
  rewrite minus_plus. apply plus_comm. rewrite H0 in H; clear H0.
  apply IHm in H. clear IHm. rewrite mult_INR. rewrite (Rmult_comm (INR 3) _).
  unfold Rdiv at 2. rewrite Rmult_assoc. assert (INR 3 = 3)%R. simpl; Rcompute.
  rewrite H0. rewrite Rinv_r. rewrite Rmult_1_r. rewrite mult_INR in H.
  rewrite (Rmult_comm (INR 3)) in H. rewrite H0 in H. unfold Rdiv in H at 2.
  rewrite Rmult_assoc in H. rewrite Rinv_r in H. rewrite Rmult_1_r in H.
  destruct m.
  { simpl. rewrite Rpower_1. unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l.
    rewrite Rmult_1_r. right. Rcompute. discrR. prove_sup.
  }
  apply (Rplus_le_reg_r (Ropp (4 / 3 * (Rpower 3 (INR (S m)))))).
  rewrite <- mult_n_Sm. rewrite (plus_comm (3 * (S m)) _ ).
  rewrite <- plus_assoc. rewrite plus_INR. rewrite (Rplus_assoc (INR 3)).
  assert ((INR 3) + ((INR (3 *(S m) + 1)) + - (4/3 * (Rpower 3 (INR (S m))))) <= INR 3)%R.
  rewrite <- Rplus_0_r. apply Rplus_le_compat_l. apply (Rle_minus _ _ H).
  apply (Rle_trans _ _ _ H1). rewrite H0. rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l. repeat rewrite Rpower_pow.
  { clear. simpl. rewrite <- (Rmult_1_l (Ropp _)). rewrite <- Ropp_mult_distr_r.
    rewrite Ropp_mult_distr_l. rewrite <- Rmult_plus_distr_r.
    assert (3 + - 1 = 2)%R. Rcompute. rewrite H; clear H.
    repeat rewrite <- Rmult_assoc. assert (4/3 * 2 * 3 = 8)%R.
    unfold Rdiv. rewrite (Rmult_comm 4 _). rewrite (Rmult_comm _ 3).
    repeat rewrite <- Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_l.
    reflexivity. discrR. rewrite H. clear H. induction m.
    simpl. rewrite Rmult_1_r. left. prove_sup. simpl.
    rewrite <- Rmult_assoc. rewrite (Rmult_comm 8 3).
    rewrite <- Rmult_1_l at 1. rewrite Rmult_assoc. apply Rmult_le_compat.
    left. prove_sup. left. prove_sup. left. prove_sup. apply IHm.
  } prove_sup. prove_sup. discrR. discrR. auto.
  rewrite <- mult_n_Sm. rewrite (plus_comm _ 3). simpl.
  repeat apply le_n_S. apply Peano.le_0_n. Qed.

Lemma ex1_help2: forall (n a : nat),
  a mod 3 = 2 -> (2 * (Rpower 3 ((INR (a - 2))/3)) * (I n) <= I (n + a))%R.
Proof.
  intros. assert (exists b, a = 3 * b + 2). exists (a / 3). rewrite <- H at 3.
  apply Nat.div_mod. auto. destruct H0 as [b H0]; subst. rewrite plus_comm.
  rewrite minus_plus. rewrite mult_INR. unfold Rdiv. rewrite (Rmult_comm (INR 3)).
  assert (INR 3 = 3)%R. simpl; Rcompute. rewrite H0. rewrite (Rmult_assoc _ 3).
  rewrite Rinv_r. rewrite Rmult_1_r. rewrite plus_comm. rewrite (plus_comm 2).
  rewrite mult_comm. rewrite mult_comm in H.
  induction n using strong_induction.
  { rewrite <- plus_n_O. unfold I; rewrite H; simpl. rewrite plus_comm.
    rewrite minus_plus. rewrite mult_INR. rewrite H0. unfold Rdiv.
    rewrite (Rmult_assoc _ 3). rewrite Rinv_r. rewrite Rmult_1_r.
    rewrite Rmult_0_l. rewrite Rpower_O. rewrite Rmult_1_r.
    apply Rle_refl. prove_sup. discrR.
  } destruct (eq_nat_dec ((S n) mod 3) 0).
  { assert (exists m, (S n) = m * 3 + 3). assert (exists m, (S n) = 3 * m).
    exists ((S n) / 3). rewrite plus_n_O. rewrite <- e at 3. apply Nat.div_mod.
    auto. destruct H2 as [m H2]. rewrite H2. exists (m - 1). destruct m.
    inversion H2. simpl. rewrite <- minus_n_O. rewrite mult_comm.
    rewrite mult_n_Sm. reflexivity. destruct H2 as [m H2]. rewrite H2.
    rewrite H2 in e. assert (m * 3 <= n). apply le_S_n. rewrite H2.
    rewrite plus_comm. simpl. auto. apply H1 in H3. assert (m * 3 mod 3 = 0).
    rewrite <- Nat.mul_mod_idemp_r. rewrite mult_comm. reflexivity. auto.
    assert ((b * 3 + 2 + m * 3) mod 3 = 2). rewrite <- Nat.add_mod_idemp_r.
    rewrite H4. rewrite <- plus_n_O. apply H. auto.
    assert ((b * 3 + 2 + (m * 3 + 3)) mod 3 = 2). rewrite plus_assoc.
    rewrite <- Nat.add_mod_idemp_r. assert (3 mod 3 = 0). auto.
    rewrite H6. rewrite <- plus_n_O. apply H5. auto.
    unfold I; rewrite H6; rewrite e; simpl.
    unfold I in H3; rewrite H5 in H3; rewrite H4 in H3; simpl in H3.
    clear -H0 H3. unfold Rdiv. unfold Rdiv in H3.
    assert (b * 3 + 2 + (m * 3 + 3) - 2 = b * 3 + 2 + m * 3 - 2 + 3).
    repeat rewrite (plus_comm _ 2). repeat rewrite <- plus_assoc.
    repeat rewrite minus_plus. apply plus_assoc. rewrite H; clear H.
    repeat rewrite (plus_INR _ 3). rewrite H0. repeat rewrite (Rmult_plus_distr_r _ 3).
    repeat rewrite Rpower_plus. repeat rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r. rewrite Rinv_r. rewrite Rpower_1. left; prove_sup.
    prove_sup. discrR. apply H3.
  } destruct (eq_nat_dec ((S n) mod 3) 1).
  { assert (S n = 1 \/ 1 < S n). destruct n. left; reflexivity.
    right; repeat apply le_n_S; apply Peano.le_0_n.
    assert ((b * 3 + 2 + (S n)) mod 3 = 0). rewrite <- Nat.add_mod_idemp_l.
    rewrite H. rewrite <- Nat.add_mod_idemp_r. rewrite e. auto. auto. auto. inversion H2.
    { rewrite H4; rewrite H4 in H3; clear - H0 H3. unfold I; rewrite H3; simpl.
      rewrite <- plus_assoc. simpl. rewrite plus_INR. unfold Rdiv at 2.
      rewrite (Rmult_plus_distr_r _ (INR 3)). rewrite mult_INR. rewrite H0.
      rewrite (Rmult_assoc _ 3). rewrite Rinv_r. rewrite Rmult_1_r. rewrite Rpower_plus.
      rewrite Rpower_1. rewrite (Rmult_comm _ 3). rewrite (Rmult_comm (2 * _)).
      repeat rewrite <- Rmult_assoc. apply Rmult_le_compat_r. rewrite Rpower_pow.
      apply pow_le. left; prove_sup. prove_sup. assert (1 - 4 = -3)%R. Rcompute.
      rewrite H; clear H. unfold Rdiv. rewrite <- Ropp_mult_distr_l. rewrite Rpower_Ropp.
      rewrite Rinv_r. rewrite Rpower_1. rewrite Rmult_comm. rewrite <- Rmult_assoc.
      apply (Rmult_le_reg_r 3). prove_sup. rewrite Rmult_assoc. rewrite Rinv_l.
      rewrite Rmult_1_r. assert (3 * 3 = 9)%R. Rcompute. rewrite H. left. prove_sup.
      discrR. prove_sup. discrR. prove_sup. discrR.
    } assert (0 < 3). auto. assert (H6 := mod_b_eq _ _ H5 (mod_lt_gt _ _ _ H5 e H4)).
    assert (exists m, S n = m * 3 + 1 + 3). assert (exists m, S n = m * 3 + 1).
    exists ((S n) /3). rewrite <- e at 3. rewrite mult_comm. apply Nat.div_mod. auto.
    destruct H7 as [m H7]. rewrite H7. exists (m - 1). destruct m. simpl in H7.
    rewrite H7 in H4. inversion H4. inversion H9.
    rewrite (plus_comm _ 3). simpl. rewrite <- minus_n_O. reflexivity.
    destruct H7 as [m H7]. rewrite H7 in H6, H3, e. rewrite H7.
    assert (m * 3 + 1 <= n). apply le_S_n. rewrite H7.
    rewrite (plus_comm _ 3). simpl; auto. apply H1 in H8.
    clear - H0 e H3 H6 H8. rewrite (plus_comm _ 3) in H6 at 2.
    rewrite minus_plus in H6.
    assert ((b * 3 + 2 + (m * 3 + 1)) mod 3 = 0). rewrite <- Nat.add_mod_idemp_r.
    rewrite <- H6. rewrite Nat.add_mod_idemp_r. apply H3. auto. auto.
    unfold I; rewrite e; rewrite H3; simpl.
    unfold I in H8; rewrite <- H6 in H8; rewrite e in H8; rewrite H in H8; simpl in H8.
    clear - H0 H8. assert ((INR (m * 3 + 1 + 3)) - 4 = (INR (m * 3 + 1)) - 4 + 3)%R.
    unfold Rminus. rewrite plus_comm. rewrite plus_INR. rewrite H0.
    rewrite (Rplus_comm _ 3). apply Rplus_assoc. rewrite H; clear H.
    rewrite plus_assoc. rewrite (plus_INR _ 3). rewrite H0. unfold Rdiv.
    repeat rewrite (Rmult_plus_distr_r _ 3). rewrite Rinv_r.
    repeat rewrite Rpower_plus. repeat rewrite <- Rmult_assoc.
    repeat rewrite <- Rmult_assoc in H8. apply Rmult_le_compat_r.
    rewrite Rpower_1; try left; prove_sup. unfold Rdiv in H8. apply H8. discrR.
  } assert (H2 := mod3_eq_2 _ n0 n1). assert ((b * 3 + 2 + S n) mod 3 = 1).
  rewrite <- Nat.add_mod_idemp_r. rewrite H2. rewrite <- Nat.add_mod_idemp_l.
  rewrite H. reflexivity. auto. auto. assert (S n = 2 \/ 2 < S n).
  destruct n. exfalso. apply n1. reflexivity. destruct n. left. reflexivity.
  right. repeat apply le_n_S. apply Peano.le_0_n. inversion H4; clear n0 n1 H4.
  { unfold I; rewrite H2; rewrite H3; rewrite H5; clear - H0; simpl.
    unfold Rdiv. rewrite Rmult_0_l. rewrite Rpower_O. rewrite Rmult_1_r.
    rewrite Rmult_comm. rewrite <- Rmult_assoc. apply Rmult_le_compat_l.
    left; prove_sup. right. rewrite <- plus_assoc. simpl. rewrite plus_INR.
    assert (INR 4 = 4)%R. simpl; Rcompute. rewrite H. unfold Rminus.
    rewrite Rplus_assoc. assert (4 + -4 = 0)%R. Rcompute. rewrite H1.
    rewrite Rplus_0_r. rewrite mult_INR. rewrite H0. rewrite Rmult_assoc.
    rewrite Rinv_r. rewrite Rmult_1_r. reflexivity. discrR. prove_sup.
  } assert (0 < 3). auto. assert (H6 := mod_b_eq _ _ H4 (mod_lt_gt _ _ _ H4 H2 H5)).
  assert (exists m, S n = m * 3 + 2 + 3). assert (exists m, S n = m * 3 + 2).
  exists ((S n)/3). rewrite <- H2 at 3. rewrite mult_comm. apply Nat.div_mod. auto.
  destruct H7 as [m H7]. destruct m. simpl in H7. rewrite H7 in H5.
  inversion H5; inversion H9; inversion H11. exists m. rewrite H7.
  rewrite (plus_comm _ 3). reflexivity. destruct H7 as [m H7].
  assert (m * 3 + 2 <= n). apply le_S_n. rewrite H7. rewrite (plus_comm _ 3).
  simpl. auto. apply H1 in H8. rewrite H7 in H2, H3, H6. rewrite H7.
  clear - H0 H2 H3 H6 H8. rewrite (plus_comm _ 3) in H6 at 2.
  rewrite minus_plus in H6. assert ((b * 3 + 2 + (m * 3 + 2)) mod 3 = 1).
  rewrite <- Nat.add_mod_idemp_r. rewrite <- H6. rewrite Nat.add_mod_idemp_r.
  apply H3. auto. auto. unfold I; rewrite H2; rewrite H3; simpl.
  unfold I in H8; rewrite <- H6 in H8; rewrite H2 in H8; rewrite H in H8;
  simpl in H8. clear -H0 H8. assert (m * 3 + 2 + 3 - 2 = m * 3 + 2 - 2 + 3).
  rewrite (plus_comm _ 2). rewrite <- plus_assoc. repeat rewrite minus_plus.
  reflexivity. rewrite H; clear H.
  assert ((INR (b * 3 + 2 + (m * 3 + 2 + 3))) - 4 = (INR (b * 3 + 2 + (m * 3 + 2))) - 4 + 3)%R.
  rewrite plus_assoc. rewrite plus_INR. rewrite H0. unfold Rminus.
  rewrite Rplus_assoc. rewrite (Rplus_comm 3). rewrite <- Rplus_assoc. reflexivity.
  rewrite H; clear H. unfold Rdiv; unfold Rdiv in H8. rewrite plus_INR. rewrite H0.
  repeat rewrite (Rmult_plus_distr_r _ 3). rewrite Rinv_r.
  repeat rewrite Rpower_plus. repeat rewrite <- Rmult_assoc.
  repeat rewrite <- Rmult_assoc in H8. apply Rmult_le_compat_r.
  rewrite Rpower_1; try left; prove_sup. apply H8. discrR. discrR.
Qed.

Lemma ex1_help2': forall (n : nat),
  n mod 3 = 2 ->
  (INR n <= 2 * (Rpower 3 ((INR (n - 2))/3)))%R.
Proof.
  intros. assert (exists m, n = 3*m + 2).
  exists (n / 3). rewrite <- H at 3.
  apply Nat.div_mod. auto. destruct H0 as [m H0].
  rewrite H0. assert (3 * m  + 2 - 2 = 3 * m).
  rewrite plus_comm. apply minus_plus. subst. rewrite H1; clear.
  rewrite mult_INR. rewrite (Rmult_comm (INR 3)). unfold Rdiv.
  rewrite Rmult_assoc. assert (INR 3 = 3)%R. simpl; Rcompute.
  rewrite H. rewrite Rinv_r. rewrite Rmult_1_r. rewrite Rpower_pow.
  induction m.
  { simpl. rewrite Rmult_1_r. apply Rle_refl. }
  rewrite <- mult_n_Sm. rewrite (plus_comm _ 3). rewrite <- plus_assoc.
  rewrite plus_INR. rewrite H. apply (Rplus_le_reg_r (Ropp (2 * (3 ^ m)))).
  rewrite Rplus_assoc. assert (3 + ((INR (3 * m + 2)) + -(2 * (3 ^ m))) <= 3)%R.
  rewrite <- Rplus_0_r. apply Rplus_le_compat_l. apply (Rle_minus _ _ IHm).
  apply (Rle_trans _ _ _ H0). clear. rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l. simpl. rewrite <- (Rmult_1_l (3 ^ m)) at 2.
  rewrite Ropp_mult_distr_l. rewrite <- Rmult_plus_distr_r.
  assert (3 + -1 = 2)%R. Rcompute. rewrite H. rewrite <- Rmult_assoc. clear.
  { induction m. simpl. rewrite Rmult_1_r. left. prove_sup.
    simpl. rewrite <- Rmult_assoc. rewrite (Rmult_comm 4 3).
    rewrite Rmult_assoc. rewrite <- Rmult_1_l at 1.
    apply Rmult_le_compat; try (left; prove_sup; fail). apply IHm.
  } prove_sup. discrR. Qed.

Theorem ex1': forall (n a : nat) (r : R),
  (0 <= r -> r <= I n -> (INR a)*r <= I (n + a))%R.
Proof.
  intros. destruct (eq_nat_dec (a mod 3) 0).
  { assert ((n +  a) mod 3 = n mod 3). rewrite <- Nat.add_mod_idemp_r.
    rewrite e. rewrite <- plus_n_O. reflexivity. auto.
    rewrite (ex1_help _ _ H1). apply Rmult_le_compat. apply pos_INR.
    apply H. apply n_q. apply H0.
  } destruct (eq_nat_dec (a mod 3) 1).
  { assert (H1 := e). apply (ex1_help1 n) in H1.
    apply (Rle_trans _ (4/3 * (Rpower 3 ((INR (a - 1))/3)) * (I n)) _).
    { apply Rmult_le_compat. apply pos_INR. apply H.
      apply (ex1_help1' _ e). apply H0.
    }
    apply H1.
  } assert (H1 := mod3_eq_2 _ n0 n1). assert (H2 := H1).
  apply (ex1_help2 n) in H1. apply ex1_help2' in H2.
  apply (Rle_trans _ (2 * (Rpower 3 ((INR (a - 2))/3)) * (I n))).
  { apply Rmult_le_compat. apply pos_INR. apply H. apply H2. apply H0. }
  apply H1. Qed.

Theorem ex1 : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= I n)%R.
Proof.
  intros l. induction l; intros.
  { simpl in H. rewrite <- H. unfold I; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O. apply Rle_refl. prove_sup.
  } simpl in H. symmetry in H. assert (a <= n). rewrite H.
  rewrite plus_n_O at 1. apply plus_le_compat_l. apply Peano.le_0_n.
  apply plus_minus in H. apply IHl in H. simpl. rewrite mult_INR.
  induction a using strong_induction. simpl. rewrite <- minus_n_O in H.
  rewrite Rmult_0_l. assert (H1 := pos_INR (prod l)).
  apply (Rle_trans _ _ _ H1 H). apply (ex1' _ (S a) _ ) in H.
  rewrite plus_comm in H. rewrite (le_plus_minus_r _ _ H0) in H.
  apply H. assert (0 = INR 0)%R. reflexivity. rewrite H2.
  apply le_INR. apply Peano.le_0_n. Qed.

Theorem ex2 : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= Rpower 3 ((INR n) / 3))%R.
Proof.
  intros. apply ex1 in H. apply (Rle_trans _ _ _ H (I_n_q n)). Qed.

Theorem ex2_direct : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= Rpower 3 ((INR n) / 3))%R.
Proof.
  intros l. induction l; intros.
  { simpl in H. rewrite <- H. unfold I; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O. apply Rle_refl. prove_sup.
  } simpl in H. symmetry in H. assert (a <= n). rewrite H.
  rewrite plus_n_O at 1. apply plus_le_compat_l. apply Peano.le_0_n.
  apply plus_minus in H. apply IHl in H. simpl. rewrite mult_INR.
  assert (n = a + (n - a)). apply (le_plus_minus _ _ H0).
  rewrite H1. rewrite plus_INR. unfold Rdiv. rewrite Rmult_plus_distr_r.
  fold (Rdiv (INR a) (3)). unfold Rdiv in H. rewrite Rpower_plus.
  apply Rmult_le_compat; try apply pos_INR. apply n_q. auto. Qed.