Require Import Reals.
Require Import Omega.
Require Import Fourier.
Open Scope R_scope.

Definition I (n : nat) : R :=
  if eq_nat_dec (n mod 3) 0 then Rpower 3 ((INR n) / 3)
  else if eq_nat_dec (n mod 3) 1 then 4 * (Rpower 3 ((INR n - 4)/3))
  else 2 * (Rpower 3 ((INR (n - 2)) / 3)).

Lemma n_q' : forall (n : nat),
  (3 <= n)%nat -> 1 <= (Rpower 3 ((INR (S n))/3)) - (Rpower 3 ((INR n)/3)).
Proof.
  intros. assert (3 = INR 3). simpl; Rcompute. induction H.
  { unfold Rdiv. rewrite <- H0. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup. unfold Rminus.
    apply (Rplus_le_reg_r 3 _ _). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    assert (1+3 = 4). Rcompute. rewrite H.
    rewrite <- Rpower_mult. rewrite Rpower_pow; prove_sup.
    assert (3^4 = 81)%R. simpl. Rcompute.
    rewrite H1. assert (4 = Rpower 64 (/3)).
    assert (64 = Rpower 4 3). rewrite H0.
    rewrite Rpower_pow; prove_sup; ring.
    rewrite H2. rewrite Rpower_mult.
    rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H2 at 1. apply Rle_Rpower_l;
    [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } rewrite S_INR. rewrite S_INR at 2. unfold Rdiv.
  repeat rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
  repeat rewrite Rpower_plus. unfold Rminus.
  rewrite Ropp_mult_distr_l. rewrite <- Rmult_plus_distr_r.
  assert (1 <= (Rpower 3 (/3))). assert (1 = Rpower 1 (/3)).
  assert (1 = (Rpower 1 3)). rewrite H0.
  rewrite Rpower_pow; prove_sup; simpl; Rcompute.
  rewrite H1 at 2. rewrite Rpower_mult.
  rewrite Rinv_r; discrR.
  rewrite Rpower_1; prove_sup; auto.
  rewrite H1 at 1. apply Rle_Rpower_l;
  [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  rewrite <- Rmult_1_r at 1.
  apply Rmult_le_compat; try (left; prove_sup; fail); assumption. Qed.

Theorem n_q : forall (n : nat),
  INR n <= Rpower 3 ((INR n)/3).
Proof.
  assert (3 = INR 3). simpl; Rcompute. destruct n.
  { simpl. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup; apply Rle_0_1.
  } destruct n. {
    simpl. unfold Rdiv. rewrite Rmult_1_l.
    assert (1 = Rpower 1 (/3)).
    assert (1 = (Rpower 1 3)). rewrite H.
    rewrite Rpower_pow; prove_sup; simpl; Rcompute.
    rewrite H0 at 2. rewrite Rpower_mult.
    rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H0 at 1. apply Rle_Rpower_l;
    [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } destruct n. {
    unfold Rdiv. rewrite <- Rpower_mult.
    rewrite Rpower_pow; prove_sup.
    assert (3^2 = 9)%R. simpl; Rcompute. rewrite H0. simpl.
    assert (2 = Rpower 8 (/3)). assert (8 = Rpower 2 3).
    rewrite H. rewrite Rpower_pow; prove_sup; simpl; Rcompute.
    rewrite H1. rewrite Rpower_mult. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H1 at 1; apply Rle_Rpower_l;
    [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } induction n. {
    rewrite <- H. unfold Rdiv. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; apply Rle_refl.
  } remember (S (S (S n))) as m.
  rewrite S_INR at 1. rewrite Rplus_comm.
  apply Rle_minus in IHn.
  apply (Rplus_le_reg_r (Ropp (Rpower 3 ((INR m)/3))) _ _).
  rewrite Rplus_assoc. fold (Rminus (INR m) (Rpower 3 ((INR m)/3))).
  fold (Rminus (Rpower 3 ((INR (S m))/3)) (Rpower 3 ((INR m)/3))).
  apply (Rle_trans _ 1 _). rewrite <- Rplus_0_r.
  apply Rplus_le_compat; auto; apply Rle_refl.
  apply n_q'. rewrite Heqm. repeat apply le_n_S. apply Nat.le_0_l.
Qed.

Lemma strongind_aux : forall (P : nat -> Prop),
 (P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)))%nat.
Proof.
  induction n.
  intros m H1.
  inversion H1.
  assumption.
  intros.
  assert (m <= n \/ m = S n)%nat.
    inversion H1. right. reflexivity.
    left. subst. apply H3.
  inversion H2.
  apply IHn; assumption.
  rewrite H3.
  apply (H0 n). assumption.
Qed.

Lemma weaken : forall (P : nat -> Prop),
  ((forall n, (forall m, ((m <= n) -> P m))) -> (forall n, P n))%nat.
Proof.
  intros.
  apply (H n n).
  apply le_n.
Qed.

Theorem strong_induction : forall (P : nat -> Prop),
 (P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n)%nat.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.

Lemma mod_b_eq : forall (a b : nat),
 (0 < b -> b <= a -> a mod b = (a - b) mod b)%nat.
Proof.
  intros.
  rewrite <- (Nat.mod_add (a - b) 1 b).
  rewrite Nat.mul_1_l.
  rewrite Nat.sub_add.
  reflexivity.
  apply H0.
  unfold not.
  intros.
  subst.
  inversion H.
Qed.

Lemma mod_lt_gt : forall (a b c : nat),
 (0 < b -> a mod b = c -> c < a -> b <= a)%nat.
Proof.
  intros.
  assert (H2 := lt_eq_lt_dec a b).
  inversion H2.
  inversion H3.
  apply Nat.mod_small in H4.
  rewrite H4 in H0.
  subst.
  exfalso.
  apply (Nat.lt_irrefl _ H1).
  rewrite H4.
  reflexivity.
  apply le_Sn_le.
  apply H3.
Qed.

Lemma mod3_eq_2 : forall (a : nat),
 (a mod 3 <> 0 -> a mod 3 <> 1 -> a mod 3 = 2)%nat.
Proof.
  intros.
  assert (3 <> 0)%nat.
  auto.
  assert (forall (n : nat), n <> n -> False).
    intros;
    apply H2;
    reflexivity.
  assert (H3 := Nat.mod_upper_bound a 3 H1).
  destruct (a mod 3);
  [ apply H2 in H |
    destruct n;
    [ apply H2 in H0|]]; try contradiction.
  destruct n; auto.
  unfold lt in H3.
  repeat apply le_S_n in H3.
  apply le_n_0_eq in H3.
  inversion H3.
Qed.

Theorem I_unfold: forall (n : nat),
  (I n) * 3 = I (n + 3).
Proof.
  intros. assert ((n + 3) mod 3 = n mod 3).
  rewrite <- Nat.add_mod_idemp_r; auto.
  assert (INR 3 = 3). simpl; Rcompute.
  unfold I; rewrite H.
  destruct (eq_nat_dec (n mod 3) 0).
  { unfold Rdiv. rewrite plus_INR. rewrite H0.
    rewrite Rmult_plus_distr_r.
    rewrite Rinv_r; discrR.
    rewrite Rpower_plus.
    rewrite Rpower_1; prove_sup; auto.
  } destruct (eq_nat_dec (n mod 3) 1).
  { unfold Rdiv. rewrite plus_INR. rewrite H0.
    unfold Rminus. rewrite (Rplus_assoc _ 3).
    rewrite (Rplus_comm 3). rewrite <- (Rplus_assoc _ _ 3).
    rewrite (Rmult_plus_distr_r _ 3 (/3)).
    rewrite Rinv_r; discrR.
    rewrite Rpower_plus.
    rewrite Rpower_1; prove_sup. ring.
  } assert (H1 := Nat.mod_le n 3).
  rewrite (mod3_eq_2 _ n0 n1) in H1.
  rewrite plus_comm. rewrite <- Nat.add_sub_assoc; [|apply H1; auto].
  rewrite plus_comm. rewrite plus_INR. rewrite H0. unfold Rdiv.
  rewrite (Rmult_plus_distr_r _ 3 (/3)).
  rewrite Rinv_r; discrR.
  rewrite Rpower_plus.
  rewrite Rpower_1; prove_sup. ring.
Qed.

Theorem I_n_q : forall (n : nat),
  I n <= Rpower 3 ((INR n)/3).
Proof.
  intros n. induction n using strong_induction.
  { unfold I; simpl. apply Rle_refl.
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H0.
  { inversion H0; subst. unfold I. simpl. unfold Rdiv.
    assert ((1 - 4) * / 3 = -1). field. rewrite H1.
    rewrite Rmult_1_l. rewrite Rpower_Ropp.
    rewrite Rpower_1; prove_sup.
    assert (4 * / 3 = Rpower (64*/27) (/3)).
    assert (64 */27 = Rpower (4*/3) (INR 3)).
    rewrite Rpower_pow; try fourier; field.
    rewrite H2. rewrite Rpower_mult. simpl.
    rewrite (Rplus_comm 2 1). rewrite Rinv_r; discrR.
    symmetry; apply Rpower_1; fourier.
    rewrite H2. apply Rle_Rpower_l; [|split]; fourier.
  } destruct H0.
  { inversion H0; subst. unfold I; simpl.
    unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup. rewrite Rmult_1_r.
    rewrite <- Rpower_mult. assert (Rpower 3 (INR 2) = 9).
    rewrite Rpower_pow; prove_sup. field.
    simpl in H1; rewrite H1. assert (2 = Rpower 8 (/3)).
    assert (8 = Rpower 2 (INR 3)).
    rewrite Rpower_pow; prove_sup; field. rewrite H2.
    rewrite Rpower_mult. simpl.
    rewrite (Rplus_comm 2 1). rewrite Rinv_r; discrR.
    symmetry; apply Rpower_1; fourier.
    rewrite H2 at 1. apply Rle_Rpower_l; [|split]; fourier.
  } destruct H0 as [m H0]. assert (m <= n)%nat. omega.
  apply H in H1. rewrite H0. rewrite <- I_unfold.
  unfold Rdiv. rewrite plus_INR. rewrite Rmult_plus_distr_r.
  rewrite Rpower_plus. simpl. rewrite (Rplus_comm 2 1).
  rewrite Rinv_r; discrR. rewrite Rpower_1; prove_sup.
  apply Rmult_le_compat_r; auto; fourier.
Qed.

Definition sum (l : list nat) : nat := List.fold_right plus 0%nat l.
Definition prod (l : list nat): nat := List.fold_right mult 1%nat l.

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
  } assert (n - 2 + a = n + a -2)%nat.
  assert (H1 := Nat.mod_le n 3). omega. rewrite <- H0.
  rewrite plus_INR. unfold Rdiv.
  rewrite (Rmult_plus_distr_r _ _ (/3)).
  rewrite Rpower_plus. rewrite (Rmult_comm _ (2 * _)).
  rewrite (Rmult_assoc 2 _ _). reflexivity.
Qed.

Lemma ex1_help1 : forall (n a : nat),
  (a mod 3 = 1)%nat -> ((4/3) * (Rpower 3 ((INR (a -1))/3)) * (I n) <= I (n + a))%R.
Proof.
  intros. assert (exists b, a = 3 * b + 1)%nat. exists (a / 3)%nat.
  rewrite <- H at 3. apply Nat.div_mod. auto. destruct H0 as [b H0].
  subst. assert (3 * b + 1 - 1 = 3 * b)%nat. omega. rewrite H0; clear H0.
  rewrite mult_comm. rewrite mult_INR. unfold Rdiv at 2.
  rewrite (Rmult_assoc _ _ (/3)). assert (INR 3 = 3)%R. simpl; Rcompute.
  rewrite H0. rewrite Rinv_r; discrR. rewrite Rmult_1_r.
  rewrite (plus_comm _ 1). rewrite mult_comm in H. rewrite (plus_comm 1 _).
  induction n using strong_induction.
  { simpl. unfold I; rewrite H; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O; prove_sup. rewrite Rmult_1_r.
    assert (((INR (b * 3 + 1)) - 4)* /3 = (INR b) + - 1).
    rewrite plus_INR. rewrite mult_INR. simpl. field. rewrite H1.
    rewrite Rpower_plus. rewrite (Rmult_comm (Rpower 3 _)).
    rewrite Rpower_Ropp. rewrite Rpower_1; prove_sup.
    rewrite Rmult_assoc. apply Rle_refl.
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H2.
  { inversion H2; subst. assert ((1 + (b * 3 + 1)) mod 3 = 2)%nat.
    rewrite <- Nat.add_mod_idemp_r; [rewrite H|]; auto.
    unfold I; rewrite H3; simpl. assert ((1 - 4)/3 = -1). field.
    rewrite H4; clear H4. rewrite Rpower_Ropp.
    rewrite Rpower_1; prove_sup. assert (b * 3 + 1 - 1 = b * 3)%nat. omega.
    rewrite H4; clear H4. rewrite mult_INR. rewrite H0.
    assert (INR b * 3 /3 = INR b). field. rewrite H4; clear H4.
    rewrite Rmult_assoc. rewrite (Rmult_comm _ (4 * / 3)).
    rewrite <- Rmult_assoc. apply Rmult_le_compat_r;
    [left; apply exp_pos | fourier].
  } destruct H2.
  { inversion H2; subst. assert ((2 + (b * 3 + 1)) mod 3 = 0)%nat.
    rewrite <- Nat.add_mod_idemp_r; [rewrite H |]; auto.
    unfold I; rewrite H3; clear H3. rewrite plus_comm. simpl.
    assert ((INR (b * 3 + 1 + 2)) / 3 = INR b + 1).
    repeat rewrite plus_INR. rewrite mult_INR. simpl; field.
    rewrite H3; clear H3. rewrite Rpower_plus.
    rewrite Rpower_1; prove_sup. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup. rewrite Rmult_comm.
    rewrite (Rmult_comm _ 3). repeat rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; [left; apply exp_pos | fourier].
  } destruct H2 as [m H2]. rewrite H2.
  assert (m + 3 + (b * 3 + 1) = m + (b * 3 + 1) + 3)%nat. omega.
  rewrite H3; clear H3. repeat rewrite <- I_unfold.
  rewrite <- Rmult_assoc. apply Rmult_le_compat_r;
  [ fourier | apply H1; omega].
Qed.

Lemma ex1_help1': forall (n : nat),
  n mod 3 = 1%nat ->
  (INR n) <= 4/3 * Rpower 3 ((INR (n - 1))/3).
Proof.
  intros. assert (exists m, n = 3*m + 1)%nat.
  exists (n / 3)%nat. rewrite <- H at 3.
  apply Nat.div_mod. auto. destruct H0 as [m H0]. subst.
  assert (INR (3 * m  + 1 - 1)/3 = INR m).
  rewrite minus_INR. rewrite plus_INR; rewrite mult_INR; simpl; field.
  omega. rewrite H0. rewrite Rpower_pow; prove_sup. clear. induction m.
  { simpl. fourier. }
  assert (forall n, 1 <= n -> 3 * (S n) + 1 <= 3 * (3 * n + 1))%nat.
  intros. omega. destruct m. simpl. fourier.
  assert (1 <= S m)%nat. omega. apply H in H0. apply le_INR in H0.
  apply (Rle_trans _ _ _ H0). rewrite mult_INR.
  rewrite Rmult_comm. unfold pow; fold (pow 3 (S m)).
  rewrite (Rmult_comm 3). rewrite <- Rmult_assoc.
  assert (INR 3 = 3). simpl; Rcompute. rewrite H1.
  apply Rmult_le_compat_r; [ fourier | apply IHm].
Qed.

Lemma ex1_help2: forall (n a : nat),
  a mod 3 = 2%nat -> 2 * (Rpower 3 ((INR (a - 2))/3)) * (I n) <= I (n + a).
Proof.
  intros. assert (exists b, a = b*3 + 2)%nat. exists (a / 3)%nat.
  rewrite <- H at 3. rewrite mult_comm. apply Nat.div_mod. auto.
  destruct H0 as [b H0]; subst. assert ((INR (b*3 + 2 - 2))/3 = INR b).
  rewrite minus_INR. rewrite plus_INR; rewrite mult_INR; simpl; field.
  omega. rewrite H0. induction n using strong_induction.
  { simpl. unfold I; rewrite H; simpl. rewrite H0.
    unfold Rdiv; rewrite Rmult_0_l; rewrite Rpower_O;
    prove_sup; rewrite Rmult_1_r; apply Rle_refl.
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H2.
  { inversion H2; subst. assert ((1 + (b * 3 + 2)) mod 3 = 0%nat).
    rewrite <- Nat.add_mod_idemp_r; [rewrite H| ]; auto.
    assert (1 + (b * 3 + 2) = b * 3 + 3)%nat. omega.
    unfold I; rewrite H3; rewrite H4; simpl. rewrite plus_INR.
    unfold Rdiv. rewrite (Rmult_plus_distr_r _ _ (/3)).
    assert (INR 3 = 3). simpl; Rcompute. rewrite H5.
    rewrite Rinv_r; discrR. rewrite Rpower_plus.
    assert ((1 - 4)*/3 = -1). field. rewrite H6.
    rewrite Rpower_Ropp. rewrite Rpower_1; prove_sup.
    assert (INR (b * 3) * /3 = INR b).
    rewrite mult_INR; simpl; field. rewrite H7. rewrite Rmult_assoc.
    rewrite Rmult_comm. rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [left; apply exp_pos | fourier].
  } destruct H2. {
    inversion H2; subst. assert ((2 + (b * 3 + 2)) mod 3 = 1)%nat.
    rewrite <- Nat.add_mod_idemp_r; [rewrite H |]; auto.
    assert (2 + (b * 3 + 2) = b * 3 + 4)%nat. omega.
    unfold I; rewrite H3; rewrite H4; simpl.
    unfold Rdiv. rewrite Rmult_0_l. rewrite Rpower_O; prove_sup.
    rewrite Rmult_1_r. assert ((INR (b * 3 + 4) - 4)*/3 = INR b).
    rewrite plus_INR; rewrite mult_INR; simpl; field. rewrite H5.
    right. field.
  } destruct H2 as [m H2]. rewrite H2.
  assert (m + 3 + (b * 3 + 2) = m + (b * 3 + 2) + 3)%nat. omega.
  rewrite H3; clear H3. repeat rewrite <- I_unfold.
  rewrite <- Rmult_assoc. apply Rmult_le_compat_r;
  [ fourier | apply H1; omega].
Qed.

Lemma ex1_help2': forall (n : nat),
  n mod 3 = 2%nat ->
  INR n <= 2 * (Rpower 3 ((INR (n - 2))/3)).
Proof.
  intros. assert (exists m, n = 3*m + 2)%nat.
  exists (n / 3)%nat. rewrite <- H at 3.
  apply Nat.div_mod; auto. destruct H0 as [m H0]; subst; clear.
  assert (INR (3 * m + 2 - 2)/3 = INR m).
  rewrite minus_INR; [|omega]; rewrite plus_INR;
  rewrite mult_INR; simpl; field.
  rewrite H; clear. rewrite Rpower_pow; prove_sup.
  induction m.
  { simpl; right; field. }
  assert (forall n, 3 * (S n) + 2 <= 3 * (3 * n + 2))%nat.
  intros. omega. assert (H0 := H m). apply le_INR in H0.
  apply (Rle_trans _ _ _ H0). rewrite mult_INR.
  rewrite Rmult_comm. unfold pow; fold (pow 3 m).
  rewrite (Rmult_comm 3). rewrite <- Rmult_assoc.
  assert (INR 3 = 3). simpl; Rcompute. rewrite H1.
  apply Rmult_le_compat_r; [ fourier | apply IHm].
Qed.

Theorem ex1': forall (n a : nat) (r : R),
  0 <= r -> r <= I n -> (INR a)*r <= I (n + a).
Proof.
  intros. destruct (eq_nat_dec (a mod 3) 0).
  { assert ((n +  a) mod 3 = n mod 3). rewrite <- Nat.add_mod_idemp_r.
    rewrite e. rewrite <- plus_n_O. reflexivity. auto.
    rewrite (ex1_help _ _ H1). apply Rmult_le_compat;
    auto; try apply n_q; apply pos_INR.
  } destruct (eq_nat_dec (a mod 3) 1).
  { assert (H1 := e). apply (ex1_help1 n) in H1.
    apply (Rle_trans _ (4/3 * (Rpower 3 ((INR (a - 1))/3)) * (I n)) _).
    { apply Rmult_le_compat; auto.
      apply pos_INR. apply (ex1_help1' _ e).
    }
    apply H1.
  } assert (H1 := mod3_eq_2 _ n0 n1). assert (H2 := H1).
  apply (ex1_help2 n) in H1. apply ex1_help2' in H2.
  apply (Rle_trans _ (2 * (Rpower 3 ((INR (a - 2))/3)) * (I n))).
  { apply Rmult_le_compat; auto; apply pos_INR. }
  apply H1.
Qed.

Theorem ex1 : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= I n)%R.
Proof.
  intros l. induction l; intros.
  { simpl in H. rewrite <- H. unfold I; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O. apply Rle_refl. prove_sup.
  } simpl in H. symmetry in H. assert (a <= n)%nat. omega.
  apply plus_minus in H. apply IHl in H. simpl. rewrite mult_INR.
  induction a using strong_induction. simpl. rewrite <- minus_n_O in H.
  rewrite Rmult_0_l. assert (H1 := pos_INR (prod l)).
  apply (Rle_trans _ _ _ H1 H). apply (ex1' _ (S a) _ ) in H.
  rewrite plus_comm in H. rewrite (le_plus_minus_r _ _ H0) in H.
  apply H. assert (0 = INR 0). reflexivity. rewrite H2.
  apply le_INR. apply Peano.le_0_n.
Qed.

Theorem ex2 : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= Rpower 3 ((INR n) / 3))%R.
Proof.
  intros. apply ex1 in H. apply (Rle_trans _ _ _ H (I_n_q n)). Qed.

Theorem ex2_direct : forall (l : list nat) (n : nat),
  sum l = n -> (INR (prod l) <= Rpower 3 ((INR n) / 3))%R.
Proof.
  intros l. induction l; intros.
  { simpl in H. rewrite <- H. unfold I; simpl. unfold Rdiv.
    rewrite Rmult_0_l. rewrite Rpower_O; fourier.
  } simpl in H. symmetry in H. assert (a <= n)%nat. omega. 
  apply plus_minus in H. apply IHl in H. simpl. rewrite mult_INR.
  assert (n = a + (n - a))%nat. omega. rewrite H1. rewrite plus_INR.
  unfold Rdiv. rewrite Rmult_plus_distr_r.
  fold (Rdiv (INR a) (3)). unfold Rdiv in H. rewrite Rpower_plus.
  apply Rmult_le_compat; try apply pos_INR. apply n_q. auto.
Qed.

Theorem ex2_tight : forall (n : nat),
  (n >= 3)%nat ->
  exists (l : list nat),
    sum l = n /\ INR (prod l) = I n.
Proof.
  intros n H. destruct n. inversion H. destruct n. apply le_S_n in H; inversion H.
  destruct n. repeat apply le_S_n in H; inversion H. clear H.
  assert (S (S (S n)) = n + 3)%nat. omega. rewrite H; clear H.
  induction n using strong_induction.
  { unfold I. simpl. rewrite (Rplus_comm 2 1). unfold Rdiv. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup. exists (List.cons 3%nat List.nil). simpl.
    split; [reflexivity | Rcompute].
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H0.
  { inversion H0; subst. exists (List.cons 4%nat List.nil). simpl.
   split; auto. unfold I. simpl. assert ((2 + 1 + 1 -4)/3 = 0). field.
   rewrite H1. rewrite Rpower_O; prove_sup; field.
  } destruct H0.
  { inversion H0; subst. exists (List.cons 3 (List.cons 2 List.nil))%nat.
    split; auto. unfold I; simpl. assert ((2+1)/3 = 1). field. rewrite H1.
    rewrite Rpower_1; prove_sup; field.
  } destruct H0 as [m H0]. assert (m <= n)%nat. omega. apply H in H1.
  destruct H1 as [l H1]. destruct H1 as [Hs Hp]. exists (List.cons 3%nat l).
  split. simpl. omega. rewrite H0. rewrite <- I_unfold. rewrite Rmult_comm.
  simpl. fold (3 * prod l)%nat. rewrite mult_INR.
  simpl; rewrite Rplus_comm; rewrite Hp; auto.
Qed.

Definition L (n : nat) : nat :=
  if eq_nat_dec (n mod 3) 0 then 3^(n / 3)
  else if eq_nat_dec (n mod 3) 1 then 4 * 3^((n - 4)/3)
  else 2 * 3 ^((n-2)/3).

Example L_unfold : forall (n : nat),
  (2 <= n -> 3 * (L n) = L (n + 3))%nat. 
Proof.
  intros. destruct n. inversion H.
  destruct n. inversion H; inversion H1.
  assert (S (S n) = n + 2)%nat. omega.
  rewrite H0; clear.
  assert ((n + 2) mod 3 = (n + 2 + 3) mod 3).
  rewrite <- (Nat.add_mod_idemp_r _ 3); auto.
  unfold L. rewrite <- H.
  destruct (eq_nat_dec ((n + 2) mod 3) 0).
  { assert ((n + 2 + 3)/3 = (n + 2)/3 + 1)%nat.
    rewrite <- (Nat.mul_cancel_l _ _ 3); auto.
    symmetry in H. rewrite e in H.
    apply Nat.div_exact in H; apply Nat.div_exact in e; omega.
    rewrite H0. rewrite Nat.pow_add_r. simpl; omega.
  } destruct (eq_nat_dec ((n + 2) mod 3) 1).
  { assert (exists m, n + 2 = 3 * m + 4)%nat.
    assert (exists m, n + 2 = 3 * m + 1)%nat.
      exists ((n + 2)/3)%nat. rewrite <- e at 5.
      apply Nat.div_mod; auto.
    destruct H0 as [m H0]. rewrite H0.
    destruct m. omega. exists m. omega.
    destruct H0 as [m H0]. rewrite H0.
    assert (3 * m + 4 - 4 = 3 * m)%nat. omega.
    assert (3 * m + 4 + 3 - 4 = 3 * m + 3)%nat. omega.
    rewrite H1, H2. clear.
    assert (3 * m + 3 = (m + 1)*3)%nat. omega.
    rewrite H. rewrite (mult_comm 3 m).
    repeat rewrite Nat.div_mul; auto.
    rewrite Nat.pow_add_r. simpl; omega.
  } assert (n mod 3 = 0)%nat.
  destruct (eq_nat_dec (n mod 3) 0). auto.
  destruct (eq_nat_dec (n mod 3) 1).
  rewrite <- Nat.add_mod_idemp_l in n0; auto.
  rewrite e in n0. simpl in n0. omega.
  assert (H1 := mod3_eq_2 _ n2 n3).
  rewrite <- Nat.add_mod_idemp_l in n1; auto.
  rewrite H1 in n1. simpl in n1. omega.
  clear - H0. assert ((n + 3) mod 3 = 0)%nat.
  rewrite <- Nat.add_mod_idemp_l; [rewrite H0|]; auto.
  assert (n + 2 - 2 = n)%nat. omega. rewrite H1.
  assert ((n + 2 + 3 - 2)/3 = n/3 + 1)%nat.
  assert (n + 2 + 3 - 2 = n + 3)%nat. omega. rewrite H2.
  rewrite <- (Nat.mul_cancel_l _ _ 3); auto.
  apply Nat.div_exact in H0; apply Nat.div_exact in H; omega.
  rewrite H2. rewrite Nat.pow_add_r. simpl; omega.
Qed.

Lemma L_I : forall (n : nat),
  (2 <= n)%nat -> INR (L n) = I n.
Proof.
  intros. destruct n. omega. destruct n. omega. clear.
  assert (S (S n) = n + 2)%nat. omega. rewrite H; clear.
  induction n using strong_induction.
  { unfold L; unfold I; simpl. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup; field.
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H0.
  { inversion H0; subst. unfold L, I; simpl.
    assert ((2 + 1)/3 = 1). field. rewrite H1.
    rewrite Rpower_1; prove_sup; field.
  } destruct H0.
  { inversion H0; subst. unfold L, I; simpl.
    assert ((2 + 1 + 1 - 4)/3 = 0). field. rewrite H1.
   rewrite Rpower_O; prove_sup; field.
  } destruct H0 as [m H0]. rewrite H0.
  assert (m <= n)%nat. omega. apply H in H1.
  assert (m + 3 + 2 = m + 2 + 3)%nat. omega.
  rewrite H2. rewrite <- I_unfold. rewrite <- L_unfold.
  rewrite mult_INR; simpl; rewrite H1; field. omega.
Qed.