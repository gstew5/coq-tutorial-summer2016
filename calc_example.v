Require Import Reals Rpower Ranalysis Fourier.
Require Import mathcomp.ssreflect.ssreflect.

Print exp.
Print exist_exp.
Print ln.
Print Rln.
Check ln_exists.

Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
Proof.
  intros h.
  rewrite /ln.
  case_eq (Rlt_dec 0 (1-x)); move => h1 h2;
  last by apply False_rec; apply h1; fourier.
  rewrite /Rln => /=.
  destruct (ln_exists (1 - x) h1) as [x0 e0].
  apply Rplus_le_reg_l with (r := 1%R).
  rewrite /Rminus in e0.
  rewrite e0.
  SearchAbout exp.
  Check exp_ineq1.
  left.
  apply exp_ineq1.
    (*
|:(
    *) 
  Abort.

(*
Goal : forall x, 1 + x <= exp x.
*)















Check MVT_cor1.





























Lemma aux_const' : derivable (fun x => (exp x - (1 +x))%R).
Proof.
  apply derivable_minus.
  apply derivable_exp.
  apply derivable_plus.
  apply derivable_const.
  apply derivable_id.
Qed.


Lemma aux_neg y (H :(y < 0)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const' y < 0)%R.
Proof.
  SearchAbout derive.
  rewrite /derive.
  SearchAbout derive_pt.
  (* apply derive_pt_minus. *)
Abort.

Definition aux_const x : derivable_pt (fun x => (exp x - (1 +x))%R) x :=
  derivable_pt_minus exp (Rplus 1) x (derivable_pt_exp x)
    (derivable_pt_plus (fun _ : R => 1%R) id x (derivable_pt_const 1 x)
    (derivable_pt_id x)).

Lemma aux_neg y (H :(y < 0)%R) :
  (derive (fun x => (exp x - (1 + x))%R) aux_const y < 0)%R.
Proof.
  rewrite /derive /aux_const
          derive_pt_minus
          derive_pt_exp
          derive_pt_plus
          derive_pt_const
          derive_pt_id.
  apply Rlt_minus.
  rewrite -exp_0 Rplus_0_l.
  apply exp_increasing => //.
Qed.

Lemma aux_pos y (H :(0 <= y)%R) :
  (derive (fun x => (exp x - (1 + x))%R) aux_const y >= 0)%R.
Proof.
  rewrite /derive /aux_const
          derive_pt_minus
          derive_pt_exp
          derive_pt_plus
          derive_pt_const
          derive_pt_id.
  apply Rge_minus.
  rewrite -exp_0 Rplus_0_l.
  apply Rle_ge.
  case: H => H;
  first by left; apply exp_increasing => //.
  right. f_equal => //.
Qed.

Lemma ln_Taylor_upper' x : ((1 + x) <= exp x)%R.
Proof.
  apply Rge_le.
  apply Rminus_ge.
  set f := fun x => (exp x - (1 + x))%R.
  have H0 : (f x = exp x - (1 + x))%R => //.
  rewrite -H0; clear H0.
  have H0 : (f 0 = 0)%R by
    rewrite /f exp_0 Rplus_0_r;
    apply Rminus_diag_eq => //.
  rewrite -H0.
  case: (Rtotal_order x 0) => H.
  {
    left.
    apply (MVT_cor1 f x 0 aux_const) in H.
    case: H => c; case => H1 H2.
    rewrite H0 !Rminus_0_l in H1.
    rewrite H0.
    have H3 :  (x < 0)%R
      by case: H2 =>  H2 H3; apply (Rlt_trans x c 0) => //.
    apply Ropp_eq_compat in H1.
    rewrite Ropp_involutive in H1.
    rewrite H1.
    apply Rlt_gt.
    rewrite Ropp_mult_distr_l.
    apply Rmult_lt_0_compat.
    apply Ropp_0_gt_lt_contravar.
    apply Rlt_gt.
    apply aux_neg.
    case: H2 => //.
    fourier.
  }
  {
    case: H => H;
    first by subst; rewrite /f Rplus_0_r exp_0; right => //.
    apply (MVT_cor1 f 0 x aux_const) in H.
    case: H => c; case => H1 H2.
    rewrite H0 !Rminus_0_r in H1.
    rewrite H0.
    have H3 :  (0 < x)%R
      by case: H2 =>  H2 H3; apply (Rlt_trans 0 c x) => //.
    rewrite H1.
    apply Rle_ge.
    rewrite -(Rmult_0_l x).
    apply Rmult_le_compat.
    right => //.
    left => //.
    apply Rge_le.
    apply aux_pos.
    left. case: H2 => //.
    right => //.
  }
Qed.

Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
Proof.
  intros h.
  rewrite /ln.
  case_eq (Rlt_dec 0 (1-x)); move => h1 h2;
  last by apply False_rec; apply h1; fourier.
  rewrite /Rln => /=.
  destruct (ln_exists (1 - x) h1) as [x0 e0].
  apply Rplus_le_reg_l with (r := 1%R).
  rewrite /Rminus in e0.
  rewrite e0.
  apply ln_Taylor_upper'.
Qed.
