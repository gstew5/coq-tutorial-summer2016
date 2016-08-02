Require Import Reals Rpower Ranalysis Fourier.

Check MVT_cor1.
(* MVT_cor1 requires us to show that f is derivable, but we also need to
   reason about the derivative at the value c provided by the theorem.

   In order to do this eaisily, we want to use the lemmas
   derive_pt_plus, derive_pt_minus, etc..., but these lemmas
   require our proof of derivability to be constructed in a 
   particular way.  
*)

(* Two ways to build the proof of derivable so we can use the
   afformentioned lemmas:
    - Interactively => aux_const.
    - Manually => aux_const'.
*)
Lemma aux_const : derivable (fun x => (exp x - (1 +x))%R).
Proof.
  unfold derivable. intros x.
  apply derivable_pt_minus.
  apply derivable_pt_exp.
  apply derivable_pt_plus.
  apply derivable_pt_const.
  apply derivable_pt_id.
Defined. (* Later we'll need to reason about how this proof
            was built, so we end the proof with defined rather
            than Qed. *)

Definition aux_const' x : derivable_pt (fun x => (exp x - (1 +x))%R) x :=
  derivable_pt_minus exp (Rplus 1) x (derivable_pt_exp x)
    (derivable_pt_plus (fun _ : R => 1%R) id x (derivable_pt_const 1 x)
    (derivable_pt_id x)).

(* Really these are the same things, and we can prove it... *)
Lemma aux_eq : aux_const = aux_const'.
Proof.
  auto.
Qed.

(* Proof: If y < 0, then the derivative of this function at y is negative *)
Lemma aux_neg y (H :(y < 0)%R) :
  (derive (fun x => (exp x - (1 + x))%R) aux_const y < 0)%R.
Proof.
  unfold derive, aux_const.
  (* The rewritng here isn't as good as ssreflect's, so we need to
     apply the decomposition manually *)
  rewrite (derive_pt_minus (fun x => exp x) (fun x => (1 + x)%R)).
  rewrite derive_pt_exp.
  rewrite (derive_pt_plus (fun _ : R => 1) id).
  rewrite (derive_pt_const 1).
  rewrite (derive_pt_id).
  apply Rlt_minus.
  rewrite <- exp_0.
  rewrite Rplus_0_l.
  apply exp_increasing; exact H.
Qed.

(* Proof: If 0 <= y, then the derivative of this function at y is positive *)
Lemma aux_pos y (H :(0 <= y)%R) :
  (derive (fun x => (exp x - (1 + x))%R) aux_const y >= 0)%R.
Proof.
  unfold derive, aux_const.
  rewrite (derive_pt_minus (fun x => exp x) (fun x => (1 + x)%R)).
  rewrite derive_pt_exp.
  rewrite (derive_pt_plus (fun _ : R => 1) id).
  rewrite (derive_pt_const 1).
  rewrite (derive_pt_id).
  rewrite Rplus_0_l.
  apply Rge_minus.
  rewrite <- exp_0.
  destruct H.
  left. apply exp_increasing. auto.
  subst. fourier.
Qed.

(* We use the MVT + the above results to show that *)
Lemma ln_Taylor_upper' x : ((1 + x) <= exp x)%R.
Proof.
  apply Rge_le.
  apply Rminus_ge.
  set (f := fun x => (exp x - (1 + x))%R).
  assert (f x = exp x - (1 + x)%R) as H0.
    unfold f. auto.
  rewrite <- H0; clear H0.
  assert (f 0 = 0)%R as H0.
    unfold f. rewrite exp_0, Rplus_0_r.
    apply Rminus_diag_eq; auto.
  rewrite <- H0.
  case_eq (Rtotal_order x 0); intros H.
  {
    left. clear H1.
    apply (MVT_cor1 f x 0 aux_const) in H.
    destruct H as [c [H1 [H2 H3]]].
    rewrite H0, Rminus_0_l, Rminus_0_l in H1.
    rewrite H0.
    assert (x < 0)%R as H4. apply (Rlt_trans x c 0); auto.
    apply Ropp_eq_compat in H1.
    rewrite Ropp_involutive in H1.
    rewrite H1.
    apply Rlt_gt.
    rewrite Ropp_mult_distr_l.
    apply Rmult_lt_0_compat.
    apply Ropp_0_gt_lt_contravar.
    apply Rlt_gt.
    apply aux_neg; auto.
    fourier.
  }
  {
    destruct H as [H | H].
    { intros _; subst; right; auto. }
    intros _.
    apply (MVT_cor1 f 0 x aux_const) in H.
    destruct H as [c [H1 [H2 H3]]].
    rewrite H0, Rminus_0_r, Rminus_0_r in H1.
    rewrite H0.
    assert (0 <= x)%R as H4. fourier.
    rewrite H1.
    apply Rle_ge.
    rewrite <- (Rmult_0_l x).
    apply Rmult_le_compat; try fourier.
    apply Rge_le.
    apply aux_pos.
    left; auto.
  }
Qed.

Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
Proof.
  intros h.
  unfold ln.
  case_eq (Rlt_dec 0 (1-x)); intros h1 h2;
  last by apply False_rec; apply h1; fourier.
  unfold Rln; simpl.
  destruct (ln_exists (1 - x) h1) as [x0 e0].
  apply Rplus_le_reg_l with (r := 1%R).
  unfold Rminus in e0.
  rewrite e0.
  apply ln_Taylor_upper'.
Qed.
