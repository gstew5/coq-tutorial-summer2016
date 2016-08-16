Require Import Orders OrdersEx.

Module PairUsualOrderedType (O1 O2 : UsualOrderedType) <: UsualOrderedType.
  Definition t := prod O1.t O2.t.


  (* This is weird:
    Without this line, the module complains about
    the form of the equality props when you close
    the module. The fields this thing encomapsses
    are just definitions w/in the module and
    shouldn't need to be parameterized, right?
  *)
  Include HasUsualEq <+ UsualIsEq.

  Definition lt x y := 
    O1.lt (fst x) (fst y) \/
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    constructor.
    {
      unfold Irreflexive.
      unfold Reflexive, complement.
      intros. destruct x as (x1, x2).
      unfold lt in H.
      destruct H as [H | H].
      destruct (O1.lt_strorder) as [H0 H1].
      apply H0 in H; auto.
      destruct (O2.lt_strorder) as [H0 H1].
      destruct H as [H H2].
      apply H0 in H2; auto.
    }
    {
      unfold Transitive. intros.
      unfold lt in *.
      destruct H as [H | H]; destruct H0 as [H0 | H0].
      {
        left.
        destruct (O1.lt_strorder) as [H1 H2].
        apply H2 with (y := (fst y)); auto.
      }
      {
        left. destruct H0 as [H0 H1].
        unfold O1.eq in H0.
        rewrite H0 in H. auto.
      }
      {
        left. destruct H as [H  H1].
        unfold O1.eq in H. rewrite <- H in H0.
        auto.
      }
      {
        right.
        destruct H as [H H'].
        destruct H0 as [H0 H0'].
        split. unfold O1.eq in *.
        rewrite H; auto.
        destruct O2.lt_strorder as [H1 H1'].
        apply H1' with (y :=  snd y); auto.
      }
    }
  Qed.

  Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof.
    constructor; intros; subst; auto.
  Qed.

  Definition compare (x y : t) : comparison :=
    let (x1, x2) := x in
    let (y1, y2) := y in
      match O1.compare x1 y1 with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
          match O2.compare x2 y2 with
          | Lt => Lt
          | Gt => Gt
          | Eq => Eq
          end
      end.

  Lemma compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros.
    case_eq (compare x y); intros;
    constructor; destruct x as (x1, x2), y as (y1, y2);
    unfold compare in H;
    destruct (O1.compare_spec x1 y1);
    destruct (O2.compare_spec x2 y2);
    subst; auto; try congruence;
    unfold lt, O1.eq;
    try solve [ right; split; auto | left; auto].
  Qed.

  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    destruct x as (x1, x2), y as (y1, y2).
    destruct (O1.eq_dec x1 y1); 
    destruct (O2.eq_dec x2 y2);
    [left; f_equal; auto | right | right | right];
    intros H; inversion H; congruence.
  Qed.

End PairUsualOrderedType.