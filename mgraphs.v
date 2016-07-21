Set Implicit Arguments.

Require Import ZArith List Bool.
Require Import MSets MSetWeakList MSetRBT.

Module SetFunctorList (E : OrderedType) : WSetsOn E
  := MSetWeakList.Make E.

Module SetFunctorRBT (E : OrderedType) 
  : MSetInterface.S with Module E := E
  := MSetRBT.Make E.

Module Type RawGraph (Node : UsualOrderedType) (F : WSetsOn).
  Notation node := Node.t.
  Module NodeSet := F Node.
  Notation node_set := NodeSet.t.

  Parameter t : Type.
  Parameter inv : t -> Prop.

  Parameter Empty : t.
  Parameter Empty_inv : inv Empty.
  
  Parameter Node :
    forall (x : node) (adj : node_set) (g : t), t.
  Parameter Node_inv :
    forall x adj g,
      inv g ->
      inv (Node x adj g).
  
  Parameter ind :
    forall P : t -> Prop,
      P Empty ->
      (forall (n : node) (adj : node_set) (g : t),
          inv g -> P g -> P (Node n adj g)) ->
      forall g : t, inv g -> P g.

  Parameter fold :
    forall
      (T : Type)
      (FEmpty : t -> T)      
      (FNode : node -> node_set -> T -> T),
      forall (g : t), inv g -> T.

  Parameter fold_ind :
    forall
      (T : Type)
      (FEmpty : t -> T)
      (FNode : node -> node_set -> T -> T)
      (R : t -> T -> Prop),
      R Empty (FEmpty Empty) ->
      (forall x adj g (pf : inv g),
          let g' := fold FEmpty FNode pf in
          R g g' -> 
          R (Node x adj g) (FNode x adj g')) ->
      forall (g : t) (pf : inv g),
        R g (fold FEmpty FNode pf).
End RawGraph.

Require Import POrderedType.
Require Import graphs.

Lemma NoDup_NoDupA_eq :
  forall (A : Type) (l : list A),
    NoDup l <-> NoDupA eq l.
Proof.
  induction l;
  try solve[split; intros; constructor].
  split; inversion 1; subst; constructor; auto.
  { intros H4. rewrite InA_alt in H4.
    destruct H4 as [y [H5 H6]]. subst a. contradiction. }
  rewrite <-IHl; auto.
  intros H4. apply In_InA with (eqA:=eq) in H4. contradiction.
  apply eq_equivalence.
  rewrite IHl; auto.
Qed.  

Module InductiveRawGraph : RawGraph Positive_as_OT MSetWeakList.Make.
  Module NodeSet := MSetWeakList.Make Positive_as_OT.
  Notation node_set := NodeSet.t.

  Inductive graph_NoDup : graph -> Prop :=
  | EmptyNoDup : graph_NoDup Empty
  | NodeNoDup :
      forall x adj g,
        NoDup adj ->
        graph_NoDup g -> 
        graph_NoDup (Node x adj g). 

  Definition t := graph.
  Definition inv := graph_NoDup.

  Definition Empty := Empty.

  Lemma Empty_inv : inv Empty. Proof. apply EmptyNoDup. Qed.

  Definition Node (x : node) (adj : node_set) (g : t) :=
    Node x (NodeSet.this adj) g.

  Lemma Node_inv :
    forall x adj g,
      inv g ->
      inv (Node x adj g).
  Proof.
    intros x adj g H0.
    apply NodeNoDup; auto.
    generalize (NodeSet.is_ok adj).
    unfold NodeSet.Raw.Ok. generalize (NodeSet.this adj) as l.
    intros l H. rewrite NoDup_NoDupA_eq. auto.
  Qed.    
  
  Lemma ind :
    forall P : t -> Prop,
      P Empty ->
      (forall (n : node) (adj : node_set) (g : t),
          inv g -> P g -> P (Node n adj g)) ->
      forall g : t, inv g -> P g.
  Proof.
    intros P H IH g H2.
    revert H2.
    set (X := fun g => inv g -> P g).
    change (X g).
    apply graph_ind; unfold X; auto.
    intros n l g' H3.
    inversion 1; subst.
    unfold Node in IH.
    assert (H7: NodeSet.Raw.Ok l).
    { unfold NodeSet.Raw.Ok.
      rewrite <-NoDup_NoDupA_eq; apply H4. }
    set (l' := NodeSet.Mkt l).
    inversion H0; subst.
    apply (IH n l' g' H9); auto.
  Qed.

  Lemma fold_lem1 (g : t) (pf : inv g) x adj g' (H : g = graphs.Node x adj g') :
    NodeSet.Raw.Ok adj.
  Proof.
    rewrite H in pf.
    inversion pf; subst.
    rewrite NoDup_NoDupA_eq in H2; auto.
  Qed.    

  Lemma fold_lem2 (g : t) (pf : inv g) x adj g' (H : g = graphs.Node x adj g') :
    inv g'.
  Proof.
    rewrite H in pf.
    inversion pf; subst.
    auto.
  Qed.
  
  Fixpoint fold
           (T : Type)
           (FEmpty : t -> T)
           (FNode : node -> node_set -> T -> T)
           (g : t)
           (pf : inv g) : T :=
    (match g as g0 return _ = g0 -> _ with
    | graphs.Empty => fun _ => FEmpty g
    | graphs.Node x adj g' =>
      fun pf' =>
        let adj' := @NodeSet.Mkt _ (fold_lem1 pf pf')
        in FNode x adj' (fold FEmpty FNode (fold_lem2 pf pf'))
     end) eq_refl.

  Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
  
  Lemma fold_ind :
    forall
      (T : Type)
      (FEmpty : t -> T)
      (FNode : node -> node_set -> T -> T)
      (R : t -> T -> Prop),
      R Empty (FEmpty Empty) ->
      (forall x adj g (pf : inv g),
          let g' := fold FEmpty FNode pf in
          R g g' -> 
          R (Node x adj g) (FNode x adj g')) ->
      forall (g : t) (pf : inv g),
        R g (fold FEmpty FNode pf).
  Proof.
    intros.
    revert pf.
    induction g; auto.
    unfold fold. fold fold.
    intros pf.
    unfold Node in H0.
    assert (H1 : NodeSet.Raw.Ok l).
    { unfold NodeSet.Raw.Ok. rewrite <-NoDup_NoDupA_eq.
      inversion pf; subst; auto. }
    set (l' := @NodeSet.Mkt l H1).
    inversion pf; subst.
    specialize (H0 n l' g H6).
    assert (H7 : H1 = fold_lem1 pf eq_refl).
    { apply proof_irrelevance. }
    subst H1.
    assert (H8 : H6 = fold_lem2 pf eq_refl).
    { apply proof_irrelevance. }
    subst H6.
    auto.
  Qed.
End InductiveRawGraph.
  
  
  