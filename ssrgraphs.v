Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Record graph := mkGraph
  { T :> finType 
  ; e : rel T
  ; active : {set T}}.
      
Section basics.
  Variable g : graph.

  Definition rem (s : {set g}) : graph :=
    mkGraph
      [rel y z : g | if (y \in s) || (z \in s) then false else e y z]
      (active g :\: s).
  
  Definition ind :=
    [pred s : {set g} | [forall x in s, forall y in s, ~~e x y]].

  Lemma indP (s : {set g}) :
    reflect (forall x y, x \in s -> y \in s -> ~e x y) (ind s).
  Proof.
    case H: (ind s); constructor.
    { move=> x y H0 H1 H2.
      move: (forallP H); move/(_ x)/implyP/(_ H0)/forallP/(_ y)/implyP/(_ H1).
        by rewrite H2. }
    have H0: negb (ind s) by rewrite H.
    clear H; rewrite negb_forall in H0; case: (existsP H0)=> x.
    rewrite negb_imply; case/andP=> H1.
    rewrite negb_forall; case/existsP=> y.
    rewrite negb_imply; case/andP=> H2; move/negbNE=> H3 H4.
    by move: (H4 x y H1 H2).
  Qed.    
    
  Definition mis :=
    [pred s : {set g} |
     [&& ind s
      & [forall x, (x \notin s) ==> (x \in active g) ==> ~~ind (x |: s)]]].
  
  Lemma mis_ind s : mis s -> ind s.
  Proof. by case/andP. Qed.

  Lemma misP (s : {set g}) :
    reflect [/\ ind s & forall x, x \notin s -> x \in active g -> ~ind (x |: s)]
            (mis s).
  Proof.      
    case H: (mis s); constructor.
    { split; first by apply: mis_ind.
      move=> x H2 H3; case: (andP H)=> H4; move/forallP/(_ x).
      by move/implyP/(_ H2)/implyP/(_ H3)/negP. }
    have H0: ~~ mis s by rewrite H.
    move=> []H1 H2; rewrite negb_and in H0; case: (orP H0); first by rewrite H1.
    move/forallP; apply=> x; apply/implyP=> H3; apply/implyP=> H4.
    by apply/negP; apply: H2.
  Qed.    

  Definition neighborhood (x : g) := x |: [set y | e x y].

  Lemma neighborhoodP x y : reflect (x = y \/ e x y) (y \in neighborhood x).
  Proof.
    case H: (y \in neighborhood x); constructor.
    { move: H; rewrite /neighborhood in_setU1; case/orP.
      by case/eqP=> ->; left.
      by rewrite in_set=> H; right. }
    move=> H2; move: H; rewrite /neighborhood in_set; case: H2.
    { by move=> ->; rewrite in_set1 eq_refl. }
    by move=> H; rewrite in_set H orbC.
  Qed.    
End basics.

Section mis_lems.
  Variable g : graph.
  Hypothesis esym : forall x y, e (g:=g) x y -> e (g:=g) y x.
  Hypothesis eirrefl : forall x, ~e (g:=g) x x.
  
  Lemma m_neigh_in x (s : {set g}) :
    mis g s -> x \in s -> mis (rem (neighborhood x)) (s :\: neighborhood x).
  Proof.
    case/misP; move/indP=> H0 H1 H2; apply/misP; split.
    { apply/indP=> y z H3 H4 H5.
      rewrite in_setD in H3; case: (andP H3)=> Hx Hy. clear H3.
      rewrite in_setD in H4; case: (andP H4)=> Hz Hw. clear H4.
      apply: (H0 y z)=> //; move: H5=> /=; move: Hx Hz.
      case: (_ \in _)=> //.
      case: (_ \in _)=> //. }      
    move=> y H3 H4; move/indP=> H5.
    have H6: y \in active g.
    { by move: H4; rewrite /active /= in_setD; case/andP. }
    case H7: (y \in neighborhood (g:=g) x).
    { by move: H4; rewrite /active /=; rewrite in_setD H7. }
    have H8: y \notin s.
    { by rewrite in_setD H7 /= in H3. }
    apply: (H1 y)=> //; apply/indP=> z w H9 H10.
    rewrite in_setU1 in H9; rewrite in_setU1 in H10=> H11; case: (orP H9).
    { move/eqP=> e; subst z; case: (orP H10).
      { by move/eqP=> e; subst w; apply: (eirrefl H11). }
      move=> H12; case: (neighborhoodP x w).
      { case=> H13. 
        { subst w; move: H7; case: (neighborhoodP x y)=> //.
          by move=> H13 _; apply: H13; right; apply: esym. }
        apply: (H0 x w)=> //. }
      move=> H13.
      apply: (H5 y w); first by rewrite in_setU1 eq_refl.
      rewrite in_setU1; apply/orP; right.
      rewrite in_setD; apply/andP; split=> //.
      by case: (neighborhoodP x w).
        by rewrite /rem /= H7 /=; case: (neighborhoodP x w). }
    move=> H12; case: (orP H10).
    { move/eqP=> H13; subst w; case: (neighborhoodP x z).
      { case.
        { move=> H13; subst z.
          move: H7; case: (neighborhoodP x y)=> // H13 _.
          by apply: H13; right. }
        by move=> H13; apply: (H0 x z). }
      move=> H13; apply: (H5 y z).
      by rewrite in_setU1; apply/orP; left.
      rewrite in_setU1; apply/orP; right; rewrite in_setD.
      apply/andP; split=> //; first by case: (neighborhoodP x z).
      rewrite /rem /= H7 /=; case: (neighborhoodP x z)=> //.
      by move=> _; apply: esym. }
    move=> H13; case: (neighborhoodP x w).
    { case=> H14; first by by subst w; apply: (H0 z x).
      by apply: (H0 x w). }
    move=> H14; case: (neighborhoodP x z).
    { case=> H15; first by subst z; apply: (H0 x w).
      by apply: (H0 x z). }
    move=> H15; apply: (H5 z w).
    rewrite in_setU1; apply/orP; right; rewrite in_setD.
    apply/andP; split=> //; first by case: (neighborhoodP x z).
    rewrite in_setU1; apply/orP; right; rewrite in_setD.
    apply/andP; split=> //; first by case: (neighborhoodP x w).
    rewrite /rem /=; case: (neighborhoodP x z)=> //.
    by case: (neighborhoodP x w).
  Qed.    

  Lemma m_neigh_nin x (s : {set g}) :
    mis g s -> x \notin s -> mis (rem (set1 x)) s.
  Proof.
    case/misP; move/indP=> H0 H1 H2; apply/misP; split.
    { apply/indP=> y z H5 H6 H7.
      apply: (H0 y z)=> //.
      move: H7; rewrite /rem /= 2!in_set1. 
      by case: (y == x)=> //; case: (z == x). }
    move=> y; rewrite in_setD1; move/negP=> H3 H4; move/indP=> H5.
    case H6: (y == x).
    { move: (eqP H6)=> eq; subst y; clear H6.
      by move: H4; rewrite /rem /= eq_refl. }
    case H7: (y \in s); first by apply: H3. 
    apply: (H1 y); first by rewrite H7.
    { by move: H4; rewrite /rem /=; case/andP. }
    apply/indP => z w; rewrite !in_setU1 => H8 H9 H10.
    case: (orP H8).
    { move/eqP => e; subst y.
      case: (orP H9); first by move/eqP=> e; subst w; apply: (eirrefl H10).
      move=> H11; case H12: (w == x).
      { by move: (eqP H12)=> e; subst w; rewrite H11 in H2. }
      apply: (H5 z w); first by rewrite in_setU1; apply/orP; left.
      by rewrite in_setU1; apply/orP; right.
      by rewrite /rem /= !in_set1 H6 H12. }
    move=> H11; case: (orP H9).
    { move/eqP => e; subst w; case H12: (z == x).
      { by move: (eqP H12) => e; subst z; rewrite H11 in H2. }
      apply: (H5 z y); first by rewrite in_setU1; apply/orP; right.
      by rewrite in_setU1; apply/orP; left.
      by rewrite /rem /= !in_set1 H12 H6. }
    by move=> H12; apply: (H0 z w).
  Qed.
  
  Lemma m_neighborhood x :
    #|mis g| <= #|mis (rem (set1 x))| + #|mis (rem (g:=g) (neighborhood x))|.
  Proof.
    have H: forall s,
      mis g s -> 
      (x \notin s /\ mis (rem (set1 x)) s) \/
      (x \in s /\ mis (rem (g:=g) (neighborhood x)) (s :\: neighborhood x)).
    { move=> s H; case H1: (x \in s).
      by right; split=> //; apply: m_neigh_in.
      by left; split=> //; apply: m_neigh_nin=> //; rewrite H1. }
  Admitted.  
End mis_lems.  



  

