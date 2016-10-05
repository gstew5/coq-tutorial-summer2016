Set Implicit Arguments.
Require Import ZArith MSets.
Require Import mgraphs_ind pair_UOT.

Module graph_inst : Graphs PositiveOrderedTypeBits.
  
  
  Module mset := MSetAVL.Make PositiveOrderedTypeBits.
  Module NodePair := (PairUsualOrderedType
                        PositiveOrderedTypeBits PositiveOrderedTypeBits).
  Module msetPair := MSetAVL.Make (NodePair).

  Module mset_facts := WFacts (mset).
  Module msetPair_facts := WFacts (msetPair).
  Module mset_prop := WProperties (mset).
  Module msetPair_prop := WProperties (msetPair).

  Definition node := positive.
  Definition nodePair := NodePair.t.
  Definition node_set := mset.t.
  Definition node_setPair := msetPair.t.

  (* Notation "[ ]" := mset.empty. *)

  (* Notation "[ elt0 , .. , eltn ]" := (mset.add elt0 .. (mset.add eltn (mset.empty )) .. ) (at level 60, right associativity). *)

  Inductive graph : Type :=
  | Empty : graph
  | Node :
      node -> (** this node's id *)
      node_set -> (** its neighbors *)
      graph -> (** the rest of the graph *)
      graph.
(*vert to graph_vert*)
    Fixpoint graph_vertices' g : node_set :=
    match g with
      | Empty => mset.empty
      | Node x s g' => mset.add x (graph_vertices' g')
    end.

  
  Inductive graph_ok : graph -> Prop :=
  | EmptyOk : graph_ok Empty 
  | NodeOk : forall (x : node) (adj : node_set) (g : graph),
      graph_ok g ->
      (forall (y : node), mset.In y adj -> mset.In y (graph_vertices' g)) ->
      graph_ok (Node x adj g).
  Definition valid_graph := {g : graph | graph_ok g}.
  
  Definition proj1 (vg : valid_graph) : graph :=
    let (g, pf) := vg in g. 

  Definition project1 T: (graph -> T) -> (valid_graph -> T).
    intros.
    destruct X0.
    apply X.
    auto.
    Defined.
  
  Definition graph_vertices (vg: valid_graph) := (project1 graph_vertices') vg.

  Definition ok T: forall (vg : valid_graph) (g : graph) (f : graph -> T), f (proj1 vg) = (project1 f) vg.
    intros.
    destruct vg.
    auto.
    Defined.
    
Print ok.


  (* Fixpoint edges' g : node_setPair := *)
  (*   match g with *)
  (*     | Empty => msetPair.empty *)
  (*     | Node x s g' =>  msetPair.union (mset.fold (fun x' s'=> msetPair.add (x,x') s') s msetPair.empty) (edges' g') *)
  (*   end. *)



(*   Lemma node_ok_graph_ok : forall n adj g, graph_ok (Node n adj g) -> graph_ok g /\   (forall (y : node), mset.In y adj -> mset.In y (graph_vertices g)). *)
(*   Proof. *)
(*     intros. *)
(*     split. *)
(*     inversion H. *)
(*     auto. *)
(*     inversion H. *)
(*     auto. *)
(* Qed.     *)
  Lemma emptyOk : graph_ok Empty.
  Proof.
    constructor.
  Qed.

  Definition t := valid_graph.
  Definition empty : valid_graph.  
  assert (graph_ok Empty).
  constructor.
  exists (Empty).
  exact H.
  Defined.

    Fixpoint edges' ( g : graph) : node_setPair :=
      match g with
      | Empty => msetPair.empty
      | Node x s g' => mset.fold (fun x' s' => msetPair.add (x,x') s')
                        s (edges' g')
    end.

  Definition edges (vg : t) : node_setPair := edges' (proj1 vg).
 
  Definition add_vertex' : graph -> node -> graph :=
    fun t x => Node x mset.empty t.




  Theorem add_vertex_ok : forall v g, graph_ok g -> graph_ok (add_vertex' g v).
  Proof.
    intros.
    induction g.
    constructor.
    auto.
    intros y H1.
    auto.
    unfold add_vertex'.
    constructor; auto.
    intros y H1.
    inversion H1.
Qed.



  
  Definition add_vertex (vg : valid_graph) (v : node) : valid_graph. 
  Proof.
    exists (add_vertex' (proj1 vg) v).
    apply add_vertex_ok.
    destruct vg.
    simpl.
    exact g.
    Defined.

  Definition add_edge': graph -> node * node -> graph :=
    fun g (x : node*node)  =>
      let (x1, x2) := x in
      if (mset.mem x1 (graph_vertices' g) && mset.mem x2 (graph_vertices' g))
      then Node x1 (mset.add x2 mset.empty) g
      else g.

  Theorem add_edge_ok : forall e g, graph_ok g -> graph_ok (add_edge' g e).
  Proof.
    intros e g H.
    destruct e.
    induction g.
    auto.
    simpl.
    destruct (mset.mem n (mset.add n1 (graph_vertices' g)) &&
                        mset.mem n0 (mset.add n1 (graph_vertices' g))) eqn:H1.
    apply andb_true_iff in H1.
    destruct H1.
    constructor.
    auto.
    intros y H2.
    apply mset_prop.singleton_equal_add in H2.
    apply mset_prop.Dec.F.singleton_1 in H2.
    simpl.
    subst.
    apply mset.mem_spec.
    auto.
    auto.
  Qed.

  Definition add_edge : valid_graph ->  node * node -> valid_graph.
    intros.
    exists (add_edge' (proj1 X) H).
    apply add_edge_ok.
    destruct X.
    simpl.
    exact g.
    Defined.
  
  

  
  
  Fixpoint remove_vertex' (g : graph) (n : node) :=
  match g with
  |Empty => Empty
  |Node n' adj g' => if Pos.eqb n' n then remove_vertex' g' n
      else  Node n' adj (remove_vertex' g' n)
  end.

    Lemma remove_vertex_ok : forall g v, graph_ok g -> graph_ok (remove_vertex' g v).
    Proof.
      induction g.
      constructor.
      simpl.
      intros.
      destruct ((n =? v)%positive) eqn:H1.
      apply IHg.
      inversion H.
      auto.
      constructor.
      inversion H.
      auto.
      intros.
      inversion H.
      subst.
      apply (IHg v) in H4.
    Admitted.
    

  Definition remove_vertex (vg : t) (v : node) : t.  
    exists (remove_vertex' (proj1 vg) v).
    apply remove_vertex_ok.
    destruct vg.
    exact g.
    Defined.

  Fixpoint remove_edge' (g : graph) (e : (node * node) ) :=
    let x := (fst e) in
    let y := (snd e) in
    match g with
    |Empty => Empty
    |Node n adj g' => if Pos.eqb n x  then Node n (mset.remove y adj) (remove_edge' g' e)
                      else Node n adj (remove_edge' g' e)
    end.

  Lemma remove_edge_ok : forall (g : graph) ( e : (node * node)),
      graph_ok g -> graph_ok (remove_edge' g e).
  Proof.
    Admitted.

  Definition remove_edge (vg : t) (e : node * node ) : t.
    exists (remove_edge' (proj1 vg) e).
    apply remove_edge_ok.
    destruct vg.
    exact g.
    Defined.
  
  Fixpoint neighborhood' (g : graph) (x : node) : node_set:=
    match g with
    | Empty => mset.empty
    | Node y adj g' =>
      if Pos.eqb x y then  mset.union adj (neighborhood' g' x)
      else if mset.mem x adj then mset.add y (neighborhood' g' x)
           else neighborhood' g' x
    end.
  Definition neighborhood := (project1 neighborhood').
    
  Definition is_vertex' : graph -> node -> bool :=
    fun g x => mset.mem x (graph_vertices' g).
  Definition is_vertex := (project1 is_vertex').
  Definition is_edge' : graph -> node * node -> bool :=
    fun g x => msetPair.mem x (edges' g).

  Definition is_edge := (project1 is_edge').


  Lemma empty_vertices : graph_vertices empty = mset.empty.
  Proof. reflexivity. Qed.
  Lemma empty_edges : edges empty = msetPair.empty.
  Proof. reflexivity. Qed.

  Definition pairset_of_nodes (n : node) (e : node_set) :=
    mset.fold (fun (x : node) l => msetPair.add (n, x) l) e msetPair.empty.

  Lemma folds_equal : forall n n0 s ,
      msetPair.Equal
        ((mset.fold
          (fun (x' : mset.elt) (s' : msetPair.t) =>
             msetPair.add (n, x') s') n0 (s)))
      ((msetPair.union (pairset_of_nodes n n0) (s))).
    Proof.
      intros.
      unfold pairset_of_nodes.
      apply mset_prop.fold_rec_bis.
      {
        intros. rewrite H0.
        apply mset_prop.fold_equal with (s := s0) (s' := s').
        
        admit.
        admit.
        admit.
        apply H.
      }
      {
        rewrite mset_prop.fold_1b.
        admit. admit. 
      }
      {
        intros.
        split. simpl.
        intros. rewrite mset_prop.fold_add.
        rewrite msetPair.union_spec.
Admitted.




    (*   Open Scope positive_scope.*)
  (*  Example ex1 : graph := *)
  (* Node 1 ([2,  3]) *)
  (*      (Node 2 ([3]) *)
  (*            (Node 3 [] Empty)). *)
   
  (*  Compute (msetPair.elements (edges ex1)). *)
  (*  Compute (msetPair.elements (edges' ex1)). *)

  Lemma add_vertices :
    forall (x : node) (g : t), mset.In x (graph_vertices (add_vertex g x)).
  Proof.
    intros.
    induction g; simpl; apply mset.add_spec;
    left; reflexivity.
  Qed.

  Lemma add_edges_aux :
    forall n n0 n1 g,  n = n1 /\ mset.In n0 (graph_vertices' g) \/ n1 = n0 /\ mset.In n (graph_vertices' g) ->
       mset.mem n (mset.add n1 (graph_vertices' g)) &&                              mset.mem n0 (mset.add n1 (graph_vertices' g)) = true.
    Proof.
      intros.
      subst.
      apply andb_true_iff.
      destruct H;
      destruct H;
      split;
      rewrite mset.mem_spec;
      rewrite mset.add_spec;
      auto.
      Qed.


  Lemma add_edges :
    forall (e : node * node) (g : t),
      mset.In (fst e) (graph_vertices g) ->
      mset.In (snd e) (graph_vertices g) ->
      msetPair.In e (edges (add_edge g e)).
  Proof.
    intros. destruct e.
    destruct g as [g  pf].
    unfold edges; unfold add_edge;
    induction g; simpl.
    simpl in H, H0.
    inversion H.
    simpl in H, H0.
    apply mset.add_spec in H.
    apply mset.add_spec in H0.    
    destruct H, H0.
    {
      assert ( mset.mem n (mset.add n1 (graph_vertices' g)) = true).
      rewrite mset.mem_spec.
      apply mset_prop.Dec.F.add_iff.
      auto. subst.
      rewrite H1.
      simpl ( _ && _).
      cbv iota.
      apply msetPair.add_spec.
      auto.
    }    
   
      rewrite add_edges_aux; auto.
      generalize (Node n1 n2 g);
      intro g0;
      simpl;
      apply msetPair.add_spec;
      auto.
    {
      rewrite add_edges_aux; auto.
      generalize (Node n1 n2 g).
      intro g0;
      simpl;
      apply msetPair.add_spec;
      auto.
    }
    {
      assert ( mset.mem n (mset.add n1 (graph_vertices' g)) = true).
      rewrite mset.mem_spec.
      apply mset_prop.Dec.F.add_iff.
      auto.
      rewrite H1.
      assert (mset.mem n0 (mset.add n1 (graph_vertices' g)) = true).
      rewrite mset.mem_spec.
      apply mset_prop.Dec.F.add_iff.
      auto.
      rewrite H2.
      simpl ( _ && _); cbv iota.
      generalize (Node n1 n2 g).
      intro g0.
      simpl.
      apply msetPair.add_spec.
      auto.
    }
  Qed.

    Lemma add_vertices_other :
      forall (x y : node) (g : t),
        x <> y -> mset.In y (graph_vertices g) <-> mset.In y (graph_vertices (add_vertex g x)).
    Proof.
      split; intros; induction g.
      inversion H0.
      {
       unfold add_vertex.
       simpl. apply mset.add_spec.
       auto.
      }
      {
       simpl in H0.
       inversion H0.
       subst.
       simpl.
       apply mset.add_spec.
       auto.
       simpl.
       apply mset.add_spec.
       auto.
       simpl.
       apply mset.add_spec.
       auto.
      }
       simpl. apply mset.add_spec.
       unfold add_vertex in H0.
       simpl in H0. auto.
       simpl.
       simpl in H0.
       apply mset.add_spec in H0.
       destruct H0.
       symmetry in H0.
       contradiction.
       auto.
    Qed.

    Lemma add_edges_other :
      forall (e1 e2 : node * node) (g : t),
        e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (add_edge g e1)).
    Proof.
      intros; split.  destruct g as [g pf]. induction g; unfold edges in *; unfold add_edge in *; simpl.
      {
        inversion 1.
      }
      {
        intros. unfold add_edge. 
        simpl.  destruct e1.
        case_eq (mset.mem n1 (mset.add n (graph_vertices' g)));
          case_eq ( mset.mem n2 (mset.add n (graph_vertices' g)));
       simpl;
        intros;
        rewrite H1, H2;
        simpl (_ && _); cbv iota;
        simpl; auto;
        apply msetPair.add_spec; auto.
      }
      {
        simpl.
        unfold edges, add_edge.
        simpl.
        intros.
        unfold add_edge' in H0.
        apply msetPair_prop.Dec.F.add_3 with (x := e1).
        auto. rewrite msetPair.add_spec.
        right.
        destruct e1, e2.
        destruct g as [g pf].
        simpl in *.
        destruct (mset.mem n (graph_vertices' g) && mset.mem n0 (graph_vertices' g)) eqn:H1.
        apply folds_equal in H0.
        apply msetPair.union_spec in H0.
        fold edges' in H0.
        destruct H0.
        unfold pairset_of_nodes in H0.
        rewrite mset.fold_spec in H0.
        simpl in H0.
        Focus 2.
        auto.
        Focus 2.
        auto.
        apply msetPair.add_spec in H0.
        destruct H0.
        symmetry in H0.
        apply H in H0.
        destruct H0.
        inversion H0.
        }
    Qed.


    Lemma add_vertices_pres_edges :
      forall (x : node) (g : t), msetPair.Equal (edges (add_vertex g x)) (edges g).
    Proof.
      intros.
      reflexivity.
    Qed.
    
    Lemma add_edges_pres_vertices :
      forall (x : node * node) (g : t),
        mset.Equal (graph_vertices (add_edge g x)) (graph_vertices g).
    Proof.
      intros.
      destruct g as [g pf].
      unfold add_edge. destruct x.
      simpl.
      case_eq (mset.mem n (graph_vertices' g));
      case_eq ( mset.mem n0 (graph_vertices' g)); try (reflexivity).
      {
        intros H1 H2; simpl.
        apply mset.mem_spec in H2.
        apply mset_prop.add_equal.
        auto.
      }
    Qed.
         
    Lemma remove_vertices :
      forall (x : node) (g : t), ~ mset.In x (graph_vertices (remove_vertex g x)).
    Proof.
      intros.
      unfold graph_vertices, remove_vertex.
      destruct g as [ g pf].
      induction g.
      simpl.
      inversion 1.
      unfold not in *.
      intros.
      simpl in H.
      case_eq ((n =? x)%positive).
      intros.
      rewrite H0 in H.
      simpl in IHg.
      apply Peqb_true_eq in H0.
      inversion pf. subst.
      auto.
      intros.
      rewrite H0 in H.
      simpl in H.
      rewrite mset.add_spec in H.
      destruct H.
      apply Pos.eqb_neq in H0.
      unfold not in H0.
      auto.
      simpl in *.
      inversion pf. subst.
      auto.
    Qed.
    
    Lemma remove_edges :
      forall (e : node * node) (g : t), ~ msetPair.In e (edges (remove_edge g e)).
    Proof.
      intros.
      destruct e.
      unfold not, remove_edge. intros. destruct g as [g pf].
      induction g.
      inversion H.
      simpl in *.
      inversion pf. subst.
      apply IHg with (pf := H2).
      case_eq ((n1 =? n)%positive).
      intros.
      apply Peqb_true_eq in H0.
      subst.
      assert ((n =? n)%positive = true).
      apply Pos.eqb_refl.
      Focus 2.
      intros.
      apply Pos.eqb_neq in H0.
      apply Pos.eqb_neq in H0.
    Admitted.


    Lemma remove_vertices_edges_l :
        forall (x1 : node) (g : t) (x2 : node),
          ~ msetPair.In (x1, x2) (edges (remove_vertex g x1)).
    Proof.
      intros. unfold not. intros.
      induction g.
      inversion H.
      simpl in H.
      auto.
    Admitted.



    Lemma remove_vertices_edges_r :
        forall (x1 : node) (g : t) (x2 : node),
          ~ msetPair.In (x2, x1) (edges (remove_vertex g x1)).
    Proof.
      unfold not.
      intros.
      induction g.
      inversion H.
      simpl in H.
      
    Admitted.

    Lemma remove_vertices_other :
        forall (x y : node) (g : t),
          x <> y ->  mset.In y (graph_vertices g) <-> mset.In y (graph_vertices (remove_vertex g x)).
    Proof.
      intros.
      destruct g as [g pf].
      unfold graph_vertices, remove_vertex.
      simpl.
      split. intros.
      induction g.
      auto. simpl.
      simpl in H0.
      rewrite mset.add_spec in H0.
      destruct H0.
      {
        destruct ((n =? x)%positive) eqn:H1.
        apply Peqb_true_eq in H1.
        rewrite H1 in H0.
        unfold not in H.
        symmetry in H0.
        apply H in H0.
        destruct H0.
        simpl.
        apply mset.add_spec.
        auto.
      }
      {
        apply IHg in H0.
        destruct ((n =? x)%positive) eqn:H1.
        auto.
        simpl.
        apply mset.add_spec.
        auto.
        inversion pf.
        auto.
      }
      induction g.
      intro H0.
      inversion H0.
      intro H0.
      unfold remove_vertex in H0.
      simpl in *.
      case_eq ((n =? x)%positive); intros H1.
      rewrite H1 in H0.
      apply mset.add_spec.
      right.
      inversion pf. subst.
      apply IHg; auto.
      rewrite H1 in H0.
      simpl in *.
      rewrite mset.add_spec.
      rewrite mset.add_spec in H0.
      destruct H0.
      auto.
      right.
      inversion pf.
      apply IHg; auto.
    Qed.
    
    (* Lemma in_edge_node_or_graph : *)
    (*   forall (g : t) n n0(e : node * node) , *)
    (*     msetPair.In e (edges (Node n n0 g)) -> *)
    (*       (msetPair.In e (pairset_of_nodes n n0) \/ msetPair.In e (edges g)). *)
    (* Proof. *)
    (*   intros. *)
    (*   generalize dependent g. *)
    (*   generalize dependent n. *)
    (*   generalize dependent n0. *)
    (*   induction g. *)
    (*   auto. *)
    (*   intros. *)
    (*   Admitted. *)
      

Lemma remove_edges_other :
      forall (e1 e2 : node * node) (g : t),
        e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (remove_edge g e1)).
    Proof.
      intros. destruct e1,e2.
      destruct g as [g pf].
      induction g.
      {
        split.
        auto.
        auto.
      }
      {
        split.
        intro H1.
        simpl.
        destruct H1.
      Admitted.


      Lemma is_vertex_vertices :
        forall (x : node) (g : t), mset.In x (graph_vertices g) <-> is_vertex g x = true.
      Proof.
        destruct g as [g pf].
        intros;
        split; apply mset.mem_spec.
      Qed.
      
      Lemma is_edge_edges :
        forall (e : node * node ) (g : t), msetPair.In e (edges g) <-> is_edge g e = true.
      Proof.
        intros. destruct g as [g pf].
        split; apply msetPair.mem_spec.
      Qed.
      

      Lemma neighborhood_prop :
        forall (x : node) (y : node) (g : t),
          mset.In y (neighborhood g x) <-> msetPair.In (x, y) (edges g).
      Proof.
        intros.
      Admitted.        


      Lemma node_edges_weaken : forall (g : graph) (n x y : node) n0  (e :=(x, y) : node * node),
      msetPair.In (x,y) (edges' (Node n n0 g)) ->
      x = n /\ mset.In y n0 \/ msetPair.In e (edges' g).
    Proof.
      intros. simpl in H.
    Admitted.
      
      Lemma edges_proper_l :
        forall (e : node * node) (g : t), msetPair.In e (edges g) -> mset.In (fst e) (graph_vertices g).
      Proof.
        intros.
        destruct g as [g pf].
        induction g.
        inversion H.
        destruct e.
        apply node_edges_weaken in H.
        destruct H.
        simpl.
        apply mset.add_spec. 
        destruct H.
        auto.
        inversion pf.
        apply IHg with (pf := H2) in H.
        simpl.
        apply mset.add_spec.
        auto.
Qed.
      Lemma edges_proper_r :
        forall (e : node * node ) (g : t), msetPair.In e (edges g) -> mset.In (snd e) (graph_vertices g).
      Proof.
        intros.
        destruct g as [g pf].
        induction g.
        intros.
        inversion H.
        simpl.
        destruct e.
        apply  node_edges_weaken in H.
        destruct H.
        simpl; apply mset.add_spec.
        destruct H.
        right.
        Admitted.

End graph_inst.
Print Graphs.

Module graph_prop := graph_properties  PositiveOrderedTypeBits graph_inst.
Print graph_prop.