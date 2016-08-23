Set Implicit Arguments.
Require Import ZArith MSets.
Require Import mgraphs_ind pair_UOT.

Module Bleh : Graphs PositiveOrderedTypeBits.
  
  
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

  Notation "[ ]" := mset.empty.

  Notation "[ elt0 , .. , eltn ]" := (mset.add elt0 .. (mset.add eltn (mset.empty )) .. ) (at level 60, right associativity).



  Inductive graph : Type :=
  | Empty : graph
  | Node :
      node -> (** this node's id *)
      node_set -> (** its neighbors *)
      graph -> (** the rest of the graph *)
      graph.

  Fixpoint vertices g : node_set :=
    match g with
      | Empty => mset.empty
      | Node x s g' => mset.add x (vertices g')
    end.

  Fixpoint edges g : node_setPair :=
    match g with 
      | Empty => msetPair.empty
      | Node x s g' => mset.fold
                        (fun x' s' => msetPair.add (x,x') s')
                        s (edges g')
    end.

  Definition t := graph.
  Definition empty := Empty.
  Definition add_vertex : t -> node -> t :=
    fun t x => Node x mset.empty t.
  Definition add_edge: t -> node * node -> t :=
    fun g (x : node*node)  =>
      let (x1, x2) := x in
      if (mset.mem x1 (vertices g) && mset.mem x2 (vertices g))
      then Node x1 ([x2]) g
      else g.
  Fixpoint remove_vertex (g : graph) (n : node) :=
  match g with
  |Empty => Empty
  |Node n' adj g' => if Pos.eqb n' n then remove_vertex g' n
      else  Node n' adj g' (* this works because of the way edges are added.*)
  end.

Fixpoint remove_edge (g : graph) (e : (node * node) ) :=
  let x := (fst e) in
  let y := (snd e) in
  match g with
  |Empty => Empty
  |Node n adj g' => if Pos.eqb n x && (Nat.eqb (mset.cardinal adj) 1)(*probably don't need this*) && (mset.mem y adj)  then remove_edge g' e
                   else Node n adj (remove_edge g' e)
  end.


Fixpoint neighborhood (g : graph) (x : node) : node_set:=
  match g with
  | Empty => mset.empty
  | Node y adj g' =>
    if Pos.eqb x y then  mset.union adj (neighborhood g' x)
    else if mset.mem x adj then mset.add y (neighborhood g' x)
         else neighborhood g' x
  end.
  
    
  Definition is_vertex : t -> node -> bool :=
    fun g x => mset.mem x (vertices g).
  Definition is_edge : t -> node * node -> bool :=
    fun g x => msetPair.mem x (edges g).
  Lemma empty_vertices : vertices empty = mset.empty.
  Proof. reflexivity. Qed.
  Lemma empty_edges : edges empty = msetPair.empty.
  Proof. reflexivity. Qed.
  Lemma add_vertices :
    forall (x : node) (g : t), mset.In x (vertices (add_vertex g x)).
  Proof.
    intros.
    induction g; simpl; apply mset.add_spec;
    left; reflexivity.
  Qed.

  Lemma add_edges_helper :
    forall n n0 g,
       msetPair.In (n, n0) (edges (Node n ([n0]) g)).
    Proof.
      intros.
      induction g.
      constructor; auto.
      simpl. rewrite mset.fold_spec.
      simpl. apply msetPair.add_spec.
      auto.
    Qed.

    (* Lemma notin_vert_eq : *)
    (*   forall ( *)
   
  Lemma add_edges :
    forall (e : node * node) (g : t),
      mset.In (fst e) (vertices g) ->
      mset.In (snd e) (vertices g) ->
      msetPair.In e (edges (add_edge g e)).
  Proof.
    intros. destruct e.
    induction g; simpl.
    inversion H.
    apply mset.mem_spec in H; apply mset.mem_spec in H0.
    case_eq (mset.mem n (mset.add n1 (vertices g)));
      case_eq (mset.mem n0 (mset.add n1 (vertices g))).
    simpl (_ && _); cbv iota.
    {
      intros H1 H2.
      generalize (Node n1 n2 g).
      intros. apply msetPair.add_spec.
      auto.
    }
    {
      intros H1 H2. 
      simpl (_ && _); cbv iota.
      admit.
    }
    {
      intros.
      simpl ( _ && _); cbv iota.
      apply msetPair.mem_spec.
      admit.
    }
    {
      intros H1 H2.
      simpl (_ && _); cbv iota.
      admit.
   }
Admitted.

    Lemma add_vertices_other :
      forall (x y : node) (g : t),
        x <> y -> mset.In y (vertices g) <-> mset.In y (vertices (add_vertex g x)).
    Proof.
      split; intros; induction g.
      inversion H0.
      {
       unfold add_vertex.
       simpl. apply mset.add_spec.
       auto.
      }
      {
       simpl.
       inversion H0.
       symmetry in H2;
       contradiction.
       auto. auto.
      }
       simpl. apply mset.add_spec.
       unfold add_vertex in H0.
       simpl in H0. apply mset.add_spec in H0.
       destruct H0.
       symmetry in H0.
       contradiction.
       apply mset.add_spec in H0.
       auto.
    Qed.


    Lemma in_add_edge_in_add :
      forall e1 e2 g, msetPair.In e2 (edges (add_edge g e1)) ->msetPair.In e2 (msetPair.add e1 (edges (g))).
      Proof.
        intros.
        induction g.
        simpl. simpl in H.
        Admitted.
      


    Lemma add_edges_other :
      forall (e1 e2 : node * node) (g : t),
        e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (add_edge g e1)).
    Proof.
      intros; split; induction g; auto.
      {
       inversion 1.
      }
      {
        intros. unfold add_edge. 
        simpl.  destruct e1.
        
        case_eq (mset.mem n1 (mset.add n (vertices g)));
          case_eq ( mset.mem n2 (mset.add n (vertices g))).
       
          intros H1 H2; simpl (_ && _); cbv iota.
          apply msetPair.add_spec;
          auto.
          auto.
          auto. auto.
      }
      {
        intros.
        unfold add_edge in H0.
        simpl (_ && _) in H0. cbv iota in H0.
        simpl (let (_, _) := e1 in Empty) in H0.
        admit.
      }
      {
        intros.
        apply msetPair_prop.Dec.F.add_3 with (x := e1).
        auto. apply in_add_edge_in_add.
        auto.
      }
    Admitted.
       
    Lemma add_vertices_pres_edges :
      forall (x : node) (g : t), msetPair.Equal (edges (add_vertex g x)) (edges g).
    Proof.
      intros.
      reflexivity.
    Qed.
    
    Lemma add_edges_pres_vertices :
      forall (x : node * node) (g : t),
        mset.Equal (vertices (add_edge g x)) (vertices g).
    Proof.
      intros.
      unfold add_edge. destruct x.
      case_eq (mset.mem n (vertices g));
        case_eq ( mset.mem n0 (vertices g)).
      {
        intros H1 H2; simpl. (*(_ && _); cbv iota.*)
        apply mset.mem_spec in H2.
        apply mset_prop.add_equal.
        auto.
      }

      {
        reflexivity.
      }
      {
        reflexivity.
      }
      reflexivity.
    Qed.
         
    Lemma remove_vertices :
      forall (x : node) (g : t), ~ mset.In x (vertices (remove_vertex g x)).
    Proof.
      intros.
      induction g.
      simpl. unfold not. intros. apply mset.mem_spec in H.
      inversion H.
      unfold not.
      intros. apply mset.mem_spec in H. 
      apply IHg.
      apply mset.mem_spec in H.
      simpl in H.
      Admitted.

    Lemma remove_edges :
      forall (e : node * node) (g : t), ~ msetPair.In e (edges (remove_edge g e)).
    Proof.
      intros.
      unfold not. intros. induction g.
      inversion H.
      Admitted.


    Lemma remove_vertices_edges_l :
        forall (x1 : node) (g : t) (x2 : node),
          ~ msetPair.In (x1, x2) (edges (remove_vertex g x1)).
    Proof.
      intros. unfold not. intros.
      induction g.
      inversion H.
    Admitted.
    
    Lemma remove_vertices_edges_r :
        forall (x1 : node) (g : t) (x2 : node),
          ~ msetPair.In (x2, x1) (edges (remove_vertex g x1)).
    Proof.
      intros.
    Admitted.
    
    Lemma remove_vertices_other :
        forall (x y : node) (g : t),
          x <> y ->  mset.In y (vertices g) <-> mset.In y (vertices (remove_vertex g x)).
    Proof.
      intros.
      split. intros.
      induction g.
      auto. simpl.
      destruct (n =? x)%positive.
      Focus 2.
      simpl.
      apply mset.add_spec.
      apply mset.add_spec in H0.
      destruct H0.
      auto.
      auto.
      {
        admit.
      }
      
      admit.
    Admitted.
    
    Lemma remove_edges_other :
      forall (e1 e2 : node * node) (g : t),
        e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (remove_edge g e1)).
    Proof.
      intros.
      split; induction g.
      {
        auto.
      }
      {
        intro H1.
        simpl.
        
admit.
      }
      {
        auto.
      }





      Lemma is_vertex_vertices :
        forall (x : node) (g : t), mset.In x (vertices g) <-> is_vertex g x = true.
      Proof.
        intros;
        split; apply mset.mem_spec.
      Qed.
      
      Lemma is_edge_edges :
        forall (e : node * node ) (g : t), msetPair.In e (edges g) <-> is_edge g e = true.
      Proof.
        intros.
        split; apply msetPair.mem_spec.
      Qed.
      

      Lemma neighborhood_prop :
        forall (x : node) (y : node) (g : t),
          mset.In y (neighborhood g x) <-> msetPair.In (x, y) (edges g).
      Proof.
        intros; split. intros.  apply msetPair.mem_spec.
        induction g.
        inversion H.
        destruct H.
        subst.
        simpl in H.
Admitted.        




        

      Parameter edges_proper_l :
        forall (e : node * node) (g : t), msetPair.In e (edges g) -> mset.In (fst e) (vertices g).
      Parameter edges_proper_r :
        forall (e : node * node ) (g : t), msetPair.In e (edges g) -> mset.In (snd e) (vertices g).
End Bleh.
Print Graphs.

Module graph_prop := graph_properties  PositiveOrderedTypeBits Bleh.
Print graph_prop.