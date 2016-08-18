Set Implicit Arguments.
Require Import ZArith MSets.
Require Import mgraphs_ind pair_UOT.







Module Bleh : Graphs PositiveOrderedTypeBits.
  
  
  Module mset := MSetAVL.Make PositiveOrderedTypeBits.
  Module NodePair := (PairUsualOrderedType
                        PositiveOrderedTypeBits PositiveOrderedTypeBits).
  Module msetPair := MSetAVL.Make (NodePair).



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
  
  Parameter remove_vertex : t -> node -> t.
  Parameter remove_edge : t -> node * node -> t.

  
  
  Definition is_vertex : t -> node -> bool :=
    fun g x => mset.mem x (vertices g).
  Definition is_edge : t -> node * node -> bool :=
    fun g x => msetPair.mem x (edges g).
  Parameter neighborhood : t -> node -> node_set.
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
      
(* given H and H0 since n and n0 are not in v (g) then they must be equal to n1 and n2 then it should be possible to say that given Node n1 n2 being visible that (n, n0) is in the graph.*)
      Admitted.


    Lemma add_vertices_other :
      forall (x y : node) (g : t),
        x <> y -> mset.In y (vertices g) <-> mset.In y (vertices (add_vertex g x)).
    Proof.
      split; intros; induction g.
      inversion H0.
    Admitted.
    Parameter add_edges_other :
      forall (e1 e2 : node * node) (g : t),
        e1 <> e2 -> In e2 (edges g) <-> In e2 (edges (add_edge g e1)).
    Parameter add_vertices_pres_edges :
      forall (x : node) (g : t), Equal (edges (add_vertex g x)) (edges g).
    Parameter add_edges_pres_vertices :
      forall (x : node * node) (g : t),
        Equal (vertices (add_edge g x)) (vertices g).
    Parameter remove_vertices :
      forall (x : node) (g : t), ~ In x (vertices (remove_vertex g x)).
    Parameter remove_edges :
      forall (e : node * node) (g : t), ~ In e (edges (remove_edge g e)).
     Parameter remove_vertices_edges_l :
       forall (x1 : node) (g : t) (x2 : node),
       ~ In (x1, x2) (edges (remove_vertex g x1)).
     Parameter remove_vertices_edges_r :
       forall (x1 : node) (g : t) (x2 : node),
       ~ In (x2, x1) (edges (remove_vertex g x1)).
     Parameter remove_vertices_other :
       forall (x y : node) (g : t),
       x <> y -> In y (vertices g) <-> In y (vertices (remove_vertex g x)).
     Parameter remove_edges_other :
       forall (e1 e2 : node * node) (g : t),
       e1 <> e2 -> In e2 (edges g) <-> In e2 (edges (remove_edge g e1)).
     Parameter is_vertex_vertices :
       forall (x : elt) (g : t), In x (vertices g) <-> is_vertex g x = true.
     Parameter is_edge_edges :
       forall (e : elt) (g : t), In e (edges g) <-> is_edge g e = true.
     Parameter neighborhood_prop :
       forall (x : node) (y : elt) (g : t),
       In y (neighborhood g x) <-> In (x, y) (edges g).
     Parameter edges_proper_l :
       forall (x : elt) (g : t), In x (edges g) -> In (fst x) (vertices g).
     Parameter edges_proper_r :
       forall (x : elt) (g : t), In x (edges g) -> In (snd x) (vertices g).
Print Graphs.