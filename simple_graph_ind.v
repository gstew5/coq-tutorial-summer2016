Set Implicit Arguments.
(*End of the file has a functor that takes a Graph and gives properties. The graph implementation is not close to being done*)
Require Import ZArith List Bool pair_UOT.
Require Import MSets MSetFacts.
Require Import mgraphs_ind.


Module simple_graph
  : Graphs Positive_as_OT.
      Module Nodet := Positive_as_OT.
      Module NodePair := PairUsualOrderedType Nodet Nodet.
      Module mset := MSetAVL.Make Nodet.
      Module msetPair := MSetAVL.Make NodePair.
      Module mset_facts := WFacts (mset).
      Module msetPair_facts := WFacts (msetPair).
      Module mset_prop := WProperties (mset).
      Module msetPair_prop := WProperties (msetPair).
      Definition node := Nodet.t.
      Definition nodePair := NodePair.t.
      Definition node_set := mset.t.
      Definition node_setPair := msetPair.t.
      
      Inductive graph : Type :=
      | Empty : graph
      | Node :
          node -> (** this node's id *)
          node_set -> (** its neighbors *)
          graph -> (** the rest of the graph *)
          graph.
      
      Definition t := graph.
      Definition empty := Empty.

Definition add := Nodet.add.

Definition node_eqb := Nodet.eqb.

Lemma node_eqb_eq :
  forall x y : node,
    node_eqb x y = true <-> x = y.
Proof.
  intros x y; unfold node_eqb.
  apply Pos.eqb_eq.
Qed.

Lemma node_eqb_refl :
  forall x,
    node_eqb x x = true.
Proof.
  intros x; unfold node_eqb.
  apply Pos.eqb_refl.
Qed.  

Lemma node_eqbP :
  forall x y : node,
    reflect (x = y) (node_eqb x y).
Proof.
  intros.
  destruct (node_eqb x y) eqn:H.
  rewrite node_eqb_eq in H. constructor; auto.
  constructor; intros H2; rewrite H2, node_eqb_refl in H.
  congruence.
Qed.  


Fixpoint graph_contains (x : node) (g : graph) : bool :=
  match g with
  | Empty => false
  | Node y adj g' =>
    if node_eqb x y then true
    else graph_contains x g'
  end.

Inductive graph_Contains : node -> graph ->  Prop :=
| gc_inst : forall x g l, graph_Contains x (Node x l g) 
| gc_subg : forall x g, graph_Contains x g ->
          forall y l, graph_Contains x (Node y l g).

Lemma graph_containsP : forall x g,
  reflect (graph_Contains x g) (graph_contains x g).
Proof.
  intros x g.
  induction g.
  constructor.
  intros h.
  inversion h.
  simpl.
  case_eq (node_eqb x n);
  intros h.
  apply node_eqb_eq in h.
  subst.
  constructor.
  constructor.
  case_eq (graph_contains x g);
  intros h1.
  apply ReflectT.
  apply gc_subg.
  destruct IHg; auto.
  inversion h1.
  constructor.
  intros h2.
  inversion h2; subst.
  rewrite node_eqb_refl in h.
  inversion h.
  apply reflect_iff in IHg.
  apply IHg in H1.
  rewrite H1 in h1.
  inversion h1.
Qed.

Definition nodeset_contains (x : node) (s : node_set) :=
  mset.mem x s.
      
      (* Definition add_node  (g : graph)  (adj : node_set) *)
      (*   : graph := *)
      (*   if negb (graph_contains x g) *)
      (*           && negb (nodeset_contains x adj) *)
      (*           && mset.for_all (fun y => graph_contains y g) adj *)
      (*   then Node x adj g *)
      (*   else g. *)


Definition add_vertex (g : graph) (n : node) :=
   if negb (graph_contains n g) then 
   Node n mset.empty g else g.

Fixpoint add_edge (g : graph) (e : (node * node)) :=
  let x' := (fst e) in 
  match g with
  |Empty => Empty
  |Node x adj g' => if node_eqb x' x then Node x (mset.add x' adj) g' else add_edge g' e
   end.
 
Fixpoint remove_vertex (g : graph) (n : node) :=
  match g with
  |Empty => Empty
  |Node n' adj g' => if node_eqb n' n then remove_vertex g' n
       else  Node n' (mset.remove n adj) (remove_vertex g' n)
  end.

(*It is possible to make a graph with edges form a-b and b-a but since it is undirected maybe that should not be allowed or should be forced, need to come back to it*)
Fixpoint remove_edge (g : graph) (e : (node * node) ) :=
  let x := (fst e) in
  let y := (snd e) in 
  match g with
  |Empty => Empty
  |Node n adj g' => if node_eqb n x then Node n (mset.remove y adj) g'
                   else Node n adj (remove_edge g' e)
  end.

Fixpoint vertices (g : graph) : node_set :=
  match g with
  |Empty => mset.empty
  |Node n adj g' => mset.add n (vertices g')
  end.
Check map.

Fixpoint msetMap (l : list node) (n : node) : node_setPair :=
  match l with
  |nil => msetPair.empty
  |cons h t => msetPair.add (n, h) (msetMap t n)
  end.

(*maybe just return a list of pairs*)
Fixpoint edges (g : graph) : node_setPair :=
  match g with
  |Empty => msetPair.empty
  |Node n adj g' => msetPair.union (msetMap (mset.elements adj) n) (edges g')
  end.

Fixpoint is_vertex (g : graph) (n : node) :=
  match g with
  |Empty => false
  |Node n' adj g' => if node_eqb n' n then true
                    else is_vertex g' n
  end.

Fixpoint is_edge (g : graph) (e : (node * node)) :=
  let x := (fst e) in
  let y := (snd e) in 
  match g with
  |Empty => false
  |Node n adj g' => if node_eqb x n && nodeset_contains y adj then true
                   else is_edge g' e
  end.

Fixpoint neighborhood (g : graph) (x : node) : node_set:=
  match g with
  | Empty => mset.empty
  | Node y adj g' =>
    if node_eqb x y then  mset.union adj (neighborhood g' x)
    else if nodeset_contains x adj then mset.add y (neighborhood g' x)
         else neighborhood g' x
  end.

Lemma empty_vertices : vertices empty = mset.empty.
Proof.
  auto.
Qed.  
Lemma empty_edges : edges empty = msetPair.empty.
Proof.
  auto.
Qed.


Lemma inVert_graph_Contains : forall x g,
    graph_contains x g = true -> mset.In x (vertices g).
Proof.
  intros.
  induction g.
  simpl. inversion H.
  Admitted.
  
  

 Lemma add_vertices :
       forall (x : node) (g : t), mset.In x (vertices (add_vertex g x)).
 Proof.
   intros.
   unfold add_vertex.
   destruct (negb (graph_contains x g)) eqn:H.
   simpl. apply mset.add_spec.
   auto. apply negb_false_iff in H.
   apply inVert_graph_Contains. auto.
Qed.

  Lemma add_edges :
       forall (e : node * node) (g : t),
       mset.In (fst e) (vertices g) ->
       mset.In (snd e) (vertices g) -> msetPair.In e (edges (add_edge g e)).
  Proof.
    induction g.
    inversion 1.
    intros.
    apply msetPair.mem_spec.
    apply mset.mem_spec in H. 
    destruct e.
Admitted.



  Lemma add_vertices_other :
       forall (x y : node) (g : t),
         x <> y -> mset.In y (vertices g) <-> mset.In y (vertices (add_vertex g x)).
  Proof.
    intros.
    split.
    Focus 2.
    intros.
    Admitted.


     Parameter add_edges_other :
       forall (e1 e2 : node * node) (g : t),
         e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (add_edge g e1)).

      Parameter add_vertices_pres_edges :
       forall (x : node) (g : t), edges (add_vertex g x) = edges g.
     Parameter add_edges_pres_vertices :
       forall (x : node * node) (g : t),
       vertices (add_edge g x) = vertices g.

     Parameter remove_vertices :
       forall (x : node) (g : t), ~ mset.In x (vertices (remove_vertex g x)).
     Parameter remove_edges :
       forall (e : node * node) (g : t), ~ msetPair.In e (edges (remove_edge g e)).
     Parameter remove_vertices_edges_l :
       forall (x1 : node) (g : t) (x2 : node),
       ~ msetPair.In (x1, x2) (edges (remove_vertex g x1)).
     Parameter remove_vertices_edges_r :
       forall (x1 : node) (g : t) (x2 : node),
       ~ msetPair.In (x2, x1) (edges (remove_vertex g x1)).
     Parameter remove_vertices_other :
       forall (x y : node) (g : t),
       x <> y -> mset.In y (vertices g) <-> mset.In y (vertices (remove_vertex g x)).
     Parameter remove_edges_other :
       forall (e1 e2 : node * node) (g : t),
       e1 <> e2 -> msetPair.In e2 (edges g) <-> msetPair.In e2 (edges (remove_edge g e1)).
     Parameter is_vertex_vertices :
       forall (x : node) (g : t),
       mset.In x (vertices g) <-> is_vertex g x = true.
     Parameter is_edge_edges :
       forall (e : (node* node)) (g : t), msetPair.In e (edges g) <-> is_edge g e = true.
     Parameter neighborhood_prop :
       forall (x : node) (y : node) (g : t),
       mset.In y (neighborhood g x) <-> msetPair.In (x, y) (edges g).
     Parameter edges_proper_l :
       forall (x : (node * node) ) (g : t), msetPair.In x (edges g) -> mset.In (fst x) (vertices g).
     Parameter edges_proper_r :
       forall (x : (node * node) ) (g : t), msetPair.In x (edges g) -> mset.In (snd x) (vertices g).
End simple_graph.


Module g_prop := graph_properties Positive_as_OT simple_graph.
Print g_prop.