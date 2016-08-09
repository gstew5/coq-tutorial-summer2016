Set Implicit Arguments.

Require Import ZArith List Bool MSets.

Definition node := positive.

Module mset := MSetAVL.Make Positive_as_OT.

Notation node_set := mset.t.

Print mset. (*Functions over sets!*)

Definition add := Pos.add.

Definition node_eqb := Pos.eqb.

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
(*
Origonal graph

(** Undirected Graphs *)
Inductive graph : Type :=
| Empty : graph
| Node :
    node -> (** this node's id *)
    node_set -> (** its neighbors *)
    graph -> (** the rest of the graph *)
    graph.
*)

Inductive graph : Type :=
| Leaf : graph
| Node :
  node -> (* Vertex label*)
  node_set -> (* Adjecentcy list *)
  graph -> (* left subtree *)
  graph -> (* right subtre *)
  graph. 


Check graph.
Local Open Scope positive_scope.
Require Import MSets.MSetInterface.
Notation "[ ]" := mset.empty.

Notation "[ elt0 , .. , eltn ]" := (mset.add elt0 .. (mset.add eltn (mset.empty )) .. ) (at level 60, right associativity).

Example RefSet: node_set :=
  mset.add 4( mset.add 5 ( mset.add 4 mset.empty)).

Compute mset.elements RefSet.
Print RefSet.
Check mset.empty.

Compute mset.exists_ (fun y  =>  Pos.eqb y 4) RefSet. 
(* new example *)
Example ex1 : graph :=
  Node 1 ( [2,3] ) 
    (Node 2 ( [3] ) Leaf Leaf)
    (Node 3  [] Leaf Leaf).

Example ex2 : graph :=
  Node 3 ( [2,1])
  ( Node 2 ( [1]) Leaf Leaf) 
  ( Node 1 ( [5] )
    ( Node 5 [] Leaf Leaf)
    Leaf ).

(* This was made with the old graph
Example ex1 : graph :=
  Node 1 ([2,  3])
       (Node 2 ([3])
             (Node 3 [] Empty)).

Example ex2 : graph :=
  Node 3 ([2,1])
       (Node 2 ([1])
             (Node 1 ([5])
                   (Node 5 [] Empty))).
*)
(** Return the adjacency list associated by graph g
    with node x. *)
Fixpoint adj_of (x : node) (g : graph) : node_set :=
  match g with
  | Leaf => mset.empty
  | Node y adj l r =>
    if node_eqb x y then  adj
    else 
    mset.union (adj_of x l) (adj_of x r)
  end.

Compute mset.elements (adj_of 3 ex2).
Print mset. (**)

(** Return all neighbors in g of node x. *)
Definition nodeset_contains (x : node) (s : node_set) :=
  mset.mem x s.

Lemma nodelist_containsP :
  forall (x : node) (s : node_set),
    reflect (mset.In x s) (nodeset_contains x s).
Proof.
  intros.
  apply iff_reflect.
  unfold nodeset_contains.
  symmetry.
  apply mset.mem_spec.
Qed.

(* old one, for reference
Fixpoint neighbors_of (x : node) (g : graph) : node_set:=
  match g with
  | Empty => mset.empty
  | Node y adj g' =>
    if node_eqb x y then  mset.union adj (neighbors_of x g')
    else if nodeset_contains x adj then mset.add y (neighbors_of x g')
         else neighbors_of x g'
  end.
*)


(* I hope this is right :^) *)
Fixpoint neighbors_of (x : node) (g : graph) : node_set:=
  match g with
  | Leaf => mset.empty
  | Node y adj l r =>
    if node_eqb x y then  mset.union adj (mset.union (neighbors_of x l)(neighbors_of x r))
    else if nodeset_contains x adj then mset.add y (mset.union (neighbors_of x l) (neighbors_of x r))
         else mset.union (neighbors_of x l) (neighbors_of x r)
  end.

Compute neighbors_of 5 ex2.


Definition is_neighbor (x y : node) (g : graph) : bool :=
  nodeset_contains x (neighbors_of y g).

Compute is_neighbor 3 5 ex2.

Fixpoint graph_contains (x : node) (g : graph) : bool :=
  match g with
  | Leaf => false
  | Node y adj l r =>
    if node_eqb x y then true
    else orb (graph_contains x l) (graph_contains x r)
  end.

Compute graph_contains 5 ex2.


Inductive graph_Contains : node -> graph ->  Prop :=
| gc_inst : forall x adj l r, graph_Contains x (Node x adj l r) 
| gc_subg : forall x l r, or (graph_Contains x l) (graph_Contains x r) ->
          forall y adj l r, graph_Contains x (Node y adj l r).

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
  case_eq (graph_contains x g1);
  intros h1.
  apply ReflectT.
  apply gc_subg with ( l := g1) (r := g1).
  left.
  rewrite h1 in IHg1.
  SearchAbout reflect.
  apply reflect_iff in IHg1.
  apply IHg1.
  auto.
(*
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
*)
Admitted.


(* for reference
Inductive is_Neighbor : node -> node -> graph -> Prop :=
| IN_inl : forall x y l g, mset.In y l -> is_Neighbor x y (Node x l g)
| IN_inr : forall x y l g, mset.In x l -> is_Neighbor x y (Node y l g)
| IN_subg : forall x y g, is_Neighbor x y g ->
              forall z l, is_Neighbor x y (Node z l g).
*)

Inductive is_Neighbor : node -> node -> graph -> Prop :=
| IN_inl : forall x y l g, mset.In y l -> is_Neighbor x y (Node x l g)
| IN_inr : forall x y l g, mset.In x l -> is_Neighbor x y (Node y l g)
| IN_subg : forall x y g, is_Neighbor x y g ->
              forall z l, is_Neighbor x y (Node z l g).

Lemma is_Neighbor_symm x y g :
  is_Neighbor x y g -> is_Neighbor y x g.
Proof.
  induction g; intros h;
  inversion h; subst;
  constructor; auto.
Qed.

Lemma is_NeighborP : forall x y g,
  reflect (is_Neighbor x y g) (is_neighbor x y g).
Proof.
  intros x y g.
  induction g.
  constructor.
  intros h.
  inversion h.
  apply iff_reflect.
  split; intros h.
  inversion h; subst.
  {
    unfold is_neighbor.
    apply (reflect_iff (mset.In n (neighbors_of y (Node n t g)))).
    apply nodelist_containsP.
    unfold neighbors_of.
    destruct node_eqb;
    fold neighbors_of.
    apply mset.union_spec.
    
    right.
    unfold neighbors_of.
    
    admit.
  (*   apply (reflect_iff (In y l) (nodelist_contains y l)) in  H2. *)
  (*   rewrite H2. simpl; left; auto. *)
  (*   apply nodelist_containsP. *)
  (* } *)
  (* { *)
    admit.
  }
  {
    admit.
  }
  {
    admit. 
  }
Admitted.

Inductive graph_ok : graph -> Prop :=
| EmptyOk : graph_ok Empty
| NodeOk :
    forall (x : node) (adj : node_set) (g : graph),
      graph_contains x g = false ->
      mset.for_all (fun y => graph_contains y g) adj = true -> (** No self-loops! *)
      graph_ok g ->
      graph_ok (Node x adj g).

Compute mset.elements ([1, 1, 2]).

(** A so-called "smart constructor" for "Node". 
    We enforce the following two properties: 
      1) "x" is not already in the graph; 
      2) every node in "adj" is in the graph. *)
Definition add_node (x : node) (adj : node_set) (g : graph) : graph :=
  if negb (graph_contains x g)
          && negb (nodeset_contains x adj)
          && mset.for_all (fun y => graph_contains y g) adj
  then Node x adj g
  else g.

Lemma add_node_ok :
  forall x adj g,
    graph_ok g ->
    graph_ok (add_node x adj g).
Proof.
  intros x adj g H.
  unfold add_node.
  destruct (negb (graph_contains x g)) eqn:H3;
  destruct (negb (nodeset_contains x adj)) eqn:H4;
  destruct (mset.for_all (fun y : mset.elt => graph_contains y g) adj) eqn:H0; auto. simpl.
  apply NodeOk; auto.
  apply negb_true_iff. auto.
Qed.

Lemma ex1_graph_ok : graph_ok ex1.
Proof.
  unfold ex1; repeat (constructor; auto).
  (*apply NodeOk; auto.
  apply NodeOk; auto.
  apply NodeOk; auto.
  apply EmptyOk.*)
Qed.  

Lemma msetfilter_property :
  forall (s : node_set) (f : mset.elt -> bool),
    mset.for_all f ( mset.filter f s) = true.
Proof.
  intros s f.
  rewrite mset.for_all_spec.
  unfold mset.For_all.
  intros x H0.
  unfold mset.for_all.
  rewrite mset.filter_spec in H0.
  destruct H0 as [_ H0].
  auto. unfold respectful;
  unfold Proper; intros; apply f_equal; auto.
  unfold respectful;
  unfold Proper; intros; apply f_equal; auto.
Qed.

Definition remove (x : node) (adj : node_set) : node_set :=
  mset.filter (fun z => negb (node_eqb x z)) adj.

Lemma remove_union :
  forall x s1 s2,
    remove x (mset.union s1 s2) = mset.union (remove x s1) (remove x s2).
Proof.
Admitted.

Fixpoint remove_node (x : node) (g : graph) : graph :=
  match g with
  | Empty => Empty
  | Node y adj g' =>
    if node_eqb x y then remove_node x g'
    else Node y (remove x adj) (remove_node x g')
  end.

Lemma remove_node_neighbors_of :
  forall x y g,
    x <> y -> 
    neighbors_of y (remove_node x g) = remove x (neighbors_of y g).
Proof.
  intros x y g H.
  induction g. simpl. unfold remove.
  
  unfold mset.filter.
  simpl.    
  destruct (mset.filter (fun z : mset.elt => negb (node_eqb x z))).
Admitted.  
  
  

  
(* Old proof for my reference while I go through. *)
(*   intros x y g H; induction g; auto. *)
(*   simpl.  *)
(*   destruct (node_eqb x n) eqn:H2. *)
(*   { rewrite node_eqb_eq in H2; subst n. *)
(*     destruct (node_eqb y x) eqn:H3. *)
(*     { rewrite node_eqb_eq in H3; subst y. *)
(*       exfalso; apply H; auto. } *)
(*     rewrite IHg. *)
(*     destruct (nodelist_contains _ _); auto. *)
(*     simpl. rewrite node_eqb_refl. auto. } *)
(*   destruct (node_eqb y n) eqn:H3. *)
(*   { simpl; rewrite H3; auto. *)
(*     rewrite IHg, remove_app; auto. } *)
(*   simpl. rewrite H3. *)
(*   destruct (nodelist_containsP y (remove x l)). *)
(*   { destruct (nodelist_containsP y l). *)
(*     simpl. rewrite H2. simpl. rewrite IHg. auto. *)
(*     destruct (nodelist_containsP y l). congruence. *)
(*     destruct (nodelist_containsP y (remove x l)); [|congruence]. *)
(*     apply In_remove_weaken in i; contradiction. } *)
(*   destruct (nodelist_containsP y l); auto. *)
(*   simpl. rewrite H2. simpl. rewrite IHg. *)
(*   exfalso. apply H. apply not_In_remove_eq in n0; auto. *)
(* Qed.     *)

Lemma remove_node_contains :
  forall x y g,
    x <> y -> 
    graph_contains y (remove_node x g) = graph_contains y g.
Proof.
  intros x y g H; induction g; auto.
  simpl.
  destruct (node_eqb x n) eqn:H2.
  { rewrite node_eqb_eq in H2; subst n.
    destruct (node_eqb y x) eqn:H2.
    { rewrite node_eqb_eq in H2; subst y.
      exfalso; apply H; auto. }
    auto. }
  destruct (node_eqb y n) eqn:H3.
  rewrite node_eqb_eq in H3; subst n.
  simpl. rewrite node_eqb_refl; auto.
  simpl. rewrite H3. auto.
Qed.  

(* Lemma remove_NoDup x l : *)
(*   NoDup l -> *)
(*   NoDup (removeL x l). *)
(* Proof. *)
(*   induction l; auto. *)
(*   inversion 1; subst. *)
(*   simpl. destruct (negb _). constructor; auto. *)
(*   intros H4. apply In_remove_weaken in H4; contradiction. *)
(*   auto. *)
(* Qed. *)

Lemma In_remove_weaken :
  forall x y (s : node_set),
  mset.In y (remove x s) -> mset.In y s.
Proof.
  intros.
  unfold remove in H.
  apply mset.filter_spec in H.
  destruct H. auto.
  unfold respectful; unfold Proper; auto;
  intros. f_equal. rewrite H1. auto.
Qed.
  
Lemma In_remove_eq :
  forall x y (s : node_set),
  mset.In y (remove x s) -> x <> y.
Proof.
  intros.
  unfold remove in H.
  apply mset.filter_spec in H.
  destruct H. unfold node_eqb in H0.
  apply Pos.eqb_neq.
  apply negb_true_iff in H0. auto.
  unfold respectful. unfold Proper; auto.
  intros. f_equal. rewrite H1. auto.
Qed.

Lemma remove_node_ok :
  forall x g,
    graph_ok g ->
    graph_ok (remove_node x g).
Proof.
  intros x g H.
  induction g.
  { simpl; auto. }
  simpl.
  destruct (node_eqb x n) eqn:H2.
  { rewrite node_eqb_eq in H2.
    subst n.
    inversion H; subst; auto. }
  apply NodeOk.
  { inversion H; subst.
    rewrite remove_node_contains; auto.
    intros H3; subst x. rewrite node_eqb_refl in H2. congruence. }
  { inversion H; subst.
    specialize (IHg H6). 
    apply mset.for_all_spec.
    unfold respectful.
    unfold Proper.
    intros. f_equal. auto.
    rewrite mset.for_all_spec in H5.
    unfold mset.For_all.
    intros.
    rewrite remove_node_contains.
    unfold mset.For_all in H5.
    apply H5. apply  In_remove_weaken in H0. auto.
    apply In_remove_eq in H0. auto.
    unfold respectful.
    unfold Proper.
    intros. f_equal. auto.
  }
  inversion H. auto.
Qed.  

Inductive path (g : graph) : node -> node -> list node -> Prop :=
| start : forall x, graph_Contains x g -> path g x x (x::nil)
| step  : forall x y z l,
            graph_Contains x g ->
            path g y z (y::l) ->
            is_Neighbor x y g ->
              path g x z (x::y::l).

Fixpoint vertices (g : graph) : list node :=
  match g with
  |Empty => nil
  |Node n adj g' => n :: vertices g'
  end.

Fixpoint edges (g : graph) : list (node * node) :=
  match g with
  |Empty => nil
  |Node n adj g' => app (map (fun (elem : node) => (n, elem)) (mset.elements adj)) (edges g')
  end.

Fixpoint isSortedG (g : graph) : bool :=
  match g with
    |Empty => true
    |Node x adj g' => match g' with
                     |Empty => true
                     |Node n adj1 g'' =>  (Pos.ltb x n) && (isSortedG g')(*if negb (Pos.ltb x n) then isSortedG g'
                                        else false*)
                     end
  end.

(** Other potential operators/predicates/definitions: 
    - definition of paths from x <-> y
    - does such a path exist between x <-> y? 
    - graph union 
    - set of vertices 
    - set of edges 
    - induced graph for a given set of vertices 
    - graph isomorphism (predicate over a labeling from 
      one graph to the other)
    - definitions of independent sets, maximal independent sets, etc. 

    Other possible projects: 
    - Is there a graph invariant that implies: 
      "graph isomorphism implies syntactic equality"?
    - Abstract interface over "inductive graphs", together with 
      associated induction principle, plus faster implementation
 *)