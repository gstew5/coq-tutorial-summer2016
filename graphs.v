Set Implicit Arguments.

Require Import ZArith List Bool MSets.

Definition node := positive.
(*Lots of problems with using sets still*)
Module mset := MSetAVL.Make Positive_as_OT.

Notation node_set := mset.t.

Print mset. (*Functions over sets!*)
Check node_set.

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

(** Undirected Graphs *)
Inductive graph : Type :=
| Empty : graph
| Node :
    node -> (** this node's id *)
    node_set(*list node*) -> (** its neighbors *)
    graph -> (** the rest of the graph *)
    graph.
Check graph.
Local Open Scope positive_scope.
Require Import MSets.MSetInterface.

Notation "[ ]" := mset.empty.

Notation "[ elt0 , .. , eltn ]" := (mset.add elt0 .. (mset.add eltn (mset.empty )) .. ) (at level 60, right associativity).
(*Maybe it would also be useful to define some notation or way to print the mset.this output better for a more pleasent view.*)

Example RefSet: node_set :=
  mset.add 4( mset.add 5 ( mset.add 4 mset.empty)).

Compute mset.elements RefSet.
Print RefSet.
Check mset.empty.

Check mset.Raw.Node 2%Z mset.Raw.Leaf 1
      (mset.Raw.Node 1%Z mset.Raw.Leaf 2 mset.Raw.Leaf).

Compute mset.exists_ (fun y  =>  Pos.eqb y 4) RefSet. 

Example ex1 : graph :=
  Node 1 ([2,  3])
       (Node 2 ([3])
             (Node 3 [] Empty)).

Example ex2 : graph :=
  Node 3 ([2,1])
       (Node 2 ([1])
             (Node 1 ([5])
                   (Node 5 [] Empty))).

Check mset.this RefSet.

(** Return the adjacency list associated by graph g
    with node x. *)

Fixpoint adj_of (x : node) (g : graph) : node_set :=
  match g with
  | Empty => mset.empty
  | Node y adj g' =>
    if node_eqb x y then  adj
    else adj_of x g'
  end.

(*Maybe there could be some notation to print mset.this better than the tree form it is in now, but mset.elements makes it readable now.*)
Compute mset.elements (adj_of 3 ex2).

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

(*Did this one semi fast may want to go back and look over it again*)
Fixpoint neighbors_of (x : node) (g : graph) : node_set:=
  match g with
  | Empty => mset.empty
  | Node y adj g' =>
    if node_eqb x y then  mset.union adj (neighbors_of x g')
    else if nodeset_contains x adj then mset.add y (neighbors_of x g')
         else neighbors_of x g'
  end.

(*Changed adj to mset.elements due to adj of graph now being node_set*)

Fixpoint graph_contains (x : node) (g : graph) : bool :=
  match g with
  | Empty => false
  | Node y adj g' =>
    if node_eqb x y then true
    else graph_contains x g'
  end.


Inductive graph_ok : graph -> Prop :=
| EmptyOk : graph_ok Empty
| NodeOk :
    forall (x : node) (adj : node_set(*list node*)) (g : graph),
      graph_contains x g = false ->
      forallb (fun y => graph_contains y g) (mset.elements adj) = true -> (** No self-loops! *)
      graph_ok g ->
      graph_ok (Node x adj g).


Compute mset.elements ([1, 1, 2]).

(* Fixpoint node_nodup (l : list node) : bool := *)
(*   match l with *)
(*   | nil => true *)
(*   | x :: l' => *)
(*     if nodelist_contains x l' then false *)
(*     else node_nodup l' *)
(*   end. *)

(* Lemma node_nodupP : *)
(*   forall l, reflect (NoDup l) (node_nodup l). *)
(* Proof. *)
(*   induction l. *)
(*   constructor. constructor. *)
(*   simpl. destruct (nodelist_containsP a l). *)
(*   constructor. inversion 1; subst. contradiction. *)
(*   destruct (node_nodup l) eqn:H. *)
(*   constructor. constructor; auto. inversion IHl; auto. *)
(*   constructor. inversion 1; subst. inversion IHl; contradiction. *)
(* Qed.   *)

(**Still using forallb to not break proofs below probably should be easy to not convert it to a list I just want to change things incrementally and break as little as I can*)

(** A so-called "smart constructor" for "Node". 
    We enforce the following two properties: 
      1) "x" is not already in the graph; 
      2) every node in "adj" is in the graph. *)

Definition add_node (x : node) (adj : node_set) (g : graph) : graph :=
  if negb (graph_contains x g)
          && negb (nodeset_contains x adj)
          && forallb (fun y => graph_contains y g) (mset.elements adj)
  then Node x adj g
  else g.

(* Definition add_node (x : node) (adj : list node) (g : graph) : graph := *)
(*   if negb (graph_contains x g) *)
(*           && node_nodup adj *)
(*           && forallb (fun y => graph_contains y g) mset.elements adj *)
(*   then Node x adj g *)
(*   else g. *)

(*Slight changes to destructs in this proof, I hope i'm not totally off track doing all this but even if I am it was a good exercise.*)
Lemma add_node_ok :
  forall x adj g,
    graph_ok g ->
    graph_ok (add_node x adj g).
Proof.
  intros x adj g H.
  unfold add_node.
  destruct (negb (graph_contains x g)
                 && negb (nodeset_contains x adj)
                 && forallb (fun y : node => graph_contains y g) (mset.elements adj)) eqn:H2.
  symmetry in H2; apply andb_true_eq in H2; destruct H2.
  apply andb_true_eq in H0. destruct H0.
  apply NodeOk.
  { symmetry in H0; rewrite negb_true_iff in H0; apply H0. }
  { symmetry in H2. generalize H2. destruct (negb (nodeset_contains x adj)). auto. auto.
 }
  { auto. }
  apply H.
Qed.    

Lemma ex1_graph_ok : graph_ok ex1.
Proof.
  unfold ex1; repeat (constructor; auto).
  inversion 1; auto. congruence.
  (*apply NodeOk; auto.
  apply NodeOk; auto.
  apply NodeOk; auto.
  apply EmptyOk.*)
Qed.  

(*Change this to MSet filter sometime*)
Lemma filter_property :
  forall (A : Type) (l : list A) (f : A -> bool),
    forallb f (filter f l) = true.
Proof.
  induction l.
  { simpl. auto. }
  simpl. intros f. destruct (f a) eqn:H.
  { simpl. rewrite H. simpl. apply IHl. }
  apply IHl.
Qed.  

Definition removeS (x : node) (adj : node_set) : node_set :=
  mset.filter (fun z => negb (node_eqb x z)) adj.

Definition remove (x : node) (adj : list node) : list node :=
  filter (fun z => negb (node_eqb x z)) adj.

Lemma remove_app :
  forall x l1 l2,
    remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
Proof.
  unfold remove.
  intros x l1 l2.
  induction l1; auto.
  simpl.
  destruct (negb _); auto.
  simpl. f_equal. auto.
Qed.  

Lemma In_remove_weaken :
  forall x y l,
    In y (remove x l) -> In y l.
Proof.
  induction l; auto.
  simpl. destruct (negb _).
  { inversion 1; subst.
    left; auto.
    right; auto. }
  intros H; right; apply IHl; auto.
Qed.    

Lemma In_remove_neq :
  forall x y l,
    In y (remove x l) -> x <> y.
Proof.
  intros x y.
  induction l; auto.
  simpl. destruct (negb _) eqn:H.
  { assert (H2: x <> a).
    { intros H2. rewrite H2, node_eqb_refl in H; simpl in H; congruence. }
    inversion 1; subst; auto. }
  auto.
Qed.    

Lemma not_In_remove_eq :
  forall x y l,
    In y l -> ~In y (remove x l) -> x = y.
Proof.
  intros x y.
  induction l; auto.
  { simpl. congruence. }
  simpl. intros [H|H].
  { subst y. intros H.
    destruct (negb _) eqn:H2.
    rewrite not_in_cons in H. destruct H. exfalso; apply H; auto.
    destruct (node_eqbP x a); auto. simpl in H2. congruence. }
  destruct (node_eqbP x a); auto.
  unfold negb. rewrite not_in_cons. intros [H1 H2]. auto.
Qed.

Fixpoint remove_nodeS (x : node) (g : graph) : graph :=
  match g with
  | Empty => Empty
  | Node y adj g' =>
    if node_eqb x y then remove_nodeS x g'
    else Node y (removeS x adj) (remove_nodeS x g')
  end.

(*Changing the graph to use node_sets breaks everything in comments here.
*)Fixpoint remove_node (x : node) (g : graph) : graph :=
  match g with
  | Empty => Empty
  | Node y adj g' =>
    if node_eqb x y then remove_node x g'
    else Node y (removeS x adj) (remove_node x g')
  end.

Lemma remove_node_neighbors_of :
  forall x y g,
    x <> y -> 
    neighbors_of y (remove_node x g) = removeS x (neighbors_of y g).
Proof.
  intros x y g H; induction g; auto.
  simpl. 
  destruct (node_eqb x n) eqn:H2.
  { rewrite node_eqb_eq in H2; subst n.
    destruct (node_eqb y x) eqn:H3.
    { rewrite node_eqb_eq in H3; subst y.
      exfalso; apply H; auto. }
    rewrite IHg.
    destruct (nodelist_contains _ _); auto.
    simpl. rewrite node_eqb_refl. auto. }
  destruct (node_eqb y n) eqn:H3.
  { simpl; rewrite H3; auto.
    rewrite IHg, remove_app; auto. }
  simpl. rewrite H3.
  destruct (nodelist_containsP y (remove x l)).
  { destruct (nodelist_containsP y l).
    simpl. rewrite H2. simpl. rewrite IHg. auto.
    destruct (nodelist_containsP y l). congruence.
    destruct (nodelist_containsP y (remove x l)); [|congruence].
    apply In_remove_weaken in i; contradiction. }
  destruct (nodelist_containsP y l); auto.
  simpl. rewrite H2. simpl. rewrite IHg.
  exfalso. apply H. apply not_In_remove_eq in n0; auto.
Qed.    

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

Lemma remove_NoDup x l :
  NoDup l ->
  NoDup (remove x l).
Proof.
  induction l; auto.
  inversion 1; subst.
  simpl. destruct (negb _). constructor; auto.
  intros H4. apply In_remove_weaken in H4; contradiction.
  auto.
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
  { apply remove_NoDup; auto.
    inversion H; auto. }
  { inversion H; subst.
    specialize (IHg H7). clear H7.
    rewrite forallb_forall.
    intros y H7.
    rewrite forallb_forall in H6.
    rewrite remove_node_contains.
    { apply H6.
      apply In_remove_weaken in H7; auto. }
    apply In_remove_neq in H7; auto. }
  inversion H; subst.
  auto.
Qed.      *)

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

Fixpoint Inb (n : node) (l : list node) : bool :=
  match l with
  |nil => false
  | h :: t => if node_eqb n h then true else Inb n t
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