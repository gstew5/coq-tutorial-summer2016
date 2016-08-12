Set Implicit Arguments.

Require Import ZArith List Bool.
Require Import MSets MSetFacts.

Module Type Graph (Node : UsualOrderedType).
  (* We want a way to talk about edges *)
  Module NodePair := PairOrderedType Node Node.

  (* Build necessary modules *)
  Module mset := MSetAVL.Make Node.
  Module msetPair := MSetAVL.Make NodePair.
  Module mset_facts := WFacts (mset).
  Module msetPair_facts := WFacts (msetPair).
  Module mset_prop := WProperties (mset).
  Module msetPair_prop := WProperties (msetPair).

  (* Provide definitions for containers wrt to above modules *)
  Definition node := Node.t.
  Definition nodePair := NodePair.t.

  Definition node_set := mset.t.
  Definition node_setPair := msetPair.t.

  (* Some notation for commonly used predicates *)
  Notation In_ns := mset.In.
  Notation In_nsp := msetPair.In.

  (* The type of graphs *)
  Parameter t : Type.

  (* An empty graph *)
  Parameter empty : t.

  (* Functions for the addition/removal of edges and vertices *)
  Parameter add_vertex : t -> node -> t.
  Parameter add_edge : t -> (node*node) -> t.
  Parameter remove_vertex : t -> node -> t.
  Parameter remove_edge : t -> (node*node) -> t.

  (* Functions for finding edges/vertices of a graph *)
  Parameter vertices : t -> node_set.
  Parameter edges : t -> node_setPair.

  Parameter is_vertex : t -> node -> bool.
  Parameter is_edge : t -> (node*node) -> bool.
  
  Parameter neighborhood : t -> node -> node_set.

  (** empty *)
  Axiom empty_vertices : vertices empty = mset.empty.
  Axiom empty_edges : edges empty = msetPair.empty.  

  (** add *)
  Axiom add_vertices :
    forall (x : node) g,
      In_ns x (vertices (add_vertex g x)).
  Axiom add_edges :
    forall (e : node*node) g,
      In_ns (fst e) (vertices g) ->
      In_ns (snd e) (vertices g)->       
      In_nsp e (edges (add_edge g e)).
  Axiom add_vertices_other :
    forall (x y : node) g,
      x <> y -> In_ns y (vertices g) <-> In_ns y (vertices (add_vertex g x)).
  Axiom add_edges_other :
    forall (e1 e2 : node*node) g,
      e1 <> e2 -> In_nsp e2 (edges g) <-> In_nsp e2 (edges (add_edge g e1)).

  (** remove *)
  Axiom remove_vertices :
    forall (x : node) g,
      ~In_ns x (vertices (remove_vertex g x)).
  Axiom remove_edges :
    forall (e : node*node) g,
      ~In_nsp e (edges (remove_edge g e)).
  (* Removal of vertices, ensures that the edge list remains valid *)
  Axiom remove_vertices_edges_l :
    forall (x1 : node) g,
      forall (x2 : node), ~ In_nsp (x1,x2) (edges (remove_vertex g x1)).
  Axiom remove_vertices_edges_r :
    forall (x1 : node) g,
      forall (x2 : node), ~ In_nsp (x2,x1) (edges (remove_vertex g x1)).
  Axiom remove_vertices_other :
    forall (x y : node) g,
      x <> y -> In_ns y (vertices g) <-> In_ns y (vertices (remove_vertex g x)).
  Axiom remove_edges_other :
    forall (e1 e2 : node*node) g,
      e1 <> e2 -> In_nsp e2 (edges g) <-> In_nsp e2 (edges (remove_edge g e1)).

  (** other properties *)
  Axiom is_vertex_vertices :
    forall x g,
      In_ns x (vertices g) <-> is_vertex g x = true.
  Axiom is_edge_edges :
    forall e g,
      In_nsp e (edges g) <-> is_edge g e = true.
  Axiom neighborhood_prop :
    forall x y g,
      In_ns y (neighborhood g x) <-> In_nsp (x,y) (edges g).
  Axiom edges_proper_l :
    forall x g,
      In_nsp x (edges g) -> In_ns (fst x) (vertices g).
  Axiom edges_proper_r :
    forall x g,
      In_nsp x (edges g) -> In_ns (snd x) (vertices g).
  Lemma edges_proper :
    forall x g,
      In_nsp x (edges g) ->
        In_ns (fst x) (vertices g) /\ In_ns (snd x) (vertices g).
  Proof.
    intros.
    split;
    [apply edges_proper_l | apply edges_proper_r];
    auto.
  Qed.


  (** Equality **)
  Definition Equal (g1 g2 : t) :=
    mset.Equal (vertices g1) (vertices g2) /\
    msetPair.Equal (edges g1) (edges g2).
  Definition equal (g1 g2 : t) :=
    (mset.equal (vertices g1) (vertices g2)) &&
    (msetPair.equal (edges g1) (edges g2)).
  Lemma Equal_refl : forall g, Equal g g.
  Proof.
  Admitted.
  Lemma Equal_symm :
    forall g1 g2, Equal g1 g2 -> Equal g2 g1.
  Proof.
  Admitted.
  Lemma Equal_trans :
    forall g1 g2 g3, Equal g1 g2 -> Equal g2 g3 -> Equal g1 g3.
  Proof.
  Admitted.

  (** Subgraphs **)
  Definition Subgraph (g1 g2 : t) :=
    mset.Subset (vertices g1) (vertices g2) /\
    msetPair.Subset (edges g1) (edges g2).

  Section GraphInduction.
(** We don't know how these graphs are implemented underneath
    the module, and this can make induction principles too
    restricitive. One way to work around this would be
    to require the user to provide their own induction
    principles as axioms to the interface. But, this
    can be burdensome, and may require the introduction
    of axioms like Proof Irrelevance to work around
    (ex. Sam's implementation of graphs for MIS
    and Gordon's instance for list sets).

    But, many of our propositions regarding graphs don't
    care about their underlying construction. Instead,
    we only care about relations between the set of edges
    and the set of vertices. In many (all?) cases, these
    relations should be preserved under the Equal relation
    described above. In this section, we capitalize on this
    fact to construct an induction principle for
    functions/properties which are preserved under this
    Equality relation, tenatively deemed 'respectful'.

    This has a number of benefits:
      1.) Decreased burden of proof for the interface user.
            The user no longer has to generate their own induction
            principles.
      2.) Avoidance of additional axioms such as proof
            irrelevance.
      3.) Technique should be easily extendable to
            other (setoid?) types.

    The general process for the derivation of the first induction
    principle (ind1) looks like this:
      
      1.) Given an arbitrary graph, rebuild it up to
            Equality using 'rebuild_graph'
      2.) This rebuilt graph is made using the
            only empty, add_vertices and add_edges
            and is thus a memeber of constructed_t.
      3.) We can use the induction/recursion principle of
            constructed_t to destruct the rebuilt graph
            into cases in which the induction hypotheses
            are applicable.
      4.) Since the operation is respectful, we can use this
            output for the rebuilt graph to produce a
            an output for the input graph.
  *)

  (** Functions for a 'cannonical' construction
        of equivalent graphs **)
  Definition const_vertices (v : node_set) : t :=
    mset.fold (fun elt subg => add_vertex subg elt) v empty.

  Definition const_edges (v : node_setPair) (g : t) :=
    msetPair.fold (fun elt subg => add_edge subg elt) v g.
  
  Definition rebuild_graph : t -> t :=
    fun g => const_edges (edges g) (const_vertices (vertices g)).

  (** Proofs that these functions result in equivalent graphs **)
  Lemma const_vertices_preservation g :
    mset.Equal (vertices g) (vertices (const_vertices (vertices g))).
  Proof.
    unfold const_vertices.
    apply mset_prop.fold_rec;
    intros.
    {
      apply mset_prop.empty_is_empty_1 in H.
      apply (mset_prop.equal_trans H).
      rewrite empty_vertices.
      apply mset_prop.equal_refl.
    }
    {
      apply mset_prop.Add_Equal in H1.
      apply (mset_prop.equal_trans H1).
      split; case (Node.eq_dec x a0); intros.
      {
        subst. apply add_vertices.
      }
      {
        apply add_vertices_other; auto.
        apply H2; auto.
        apply mset_prop.Dec.F.add_neq_iff in H3; auto.
      }
      {
        subst. apply mset_prop.Dec.F.add_1; auto.
      }
      {
        apply mset_prop.Dec.F.add_2.
        apply H2.
        apply add_vertices_other in H3; auto.
      }
    }
  Qed.

  Lemma const_edges_preservation_edges
    v g
    (H0 : forall e, msetPair.In e v -> mset.In (fst e) (vertices g))
    (H1 : forall e, msetPair.In e v -> mset.In (snd e) (vertices g))
    : msetPair.Equal (msetPair.union v (edges g)) (edges (const_edges v g)).
  Proof.
    unfold const_edges.
    apply msetPair_prop.fold_rec; intros.
    {
      apply msetPair_prop.empty_union_1; auto.
    }
    {
      
    }
  Admitted.

  Lemma const_edges_preservation_vertices v g :
    mset.Equal (vertices g) (vertices (const_edges v g)).
  Proof.
  Admitted.     

  Lemma rebuild_graph_spec :
    forall t, Equal (rebuild_graph t) t.
  Proof.
    intros t.
    constructor;
    unfold rebuild_graph.
  Admitted.

  (** An inductive construction for graphs
        wrt. functions avilable to the interface **)
  Inductive constructed_t : t -> Type :=
  | const_empty : constructed_t empty
  | const_vert : forall g x,
      constructed_t g -> constructed_t (add_vertex g x)
  | const_edge : forall g x,
      constructed_t g -> constructed_t (add_edge g x).

  (** A proof that rebuild builds graphs, according to the interfaced
        add/remove functions. **)
  Lemma rebuild_is_constructed : forall g, constructed_t (rebuild_graph g).
  Proof.
    intros g.
    unfold rebuild_graph.
    (* Use set_induction from MSetProperties? *)
  Admitted.
  
  (** The definition of respectful operations **)
  Definition respectful (P : t -> Type) :=
    forall t1 t2, Equal t1 t2 -> P t1 -> P t2.

  (** With all of that out of the way, we can actually prove
        an induction principle **)  
  Lemma ind1 (P : t -> Type) (H0 : respectful P) :
    P empty -> 
    (forall x g, P g -> P (add_vertex g x)) ->
    (forall x g, P g -> P (add_edge g x)) ->
    forall g, P g.
  Proof.
    intros.
    unfold respectful in H0.
    apply H0 with (t1 := rebuild_graph g).
    apply rebuild_graph_spec.
    assert (H3 : constructed_t (rebuild_graph g))
      by apply rebuild_is_constructed.
    induction H3; auto.
  Qed.

  (** Additional Induction Lemmas **)
  (* 
    1. Induction over subgraphs
      - show that some subgraph is built using constructed_t.
    2. Induction over number of vertices.
    3. Strong induction wrt. number of vertices.
    ... ?
 *)
 End GraphInduction.

End Graph.