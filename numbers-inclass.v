(* Programming and Proving with Numbers in Coq 
              Whirlwind Tour, Part I
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Coq's most basic numeric type is [nat], or the type of natural numbers. 
    As we saw last week, naturals are defined in unary notation in Coq, 
    via the following inductive definition. This unary encoding makes 
    defining and reasoning about [nat]-valued functions easy, but is 
    horrendously ineficient! *)

Axiom admit : forall T : Type, T.
Arguments admit [T].

Module MyNat.
  Inductive nat : Type := (* FILL IN HERE*) .

  (** Some notation, for nats 0 through 5: *)

  Local Notation "'0'" := (O).
  Local Notation "'1'" := (S 0).
  Local Notation "'2'" := (S 1).
  Local Notation "'3'" := (S 2).    
  Local Notation "'4'" := (S 3).
  Local Notation "'5'" := (S 4).    
  
  (** Now here's addition on the unary natural numbers. *)

  Fixpoint plus (n m : nat) : nat := admit.
  
  (*Eval compute in plus 3 2.*)
End MyNat.

(** Tactics for Proving [nat] Properties *)

Require Import Arith. (** Loads a bunch of libraries related to [nat] *)

(** Exercise 1: Review *)

Lemma plus_assoc1 :
  forall n m r : nat,
    n + m + r = n + (m + r).
Proof.
Admitted.

Require Import Omega. (* The 'Omega' test 
                         -- a decision procedure for Presburger arithmetic *)

(** Exercise 2: Use 'omega' to prove the following theorem: *)

Lemma plus_assoc2 :
  forall n m r : nat,
    n + m + r = n + (m + r).
Proof.
Admitted.

(** Exercise 3: When 'omega' fails... *)

Lemma mult_assoc1 :
  forall n m r : nat,
    n * m * r = n * (m * r).
Proof.
Admitted.

(** Exercise 4: Update the above lemma statement by replacing 
    [n] and [m] with constants. Does 'omega' work now? *)

Lemma mult_plus_distrib :
  forall n m r : nat,
    n * (m + r) = n * m + n * r.
Proof.
  induction n; auto.
  simpl. intros. rewrite IHn. omega.
Qed.  
  
(** Exercise 5: Prove the following theorem without using 
    'omega' directly (you may use [mult_plus_distrib] above. *)

Lemma mult_assoc2 :
  forall n m r : nat,
    n * m * r = n * (m * r).
Proof.
Admitted.

(** The unary encoding of [nat] is really inefficient. 
    Here's a better binary encoding of the positive integers. *)

Module MyPosZ.
  Inductive positive : Type := admit.

  (** Exercise 6: Define successor on positives. *)
  
  Fixpoint succ (p : positive) : positive := admit.

  (** Some notation, for positives 1 through 5: *)

  Local Notation "'1'" := (xH).
  Local Notation "'2'" := (xO 1).
  Local Notation "'3'" := (xI 1).    
  Local Notation "'4'" := (xO 2).
  Local Notation "'5'" := (xI 2).    

  (*Eval compute in succ 2.
    Eval compute in succ 4.
    Eval compute in succ 1.*)
  
  (** Now we can define [Z] (the positive and negative integers) 
      in terms of [positive] as follows: *)

  Inductive Z : Type := (*FILL IN HERE*).
End MyPosZ.

(** This representation of positives and Z is in fact the same 
    representation Coq's standard library uses. *)

Require Import ZArith.

(* Coq's parser overloads standard notation like '*' to operate 
   on multiple different arithmetic types. We explicitly open 
   'Z_scope' here, to ensure that '*' gets parsed as multiplication 
   on the integers. *)
Open Scope Z_scope. 

(** Exercise 7: Prove the following fact on Z. Here's 
    it's pretty inconvenient to reason directly from the underlying 
    inductive definitions -- much better to make use of available 
    lemmas! Recall "SearchAbout"... *)

Lemma Zfact1 :
  forall p q r s : Z, s * (p * (q + r)) = (s * p * q) + (s * p * r).
Proof.
Admitted.

(* Now prove it using ring... *)

Lemma Zfact2 :
  forall p q r s : Z, s * (p * (q + r)) = (s * p * q) + (s * p * r).
Proof.
Admitted.

(** Exercise 8: *Withouth using ring*, try to prove the following fact 
    about the integers. *)

Lemma Zfact3 :
  forall s t u z : Z, t * (s * u) + z = z + t * u * s.
Proof.
Admitted.

(** Enough for now. In Part II, we'll look at Q, Real, and ways to inject 
    statements over one number type (e.g., nats) into another (e.g., Z). *)







