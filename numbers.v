(* Programming and Proving with Numbers in Coq 
              Whirlwind Tour, Part I
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(** Coq's most basic numeric type is [nat], or the type of natural numbers. 
    As we saw last week, naturals are defined in unary notation in Coq, 
    via the following inductive definition. This unary encoding makes 
    defining and reasoning about [nat]-valued functions easy, but is 
    horrendously ineficient! *)

Module MyNat.
  Inductive nat : Type :=
  | O : nat (** zero *)
  | S : nat -> nat. (** successor *)

  (** Some notation, for nats 0 through 5: *)

  Local Notation "'0'" := (O).
  Local Notation "'1'" := (S 0).
  Local Notation "'2'" := (S 1).
  Local Notation "'3'" := (S 2).    
  Local Notation "'4'" := (S 3).
  Local Notation "'5'" := (S 4).    
  
  (** Now here's addition on the unary natural numbers. *)

  Fixpoint plus (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n' => S (plus n' m)
    end.

  Eval compute in plus 3 2.
End MyNat.

(** Tactics for Proving [nat] Properties *)

Require Import Arith. (** Loads a bunch of libraries related to [nat] *)

(** Exercise 1: Review *)

Lemma plus_assoc1 :
  forall n m r : nat,
    n + m + r = n + (m + r).
Proof.
  induction n.
  { simpl. auto. }
  intros. simpl. rewrite IHn. auto.
Qed.

Require Import Omega. (* The 'Omega' test 
                         -- a decision procedure for Presburger arithmetic *)

(** Exercise 2: Use 'omega' to prove the following theorem: *)

Lemma plus_assoc2 :
  forall n m r : nat,
    n + m + r = n + (m + r).
Proof.
  intros.
  omega.
Qed.

(** Exercise 3: When 'omega' fails... *)

Lemma mult_assoc1 :
  forall n m r : nat,
    n * m * r = n * (m * r).
Proof.
  intros.
  (* omega fails, why? *)
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
  induction n; auto.
  simpl. intros. rewrite <-IHn.
  rewrite mult_comm.
  rewrite mult_plus_distrib.
  rewrite mult_comm.
  rewrite (mult_comm r (n * m)).
  auto.
Qed.

(** The unary encoding of [nat] is really inefficient. 
    Here's a better binary encoding of the positive integers. *)

Module MyPosZ.
  Inductive positive : Type :=
  | xI : positive -> positive (* Multiply by two and add 1 *)
  | xO : positive -> positive (* Multiply by two and add 0 *)
  | xH : positive. (* The positive '1' *)

  (** Exercise 6: Define successor on positives. *)
  
  Fixpoint succ (p : positive) : positive :=
    match p with
    | xI p' => xO (succ p')
    | xO p' => xI p'
    | xH => xO xH
    end.
  
  (** Some notation, for positives 1 through 5: *)

  Local Notation "'1'" := (xH).
  Local Notation "'2'" := (xO 1).
  Local Notation "'3'" := (xI 1).    
  Local Notation "'4'" := (xO 2).
  Local Notation "'5'" := (xI 2).    

  Eval compute in succ 2.
  Eval compute in succ 4.
  Eval compute in succ 1.

  (** The successor function defined above works correctly 
      on a few test cases. But that doesn't imply that successor
      works correctly in *all* cases. To be certain, we'll 
      have to prove it!

      Define the following interpretation function from 
      positives to nats:
 
      [[ . ]] : positive -> nat
      [[ xI p' ]] = 2 * [[ p' ]] + 1
      [[ xO p' ]] = 2 * [[ p' ]]
      [[ xH ]]    = 1

      Our correctness property will be the following theorem:            

      Theorem: forall p, [[ succ p ]] = [[ p ]] + 1.

      Case xI: 
      By IH, [[succ p']] = [[p']] + 1.
      N.T.S. [[p'~1]] + 1   = [[(succ p')~0]]
           = 2 * [[p']] + 2 = 2 * [[succ p']]
                            = 2 * ([[p']] + 1)    By IH
                            = 2 * [[ p' ]] + 2    []

      Case xO: 
      N.T.S. [[p'~0]] + 1   = [[p'~1]].
           = 2 * [[p']] + 1 = 2 * [[p']] + 1      []

      Case xH:
      N.T.S. [[xH]] + 1 = [[xO xH]]
           = 1 + 1      = 2 * [[xH]]
                        = 2 * 1 = 2               []
    *)

  Fixpoint interp (p : positive) : nat :=
    match p with
    | xH => 1
    | xO p' => 2 * interp p'
    | xI p' => 2 * interp p' + 1
    end.

  Lemma pos_succ_correct :
    forall p : positive,
      interp p + 1 = interp (succ p).
  Proof.
    induction p.
    { unfold succ. fold succ.
      unfold interp. fold interp.
      rewrite <-!IHp. omega.
    }
    { simpl. rewrite <-!plus_n_O. auto. }
    auto.
  Qed.    
  
  (** HOMEWORK Exercise 6b: Define predecessor on positives. 
      HINT: Define [pred 1 = 1]. You may find an auxiliary 
      function useful. Look in the standard library if you get 
      stuck. *)
  
  (** Now we can define [Z] (the positive and negative integers) 
      in terms of [positive] as follows: *)

  Inductive Z : Type :=
  | Z0 : Z (** Zero *)
  | Zpos : positive -> Z (* Positive Zs *)
  | Zneg : positive -> Z. (* Negative Zs *)
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
  intros p q r s.
  rewrite Z.mul_assoc.
  rewrite Z.mul_add_distr_l; auto.
Qed.  

Lemma Zfact2 :
  forall p q r s : Z, s * (p * (q + r)) = (s * p * q) + (s * p * r).
Proof.
  intros p q r s.
  ring. (*Yay!*)
  (* See [https://coq.inria.fr/refman/Reference-Manual028.html] for details *)
Qed.

(** Exercise 8: *Without using ring*, try to prove the following fact 
    about the integers. *)

Lemma Zfact3 :
  forall s t u z : Z, t * (s * u) + z = z + t * u * s.
Proof.
  intros s t u z.
  rewrite Z.add_comm.
  rewrite (Z.mul_comm s u).
  rewrite Z.mul_assoc.
  auto.
Qed.

(** Let's compose some of the pieces we've defined above to build 
    a new datatype for rationals, Q: *)

Module MyQ.
  Record Q : Type :=
    QMake { QNum : Z;
            QDen : positive }.

  (** The 'Record' declaration above basically does the following: 

    1. Define an 

       Inductive Q : Type := 
         QMake : Z -> positive -> Q

    2. Define 'projections', of the form:

       Definition QNum (q : Q) : Z := 
         match q with 
           | QMake n d => n
         end. 

       Definition QDen (q : Q) : positive := 
         match q with 
           | QMake n d => d
         end. 
   *)

  (** Here's addition on rationals. Note that we don't 
      maintain irreducibility. *)
  
  Definition Qplus (x y : Q) :=
    QMake (QNum x * Zpos (QDen y) + QNum y * Zpos (QDen x))
          (Pos.mul (QDen x) (QDen y)).

  Definition three_fourths : Q := QMake 3 4.

  Eval compute in Qplus three_fourths three_fourths.

  (** Exercise 9: Define a variant of the 'Q' type above
      such that the fraction Qnum / Qden is always in 
      reduced form (Qnum and Qden have no common divisors). To 
      do so, you'll need to add a third term to the record 
      containing a proof of the appropriate arithmetic fact. *)

  Record Q' : Type :=
    QMake' { QNum' : Z;
             QDen' : positive;
             invariant : (* FILL IN HERE *) False }.

  (* Define equality on "reduced Q" as follows: *)

  Definition Qeq (x y : Q') :=
    QNum' x * Zpos (QDen' y) = QNum' y * Zpos (QDen' x).

  (* If you've correctly defined 'reducedQ', you should be able 
     to prove the following lemma: *)

  Lemma Qeq_eq :
    forall x y : Q', Qeq x y -> x = y.
  Proof.
    (** CHALLENGE Exercise: Prove this! *)
  Admitted.    
End MyQ.  

(** We don't need to define our own rationals, of course. Coq's 
    standard library builds them in: *)

Require Import QArith.

Lemma Qfact1 :
  forall x y z : Q,
    z * (x + y) == z * x + z * y. (* To the left, == is 'Qeq'. *)
Proof.
  intros x y z.
  (* "SearchAbout Qplus Qmult" yields lemma "Qmult_plus_distr_r". *)
  apply Qmult_plus_distr_r.
Qed.  

(** Enough for now. In Part II, we'll look Real, plus ways to inject 
    statements over one number type (e.g., nats) into another (e.g., Z). *)







