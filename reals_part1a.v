Require Import Reals.
Require Import Fourier.
Require Import Omega.
Open Scope R_scope.


(* Below are some Lemmas that help prove results using inequalities *)

Lemma Rplus_lt_compat_dwj: forall a b:R, 0<a -> 0< b -> 0< a+b.
Proof.
intros.
assert (a+0<a+b).
apply Rplus_lt_compat_l.
exact H0.
assert (a+0 = a).
assert (a+0 = 0+a).
apply Rplus_comm.
rewrite H2.
apply Rplus_0_l.
assert (a<a+b).
rewrite <-H2 at 1.
exact H1.
apply (Rlt_trans 0 a (a+b)).
exact H.
exact H3.
Qed.

Lemma Rmult_le_compat_a: forall a b c d e:R, 0<a -> 0<b -> 0<e -> a<=b*c -> b<=d -> c<=e -> a<=d*e.
Proof.
intros.
assert (b*c <= b*e).
apply Rmult_le_compat_l.
left.
exact H0.
exact H4.
assert (b*e <= d*e).
apply Rmult_le_compat_r.
left.
exact H1.
exact H3.
assert (b*c <= d*e).
apply (Rle_trans (b*c) (b*e) (d*e)).
exact H5.
exact H6.
apply (Rle_trans a (b*c) (d*e)).
exact H2.
exact H7.
Qed.


	       
Lemma Rmult_lt_compat_dwj: forall a b:R, 0<a -> 0<b -> 0< a*b.
Proof.
intros.
assert (0<=a).
assert ((0<a)\/(0=a)).
left.
exact H.
unfold Rle.
exact H1.
assert (a*0 = 0).
apply Rmult_0_r.
rewrite <- H2.
apply (Rfourier_lt 0 b a).
exact H0.
exact H.
Qed.

(* The power (x^n) function preserves equality. *)
	      
Theorem Pow_pre_eq: forall n:nat, forall x y:R, 0<y-> y=x -> y^n =x^n.
Proof.
intros.
rewrite H0.
reflexivity.
Qed.


(* The power function preserves <=, i.e., x<= -> x^n <= y^n *)

Theorem Pow_pres_le: forall n:nat, forall x y:R, 0<y-> y<=x -> y^n <=x^n.
Proof.
induction n.
intros.
assert (0<x).
fourier.
simpl.
fourier.
intros.
assert (0<x).
fourier.
assert (y^(S n) = y*y^n).
simpl.
reflexivity.
assert (x^(S n) = x*x^n).
simpl.
reflexivity.
assert (y^n <=x^n).
apply IHn.
exact H.
exact H0.
assert (y*y^n <= x*y^n).
rewrite Rmult_comm.
(* rewrite Rmult_comm at 2. *)
assert (x*y^n = y^n*x).
rewrite Rmult_comm.
reflexivity.
rewrite H5.
assert (0<y^n).
generalize n.
induction n0.
simpl.
fourier.
simpl.
apply Rmult_lt_compat_dwj; auto.
apply (Rfourier_le y x (y^n));auto.
simpl.
assert (x*y^n <= x*x^n).
apply (Rfourier_le (y^n) (x^n) x);auto.
fourier.
Qed.

(* The inverse of the power function preserves <, i.e., x^n < y^n -> x<y *)
  
Theorem Pow_pres_lt_inv: forall n:nat, forall x y:R, 0<x-> 0<y-> y^n<x^n -> y<x.
Proof.
intros.
(* Proof by contradiction. *)
assert ( x<y \/ x=y \/ x>y).
apply Rtotal_order.
destruct H2.
assert (x^n <= y^n).
assert (x<=y).
unfold Rle.
left.
exact H2.
apply Pow_pres_le.
exact H.
exact H3.
fourier.
destruct H2.
assert (y^n=x^n).
apply Pow_pre_eq.
exact H0.
rewrite H2.
auto.
fourier.
exact H2.
Qed.

(*** Exercise 1 ****)	    
(*** Prove that z^(q/r)^r = z^q.    *)
(**** As long as z>0.  ****)
	    
Lemma Pow_simpl :
  forall (z : R) (q r : nat),
    0 < z -> (0 < r)%nat -> (Rpower z (INR q / INR r))^r = z^q.
Proof.
 (*** Fill in proof here. ***)
Admitted.
	    
(******** Exercise #2 ******)
(******** Real root finding lower bound ****************)							      
							      
Theorem Root_finding_l :
  forall x y z q r:nat,
    (0 < x)%nat ->
    (0 < y)%nat ->
    (0 < r)%nat ->
    (0 < z)%nat -> 
    (INR x / INR y)^r < (INR z)^q ->
    (INR x / INR y) < (Rpower (INR z) (INR q / INR r)).
Proof.
  (*** Fill in proof here. ***)
Admitted.

(* Exercise 3 *)
(* Prove that 1.414 < sqrt(2) *)	    
	    
Theorem Sqr_2_lt_1414: 14/10 < Rpower 2 (1/2).
Proof.
  (*** Fill in proof here. ***)
Admitted.
	    
