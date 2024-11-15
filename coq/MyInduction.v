From LF Require Export Basics.
Require Import Psatz.

(*
 * Let's prove that n + 0 = n for all n:nat.
 *)
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof. intros n. induction n as [|n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.  

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. intros n m. induction n as [ | n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Check add_0_r.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. Admitted. (* HW1 *)
(* ################################################################# *)
(** * Proofs Within Proofs *)

Lemma trivial_2: forall n:nat, 0 + (0 +n) = n.
Proof.
  intros n.
  assert(H: forall x:nat, 0+x = x).
  {
    intros. simpl. reflexivity.
  }
  Admitted.

Theorem mult_0_plus' : forall n m k: nat,
  ((0 + n) * m) *k   = m * (0+n) * k.
Proof.
  intros n m k. 
  assert(H: 0+n = n).
  {
    simpl. reflexivity.
  }
  Admitted.  
  
(*
  ((n + 1) + 1) = n + 2
 *)  
Theorem hamed: forall n:nat, n + 1 + 1 = n + 2.
Proof.
  intros n.
  lia.
Qed.

Theorem hamed2: forall n m:nat, 
  n < m ->
  exists k:nat, m = n + k.
Proof.
  intros.
  exists (m - n).
  lia.
Qed.


Module ListPlayGround.

Inductive NatList : Type := 
  | Nil : NatList
  | Cons: nat -> NatList -> NatList.

Check Cons.
Check NatList.

End ListPlayGround.

Module PolyListPlayGround.

Inductive List (X:Type): Type := 
  | Nil : List X
  | Cons: X -> List X -> List X.

Check List.




(* ################################################################# *)
(** * TODO for you: Please practice Induction.v *)

(* ################################################################# *)
(** * Inductive Data Structures: Working with structured data *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(** This declaration can be read: "The one and only way to
    construct a pair of numbers of type natprod is by applying 
    the constructor [pair] to two arguments of type [nat]." *)

Check (pair 3 5) : natprod.

(** Here are simple functions for extracting the first and
    second components of a pair. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Convenient notation for pairs. *)

Notation "( x , y )" := (pair x y).

(** The new notation can be used both in expressions and in pattern
    matches. *)

Compute (fst (3,5)).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.


Theorem surjective_pairing : forall (p : natprod),
p = (fst p, snd p).
Proof. intros p. induction p.
simpl. reflexivity.
Qed.

(* ################################################################# *)
(** * Lists of Numbers *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Check nil.

Check cons 3 (cons 2 nil).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check 1::2::nil.