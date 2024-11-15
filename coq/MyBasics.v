(* Functional Programming in Coq *)

Require Import Unicode.Utf8.

(* Days of the week example *)
Inductive day: Type := 
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* next_weekday function *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | _ => monday
  end.

Compute (next_weekday monday).  

(* Compute lets you perform computation and see the result *)

Compute (next_weekday monday).
(* Example *)


Lemma my_random_assertion: (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.
  
Lemma trivial_1: (2 = 2).
Proof. reflexivity. Qed.

(* bool type *)
Inductive bool : Type := 
  | true
  | false.

(* negb definition *)
Definition negb (b:bool) : bool := 
    match b with 
    | true => false
    | false => true
    end.

Notation "¬ x" := (negb x).

Compute (¬ true).

(* orb definition *)
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | true => true
  | false => b2
  end.

(* Write an example to test orb *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity. Qed. 

(* andb definition *)
Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | false => false
  | true => (match b2 with
             | true => true
             | false => false
            end)
  end.

Notation "x ∧ y" := (andb x y).
Notation "x ∨ y" := (orb x y).  

Compute (true ∧ false).


(* Conditional expressions *)
Definition orb' (b1:bool) (b2:bool) : bool := 
  if b1 then true else false.
(* ================================================================= *)
(** ** Types *)

(* Check *)

Check true: bool.

(*
 * Theorem a:T.
 * Proof. ... Qed.
 *)

Check (next_weekday tuesday).

Check negb.

Check bool.

(* ================================================================= *)
(** ** New Types from Old *)
Inductive rgb : Type :=
  | red 
  | green
  | blue.

(* Color type *)
Inductive color : Type :=
  | black
  | white
  | primary (p:rgb).

 (*
  black : color
 *) 
Theorem rgb_equality_check: 
  (primary red = primary red).
Proof. simpl. reflexivity. Qed.

(*
  to_string: Int -> String
*)

(** The definitions of [rgb] and [color] say
    which constructor expressions belong to the sets [rgb] and
    [color]:

    - [red], [green], and [blue] belong to the set [rgb];
    - [black] and [white] belong to the set [color];
    - if [p] is a constructor expression belonging to the set [rgb],
      then [primary p] (pronounced "the constructor [primary] applied
      to the argument [p]") is a constructor expression belonging to
      the set [color]; and
    - constructor expressions formed in these ways are the _only_ ones
      belonging to the sets [rgb] and [color]. *)

(* isRed function *)

(* ================================================================= *)
(** ** Modules *)
Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.


(* ================================================================= *)
(** ** Numbers *)

Module NatPlayground.

(* Define nat *)
Check 0.
Check 23.

(* Denotational semantics *)
(*  ⟦O⟧ = 0 *)
(*  ⟦S n⟧ = 1 + ⟦n⟧ *)

Inductive nat : Type := 
  | O
  | S (n:nat).

Check S (S O).

(*
 * S (S O) == S (S O)
 *  S O = S O
 * O = O
*)

Check S.

Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Compute (pred (S (S (S O)))).
(** The definition of [nat] says how expressions in the set [nat] can be built:

    - the constructor expression [O] belongs to the set [nat];
    - if [n] is a constructor expression belonging to the set [nat],
      then [S n] is also a constructor expression belonging to the set
      [nat]; and
    - constructor expressions formed in these two ways are the only
      ones belonging to the set [nat]. *)


End NatPlayground.

(* We will end NatPlayground to use the built-in definitions of naturals *)
Check O.
Check (S O).
Check 1=2.

Compute (match (S (S O))  with 
        | O => O
        | S n' => n' end).
(* Definitions of Comparison Functions *)

Fixpoint eqb( n m : nat): bool := 
  match n with
  | O => (match m with
          | O => true
          | _ => false
          end)
  | S n' => (match m with
             | O => false 
             | S m' => eqb n' m'
             end)
  end.

Compute (eqb 1 2).

Notation "x == y" := (eqb x y) (at level 70) : nat_scope.

Compute (1 == 2).

Compute (1=2).

Definition p1:Prop := forall (n:nat), n>0.
Definition p2:Prop := forall (n:nat), n>2.
Compute (p1 = p2).


Fixpoint leb (n m : nat) : bool := 
  match n with
   | O => true
   | S n' => (match m with 
                | O => false
                | S m' => leb n' m'
              end)
  end.  
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Fixpoint my_plus (n :nat)(m: nat) : nat :=
  match n with
   | O => m
   | S n' => S (my_plus n' m)
  end.

(* What is the difference between x = y and x =? y? *)
(* They are fundamentally different! *)

(*
  Goal: ∀x. P(x)
  P(y), where y is fresh
*)

(* ################################################################# *)
(** * Proof by Simplification *)
Theorem simpl_theorem: forall n : nat,  0+n = n.
Proof. intros n'. reflexivity. Qed.

(* ################################################################# *)
(** * Proof by Rewriting *)
Theorem plus_id_example : forall n m k:nat,
  n = m ->
  m = k ->
  n + n = k + m.
Proof. 
  intros n m k H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. Admitted.

(* ################################################################# *)
(** * Proof by Case Analysis *)
Theorem plus_1_neq_0 : forall n : nat,
  ((n + 1) == 0 = false).
Proof. 
  intros n.
  destruct n as [|n'] eqn:H.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.
   
Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec. 
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* ################################################################# *)
(** * Proof by Induction *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof. 
  intros n.
  induction n as [|n' IHn].
  + simpl. reflexivity.
  + simpl. rewrite -> IHn. reflexivity.
Qed.  



(* Making local assertions *)
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof. Admitted.




