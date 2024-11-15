(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Inductive list (A: Type) : Type :=
  | nil: list A
  | cons (x:A) (xs: list A) : list A.

Check list.
Check cons.
Check (nil nat).

Definition list1: list nat := cons nat 1 (nil nat).

Arguments nil {A}.
Arguments cons {A}.

Definition list0: list nat := nil.

Definition list2 := cons 1 (cons 2 nil).

Print list2.

Notation "[ ]" := nil.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition list2' := 1::2::3::[].

Definition list3 := [1; 2; 3].
Definition list4 := [4; 5; 6; 7].

Print list3.

(* ----------------------------------------------------------------- *)
(** *** Append *)
(** The [app] function concatenates (i.e., appends) two lists. *)

Fixpoint app {A: Type} (l1: list A) (l2: list A): list A := 
  match l1 with
  | nil => l2
  | cons x xs => x::(app xs l2)
  end. 

(** Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(*
 list5 = app list3 list4.
*)
Definition list5 := list3 ++ list4.
Compute list5.

Print nat_ind.

Print list_ind.


Theorem app_is_associative: forall (X:Type) (l1 l2 l3: list X),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof. 
  intros X l1 l2 l3.
  induction l1 as [|x xs IHxs].
  {
    simpl. reflexivity.    
  }
  {
    simpl. rewrite -> IHxs. reflexivity.
  }
Qed.

(**largest_common_set: list nat -> list nat -> (bool * list nat)*)
(* Pairs, i.e., product of two types *)

Inductive prod (X:Type)(Y:Type) := 
  | pair (x:X) (y:Y).

Arguments pair {X}{Y}.

Notation "( x , y )" := (pair x y) (at level 60).
Notation "X * Y " := (prod X Y) : type_scope.

Definition simple_pair: nat * bool := ( 1 , true ).

Inductive option (A:Type): Type :=
 | none
 | some (v: A).

Arguments none {A}.
Arguments some {A}.

Fixpoint lookup_non_zero (l: list nat) : option nat :=
  match l with
   | [] => none
   | cons (S n) xs => some (S n)
   | cons 0 xs => lookup_non_zero xs 
  end.

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Check @nil.
Check @cons.

Definition doit3times {X : Type} (f: X -> X) (x:X) : X :=
  f (f (f x)).

(*
 * doit3times: forall X:Type, (X -> X) -> X -> X
*) 

Check doit3times.

Check @doit3times.

Definition minustwo (x:nat) : nat := x - 2.

Compute doit3times minustwo 9.

Definition square (x:nat) : nat := x * x.

Compute doit3times square 2.

Example test_doit3times: doit3times minustwo 9 = 3.
(* minustwo (minustwo (minustwo 9) )*)
Proof. reflexivity. Qed.

(* Anonymous functions *)

(* List filter with an anon function *)

Fixpoint filter {A: Type} (f : A -> bool) 
  (l1: list A) : list A :=
match l1 with
  | [] => []
  | x::xs => if f x then x::(filter f xs)
                         else filter f xs
end.

(* List map, List fold *)
(* Curr*)
