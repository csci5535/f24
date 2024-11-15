(**From LF Require Export Induction.*)



(* ################################################################# *)
(** * Lists of Numbers *)

Module ListPlayGround.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Check nil.
Check cons.

Check cons 3 (cons 2 nil).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check 1::2::nil.
(* (1:::2):::nil *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)
(** the [repeat] function takes a number [n] and a [count] 
    and returns a list of length [count] in which every element is [n].*)

Fixpoint repeat (n count : nat) : natlist := 
match count with
| O => []
| S count' => n :: (repeat n count')
end.

Compute (repeat 1 4).

(* ----------------------------------------------------------------- *)
(** *** Append *)
(** The [app] function concatenates (i.e., appends) two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | [] => l2
  | x :: xs => x :: (app xs l2)
  end.

(** Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Reasoning About Lists *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem nil_app2 : forall l : natlist,
  l ++ [] = l.
Proof. induction l as [ | x xs IHxs].
- reflexivity.
- simpl. rewrite -> IHxs. reflexivity.
Qed. 

Check natlist. 

End ListPlayGround.
(* ################################################################# *)
(** * Polymorphism *)

(** Polymorphic Lists *)
(* How do you define a polymorphic list? *)
(*
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

*)
Inductive list (X:Type) : Type := 
  | nil
  | cons (x:X) (l : list X).


(* What's the type of list? *)
Check list.

(* Inductive IntOrBool : Type := 
  | Int (n:nat)
  | Bool (b:bool).

Compute (cons IntOrBool (Int 0) (cons IntOrBool (Bool true) (nil IntOrBool))).*)

(* What's the type of nil? *)
Check nil.

(* What's the type of cons? *)
Check cons.

(*
 * class List<T> {
    T data;
    List<T> next;  
   }
  * List<Int> l = new List<Int>(1).
*)

(* You can get the constructors for lists of natural numbers 
   by instantiating the type parameter with nat. *)
Check nil nat.
Check cons nat.

Compute (cons nat 0 (cons nat 1 (nil nat))).

(* Polymorphic Repeat: We get polymorphic repeat function 
   by parameterizing it's definition over a type. *)
Fixpoint repeat (T:Type) (x:T) (count:nat) : list T :=
  match count with
  | O => nil T
  | S count' => cons T x (repeat T x count')
  end.


Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference and Type Argument Synthesis *)

Fixpoint repeat2 T x count : list T :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat2 T x count')
  end.

Definition list123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {T}.

Definition list123_simple := 
  cons 1 (cons 2 (cons 3 (nil))).

Compute (repeat 1 4).

(* We can make the type argument to repeat implicit *by definition*. *)
Fixpoint repeat3 {T:Type} (x:T) (count:nat) : list T :=
  match count with
  | O => nil
  | S count' => cons x (repeat3 x count')
  end.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

Fixpoint app {X} l1 l2 : list X.

Fixpoint rev {X:Type} (l:list X) : list X.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(* The following should throw an error *)
Fail Definition mynil := nil.

(* ================================================================= *)
(** ** Polymorphic Pairs *)


Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* Write a zip function that zips up two lists.
 *)
Fixpoint zip {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (zip tx ty)
  end.

  