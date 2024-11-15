(** * Imp: Simple Imperative Programs *)

(** "One man's code is another man's data."
    (Alan Perlis) *)

(** In this chapter, we take a more serious look at how to use Coq to
    study other things.  Our case study is a _simple imperative
    programming language_ called Imp, embodying a tiny core fragment
    of conventional mainstream languages such as C and Java.  Here is
    a familiar mathematical function written in Imp.

       Z := X;
       Y := 1;
       while ~(Z = 0) do
         Y := Y * Z;
         Z := Z - 1
       end
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here's a conventional BNF (Backus-Naur Form) grammar defining 
    the syntax for arithmetic and boolean expressions.

    a := nat
        | a + a
        | a - a
        | a * a

    b := true
        | false
        | a = a
        | a <= a
        | ~ b
        | b && b
*)


Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum (n:nat)
  | APlus (a:aexp) (b:aexp)
  | AMinus (a:aexp) (b:aexp)
  | AMult (a:aexp) (b:aexp).

(* (1*2) + 3 --> concrete syntax *)

(*          
             +
            / \ 
          *    3
        /  \
      1     2

*)
(*  APlus (AMult (ANum 1) (ANum 2)) (ANum 3)--> Abstract syntax*)  

(*

b := true
        | false
        | a = a
        | a <= a
        | ~ b
        | b && b

*)



Inductive bexp: Type :=
  | BTrue
  | BFalse
  | BEq (a1:aexp) (a2:aexp)
  | BLe (a1:aexp) (a2:aexp)
  | BNot (b:bexp)
  | BAnd (b1:bexp) (b2:bexp).

(* 
  ~(1+2 = 6-3)
  BNot (BEq (..) (..))
*)



(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* 2+2 --> 4*)
Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed. 

(** Similarly, evaluating a boolean expression yields a boolean. *)

(*
Inductive bexp: Type :=
  | BTrue
  | BFalse
  | BEq (a1:aexp) (a2:aexp)
  | BLe (a1:aexp) (a2:aexp)
  | BNot (b:bexp)
  | BAnd (b1:bexp) (b2:bexp).

*)
Fixpoint beval (b : bexp) : bool :=
  match b with
   | BTrue => true
   | BFalse => false
   | BEq a1 a2 => (aeval a1) =? (aeval a2)
   | BLe a1 a2 => (aeval a1) <=? (aeval a2)
   | BNot b =>  negb (beval b)
   | BAnd b1 b2 => (beval b1) && (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)
(* We want to rewrite  0 + e to e *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
    | ANum n => a
    | APlus (ANum 0) a2 => optimize_0plus a2
    | APlus a1 (ANum 0) => optimize_0plus a1
    | APlus a1 a2 => APlus (optimize_0plus a1) (optimize_0plus a2)
    | AMinus a1 a2 => AMinus (optimize_0plus a1) (optimize_0plus a2)
    | AMult a1 a2 => AMult (optimize_0plus a1) (optimize_0plus a2)
  end. 


(** 2 + 0 + 0 + 1 = 2 + 1 *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  
Qed.



(*

< relation on nat * nat 


(1,2) < (3,4)

 nat * nat -> nat * nat -> Prop.


*)

(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

(** For example, [==>] is the smallest relation closed under these
    rules:

                    [a ==> m]

                            
                    -----------                     (E_ANum)
                    ANum n ==> n

E_APlus: -> forall (n1 n2:nat)(e1 e2: aexp), 
        aevalR e1 n1 -> 
        aevalR e2 n2 ->
         aevalR (APlus e1 e2) (n1 + n2)

                    e1 ==> n1
                    e2 ==> n2
                --------------------                (E_APlus)
                APlus e1 e2 ==> n1 + n2

                    e1 ==> n1
                    e2 ==> n2
              ---------------------                (E_AMinus)
              AMinus e1 e2 ==> n1 - n2

                      e1 ==> n1
                      e2 ==> n2
                --------------------                (E_AMult)
                AMult e1 e2 ==> n1 * n2


                      e1 ==> n1
                      e2 ==> n2
                      n2 <> 0
                --------------------                (E_AMult)
                ADiv e1 e2 ==> n1 / n2
*)

Module aevalR_first_try.

(* aevalR  is ==> *)

 

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum: forall (n:nat), aevalR (ANum n) n (* ANum n ==> n *)
  | E_APlus: forall (n1 n2:nat)(e1 e2: aexp), 
        (aevalR e1 n1 /\ aevalR e2 n2) ->
         aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (n1 n2:nat)(e1 e2: aexp), 
        (aevalR e1 n1 /\ aevalR e2 n2) ->
         aevalR (APlus e1 e2) (n1 - n2)
  | E_AMult: forall (n1 n2:nat)(e1 e2: aexp), 
        (aevalR e1 n1 /\ aevalR e2 n2) ->
         aevalR (APlus e1 e2) (n1 * n2).

(** It will be convenient to have an infix notation for
    [aevalR].  We'll write [e ==> n] to mean that arithmetic expression
    [e] evaluates to value [n]. *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.


(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)



Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) -> aeval a = n.
Proof.
 intros a n H.
 induction H.
 + simpl. reflexivity.
 + simpl. rewrite IHaevalR1. rewrite IHaevalR2; reflexivity.
 + simpl. rewrite IHaevalR1. rewrite IHaevalR2; reflexivity.
 + simpl. rewrite IHaevalR1. rewrite IHaevalR2; reflexivity.   
Qed.

Theorem aeval_iff_aevalR_automated : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
split.
{
  intros H. induction H; simpl; try rewrite IHaevalR1; 
  try rewrite IHaevalR2; reflexivity.
}
{
  generalize dependent n. induction a; intros; simpl in H; 
  try subst; constructor; try apply IHa1; try apply IHa2; reflexivity.
} 
Qed.

End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations with division: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)


(*
              ??
          ---------------------       [E_ADiv]
            ADiv a1 a2 ===> n3
*)  
(** Extending the definition of [aeval] to handle this new
    operation would not be straightforward (what should we return as
    the result of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR]
    is very easy. *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) : 
      (a1 ==> n1) -> (a2 ==> n2) -> (n2>0) -> ( mult n2 n3 = n1) ->
          (ADiv a1 a2) ==> n3          (* <----- NEW *)
      

where "a '==>' n" := (aevalR a n) : type_scope.

(** Notice that the evaluation relation has now become _partial_:
    There are some inputs for which it simply does not specify an
    output. *)

End aevalR_division.

Module aevalR_extended.

(* ################################################################# *)
(** * Expressions With Variables *)

(*  

  ["a" -> 0 ; "b" -> 0 ; "c" -> 6]

  total_map nat

   BEq (AMult (APlus(AVar("a"),2), APlus(AVar("b"),3)), AVar("c"))
   (a+2) * (b+3) = c

*)








(** Now we return to defining Imp. The next thing we need to do is to
    enrich our arithmetic and boolean expressions with variables. To
    keep things simple, we'll assume that all variables are global and
    that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll reuse maps from the [Maps] chapter, and
    [string]s will be used to represent variables in Imp.

    A _machine state_ (or just _state_) represents the current values
    of _all_ variables at some point in the execution of a program. *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Check (APlus (AId W) (ANum 2)).

(** (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in the chapters
    developed to Imp, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  You do not need to understand
    exactly what these declarations do.  Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Coq to create a new
         "custom grammar" for parsing Imp expressions and
         programs. The first notation declaration after this tells Coq
         that anything between [<{] and [}>] should be parsed using
         the Imp grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) + (Y*3)}>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.


(* ================================================================= *)
(** ** Evaluation *)

(*
   aeval : aexp -> nat
   aeval : aexp -> state -> nat
*)


Definition mystate: state := t_update (t_empty 0) "a" 2.

Fixpoint aeval (st: state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
  

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ 3 + (X * 2) }>
  = 13.
Proof. reflexivity. Qed.

Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip 
        | x := a 
        | c1;c2 
        | if b then c1 else c2 
        | while b do c end 
*)

(** Here is the formal definition of the abstract syntax of
    commands: *)


Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp) (* x := a *)
  | CSeq (c1 c2 : com) (* c1;c2 *)
  | CIf (b : bexp) (c1 c2 : com) (* if b then c1 else c2*)
  | CWhile (b : bexp) (c : com). (* while b do c end *)

(** As for expressions, we can use a few [Notation] declarations to
    make reading and writing Imp programs more convenient. *)

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  <{ while ~(X = 0) do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
<{ while true do skip end }>.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)


(** Here's an attempt at defining an evaluation function for commands,
    omitting the [while] case. *)

(*
Fixpoint ceval_fun_try (st : state) (c : com) : state :=
  match c with
    | <{ skip }> => st 
    | <{ x := a }> => (x !-> (aeval st a); st)
    | <{ c1 ; c2 }> => ceval_fun_try (ceval_fun_try st c1) c2
    | <{ if b then c1 else c2 end}> => 
          if beval st b then ceval_fun_try st c1 
                        else ceval_fun_try st c2 
    | <{ while b do c end }> => 
          if beval st b then ceval_fun_try st <{ c; while b do c end }>
                        else st
    end.
*)
(*
   while b do c end  ==
   if b then c;while b do c else skip end
*)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(*
          ---------------     [E_Skip]
          st ==[skip]==> st

              st' = (x !-> aeval st a; st) 
              --------------------------
              st ==[x:=a]==> st'

                st ==[c1]==> st1
                st1 ==[c2]==> st'
              ------------------------
                st ==[c1;c2] ==> st'


                  (beval st b = true) (st ==[c1]==>st')
                --------------------------------------
                st ==[if b then c1 else c2]==> st'

                beval st b = false  st ==[c2]==>st'
                --------------------------------
                st ==[if b then c1 else c2]==> st'


                beval st b = true   st ==[c]==>st1
                    st1 ==[while b do c end]==> st'
                ----------------------------------
                st ==[while b do c end] ==> st'
*)              


(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

(*
    [st =[ c ]=> st']

        
     ------------------- [E-Skip]
       st =[ skip ]=> st

        st' = (x !-> aeval st a ; st)
     ------------------------------  [E-Asgn]
         st =[ x:=a ]=> st'


        beval st b = true   
        st  =[ c; while b do c end ]=> st'
     ---------------------------------- [E-While-True]    
        st =[ while b do c end ]=> st'


        beval st b = false   
     ---------------------------------- [E-While]    
        st =[ while b do c end ]=> st
*)



Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Theorem program_evals: exists (st':state), 
empty_st =[
  X := 2;
  if (X <= 1)
    then Y := 3
    else Z := 4
  end
]=> st'.
Proof. 
  crush_ceval_theorems.
Qed.

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (st':= (X !-> 2)).
  + apply E_Asgn. simpl. reflexivity.
  + apply E_IfFalse. 
      - simpl. reflexivity.
      - apply E_Asgn. simpl. reflexivity.  
Qed.
(*
  apply E_Seq with (st':=(X !-> 2)).
  + apply E_Asgn. reflexivity.
  + apply E_IfFalse.
    - reflexivity.
    - apply E_Asgn. reflexivity.
Qed.   *)


(* ================================================================= *)
(** ** Determinism of Evaluation *)

Check nat_ind.

(*
  forall P: nat -> Prop, 
      P 0
      -> (forall n, P n -> P (S n))
       -> (forall n, P n)
*)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Check ev_ind.

(*
  forall P: nat -> Prop,
    (P 0)
    -> (forall n, ev n -> P n -> P (S (S n)))
    -> (forall n, ev n -> P n)
*)

Check ceval_ind.


(*
  forall P:nat -> Prop, 
    P 0 -> (forall n. ev n -> P n -> P (S (S n)))
    -> (forall n:nat, ev n -> P n)
  
*)

Check ceval_ind.

(*
    Goal: (*E1*)st =[ c ]=> st1  -> (*E2*)st =[ c ]=> st2 -> st1 = st2.
    

    E1 (st c st1)  P(st c st1)
    P c st st1 = forall st2, st =[ c ]=> st2 -> st1 = st2

    (forall c s st1, st=[c]=st1 -> P c st st1)

    Case E_Skip:
    Goal: forall st, P <skip> st st
    Proof by applying E_Skip.

    Case E_Asgn:
    c = (x:=a)
    Goal: aeval st a = n -> P <x:=a> st (x !->n; st)

    Case E_Seq: 
      E1: st=[c]=> st1   E2: st=[c]=>st2
      c=c1;c2
      E1_1: st=[c1]=>st'  E1_2: st=[c2]=>st'

      *)

(*
  - Determinism: forall x, y1 ,y2. y1 = f(x) /\ y2 = f(x) -> y1 = y2
  - Totality, forall x, exist y. y = f(x)

  forall x, y1 ,y2. R(x,y1) /\ R(x,y2) -> y1 = y2
*)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1.
  + intros. inversion E2. reflexivity.
  + intros. inversion E2. rewrite <- H. rewrite <- H4. reflexivity.
  + intros. Admitted. (* c = c1;c2; E1: st =[c1;c2]=> st1 *) 