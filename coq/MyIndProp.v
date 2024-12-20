Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Fixpoint is_even (n:nat) : bool := 
  match n with
   | 0 => true
   | 1 => false
   | S (S n') => is_even n'  
  end.


Definition Even1 x := exists n : nat, x = double n.
Definition Even2 x := is_even x = true.

(*

  ev n : natural number n is even
   
    
    ------  [ev_0]
     ev 0

      ev n
  -----------  [ev_ss]
   ev (S (S n))

*)
    
(*   ---- [ev_0]
      ev 0 
     -----  [ev_ss] 
      ev 2
    -------- [ev_ss]
      ev 4
*)

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductively defined propositions_. *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true], or

      (2) [exists k, n = double k].

    A third possibility that we'll explore here is to say that [n] is
    even if we can _establish_ its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation.  (We'll
    use [ev] for the name of this property, since [even] is already
    used.)

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(** Each of the textual rules that we started with is
    reformatted here as an inference rule; the intended reading is
    that, if the _premises_ above the line all hold, then the
    _conclusion_ below the line follows.  For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also
    does.  If a rule has no premises above the line, then its
    conclusion holds unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)


Inductive my_nat : Type := 
  | my_O: my_nat
  | my_S (n:nat)  : my_nat.

Inductive my_list (X:Type) : Type :=
  | Nil : my_list X
  | Cons: X -> my_list X -> my_list X.

Check my_list.

Inductive ev : nat -> Prop := 
  | ev_0: ev 0
  | ev_SS: forall (n:nat), ev n -> ev (S (S n)).


Check ev_0.

Check ev_SS.

Definition nat_add2 (x:nat) : nat := x+2.

Check nat_add2.

(*
   ev_SS: (n : nat) -> ev n -> ev (S (S n))

   (ev_SS 4) : ev 4 -> ev (S (S 4))
*)



Theorem zero_is_even: ev 0.
Proof.
  apply ev_0.
Qed.

Theorem four_is_even: ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print nat_ind. 

Print ev_ind.




    
(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, which amounts to reasoning about how it
    could have been built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n H.
  destruct H.
  + left. reflexivity.
  + right. exists n. split.
   - reflexivity.
   - assumption.
Qed.


Theorem ev_double :
  forall (n: nat), ev n -> ev (double n).
Proof.
  intros n H.
  induction H as [| n' Hn' IHn'].
  + simpl. apply ev_0.
  + simpl. apply ev_SS. apply ev_SS. assumption.
Qed.   

Print ev.


Definition law_of_excluded_middle: Prop := forall (P : Prop), P \/ ~P.

(*
Theorem lem: law_of_excluded_middle.
Proof.
  unfold law_of_excluded_middle.
  intros.
*)

(**
Theorem p_q_rational: Exist irrational numbers P and Q, s.t P^Q is a rational number. 
Proof. 
    Consider R = (√2)^(√2).
    Two cases:
    * Case 1: R is rational. 
       P = Q = √2. Done. 
    * Case 2: R is irrational.
      Consider R^√2 = (√2)^(√2)^^√2 = (√2)^2  = 2.
  Qed.
*)


(*

compute_prime_factors: {y: nat} -> {x: list nat |
                                      every x[i] is prime /\ 
                                      y = Πx_i /\ x != []}


Theorem prime_factors_exist: forall y:nat, exists l: list nat, 
  ~(l = []) /\ every x[i] is prime /\ 
                                      y = Πx_i /\ x != []}

*)

(*
  Algorithms are computational content of proofs.
*)





(* ==>
  Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS : forall n, ev n -> ev (S (S n)).
*)

(** Suppose we introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can say "is a proof of."  For example,
    the second line in the definition of [ev] declares that [ev_0 : ev
    0].  Instead of "[ev_0] has type [ev 0]," we can say that "[ev_0]
    is a proof of [ev 0]." *)

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  data values

    See [Wadler 2015] (in Bib.v) for a brief history and up-to-date
    exposition. *)

(** Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)

Check ev_SS.

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)

(** Now let's look again at a previous proof involving [ev]. *)


(**
  (ev_SS 4) : ev 4 -> ev (S (S 4))
*)

(*
n: nat
*)


Theorem my_list2: list nat.
apply [ ]. Show Proof. Qed.


Check ev_SS.

Check 2:nat.


Definition my_two: nat := 2.
Check my_two: nat.
Print my_two.

(** * Proof Scripts *)
(* In the following we writing a "script" to build
   a proof object for ev 4 *)


Definition ev_4_po: ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS. 
  Show Proof.
  apply ev_0. 
  Show Proof.
  Qed.

Print ev_4_po.
Print ev_4.

Definition ev_4' : ev 4 := 
  (ev_SS 2 (ev_SS 0 ev_0)).

(** As with ordinary data values and functions, we can use the [Print]
    command to see the _proof object_ that results from this proof
    script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print ev_4'.

(** Indeed, we can also write down this proof object directly,
    without the need for a separate proof script: *)

Check (ev_SS 2 (ev_SS 0 ev_0)).

(** The expression [ev_SS 2 (ev_SS 0 ev_0)] can be thought of as
    instantiating the parameterized constructor [ev_SS] with the
    specific arguments [2] and [0] plus the corresponding proof
    objects for its premises [ev 2] and [ev 0].  Alternatively, we can
    think of [ev_SS] as a primitive "evidence constructor" that, when
    applied to a particular number, wants to be further applied to
    evidence that this number is even; its type,

      forall n, ev n -> ev (S (S n)),

    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] expresses the fact that the constructor
    [nil] can be thought of as a function from types to empty lists
    with elements of that type. *)



Theorem ev_4'': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.



(* ################################################################# *)
(** * Quantifiers, Implications, Functions *)

(** In Coq's computational universe (where data structures and
    programs live), there are two sorts of values that have arrows in
    their types: _constructors_ introduced by [Inductive]ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]ly defined propositions,
    and... functions! *)

(** For example, consider this statement: *)

From Coq Require Import Arith.


Definition is_eveen : nat -> Datatypes.bool := 
  fun x => x mod 2 =? 0.

(*
  (n:nat) -> ev n -> ev (4+n)
*)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition interesting_fun (H: ev 4) : ev 8 :=
    ev_plus4 4 H.

Compute (interesting_fun (ev_SS 2 (ev_SS 0 ev_0))).

Check ev_plus4.
Print ev_plus4.

Compute ev_plus4.

Compute is_eveen.

(** What is the proof object corresponding to [ev_plus4]?

    We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!

    Here it is: *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n). Admitted.

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]," and that Coq treats [4 + n] and [S (S (S (S n)))]
    as synonyms. Another equivalent way to write this definition is: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.

(** When we view the proposition being proved by [ev_plus4] as a
    function type, one interesting point becomes apparent: The second
    argument's type, [ev n], mentions the _value_ of the first
    argument, [n].

    While such _dependent types_ are not found in conventional
    programming languages, they can be useful in programming too, as
    the recent flurry of activity in the functional programming
    community demonstrates. *)

(** Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat -> nat
*)

(** For example, consider this proposition: *)

Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    even.  But the name [E] for this evidence is not used in the rest
    of the statement of [ev_plus2], so it's a bit silly to bother
    making up a name for it.  We could write it like this instead,
    using the dummy identifier [_] in place of a real name: *)

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

(** Or, equivalently, we can write it in a more familiar way: *)

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ################################################################# *)
(** * Programming with Tactics *)

(** If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may be wondering whether we can
    build _programs_ using _tactics_ rather than explicit terms.
    Naturally, the answer is yes! *)

Definition add1 : nat -> nat.
Admitted.

Print add1.
(* ==>
    add1 = fun n : nat => S n
         : nat -> nat
*)

Compute add1 2.
(* ==> 3 : nat *)

(** Notice that we terminate the [Definition] with a [.] rather than
    with [:=] followed by a term.  This tells Coq to enter _proof
    scripting mode_ to build an object of type [nat -> nat].  Also, we
    terminate the proof with [Defined] rather than [Qed]; this makes
    the definition _transparent_ so that it can be used in computation
    like a normally-defined function.  ([Qed]-defined objects are
    opaque during computation.)

    This feature is mainly useful for writing functions with dependent
    types, which we won't explore much further in this book.  But it
    does illustrate the uniformity and orthogonality of the basic
    ideas in Coq. *)





(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Coq; all the others are defined inductively.  We'll see these
    definitions in this section. *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for [P
    /\ Q] as consisting of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | 

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** **** Exercise: 2 stars, standard (conj_fact)

    Construct a proof object for the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct: *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(** **** Exercise: 2 stars, standard (or_commut')

    Construct a proof object for the following proposition. *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Check (fun (n:nat) (H:ev n) => Nat.div n 2).

(*
  (n:nat) -> (H:evn n) -> nat
*)

Check forall (n :nat), ev n -> False.

Check nat -> nat -> nat .

Check fun (X:Type) (Y:Type) (f: X -> Y) (x:X) => f x.

Definition odd(n:nat) := not (ev n).

Theorem ev_lem: forall n, ev n -> odd (S n).
Proof.
  intros n H0.
  induction n as [| n' IHn'].
  + unfold odd; unfold not. intros H1; inversion H1.
  + unfold odd; unfold not. intros H1. inversion H1.
    apply IHn' in H2. unfold odd in H2; unfold not in H2.
    apply H2. assumption.
Qed. 


Check ev_ind.

Theorem lem_even_odd: forall n, ev n \/ odd n.
Proof.
  intros n. 
  induction n as [| n' IHn'].
  + left; apply ev_0.
  + destruct IHn'.
   - right. unfold odd; unfold not.
     intros H1. apply ev_lem in H1. 
     unfold odd in H1; unfold not in H1. apply H1. 
     apply ev_SS. assumption.
   - left. rename n' into n. induction n as [| n' IHn'].
      * unfold odd in H; unfold not in H. exfalso. apply H. apply ev_0.
      * apply ev_SS.  
Qed.




(*

 l = x::t
------------ [x_head]
   x ∈ l

 l = h::t   x ∈ t
------------------ [x_tail]
    x ∈ l

*)

(*

l = x::t   y ∈ t
-----------------
     ord x y l 

l = h::t    ord x y t     
----------------------
    ord x y l

*)


Inductive In {A : Type}: A -> list A -> Prop :=
 | x_head: forall (x:A)(l t: list A), (l = x::t) -> In x l
 | x_tail: forall (x h:A)(l t: list A), (l = h::t) -> In x t -> In x l.
 

Theorem silly: forall (n :nat), ev n -> False.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | 

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

(** This may benefit from a little unpacking.  The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The notation in the standard library is a slight variant of
    the above, enabling syntactic forms such as [exists x y, P x y]. *)

(** The more familiar form [exists x, P x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** **** Exercise: 2 stars, standard (ex_ev_Sn)

    Construct a proof object for the following proposition. *)

Definition ex_ev_Sn : ex (fun n => ev (S n))
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ================================================================= *)
(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** **** Exercise: 1 star, standard (p_implies_true)

    Construct a proof object for the following proposition. *)

Definition p_implies_true : forall P, P -> True
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. For example, there is
    no way to complete the following definition such that it
    succeeds (rather than fails). *)

Fail Definition contra : False :=
  0 = 1.

(** But it is possible to destruct [False] by pattern matching. There can
    be no patterns that match it, since it has no constructors.  So
    the pattern match also is so simple it may look syntactically
    wrong at first glance. *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(** Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
    Indeed, it's impossible to ever cause the [match] to be evaluated,
    because we can never construct a value of type [False] to pass to
    the function. *)

(** **** Exercise: 1 star, standard (ex_falso_quodlibet')

    Construct a proof object for the following proposition. *)

Definition ex_falso_quodlibet' : forall P, False -> P
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End Props.

Check (fun (n:nat) (H:ev n) => Nat.div n 2).