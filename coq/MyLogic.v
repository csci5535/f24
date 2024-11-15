Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

Check (3 = 3).

Check 3 = 2.

Check (forall n m : nat, n + m = m + n).



Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.



Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.



(* You can define functions that return propositions *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Check (is_three 4).


(* You can define polymorphic propositions *)
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  unfold injective.
  intros x y H.
  injection H as Heq.
  apply Heq.
Qed.  

(* Equality is a (polymorphic) proposition *)
Check @eq.

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. 
  split.
  + reflexivity.
  + reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. 
  intros n m.
  split.
  + destruct n as [| n'].
    - reflexivity.
    - discriminate.
  + destruct m as [| m'].
  - Admitted.

(** To _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form
    [A /\ B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite  Hn. rewrite Hm. reflexivity.
Qed.


(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (This infix notation stands for [or A B], where [or : Prop ->
    Prop -> Prop].) *)

(* A \/ B -> C  <-> (A -> C) /\ (B -> C)*)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H. destruct H as [Hn | Hm].
  + rewrite Hn. reflexivity.
  + rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Check mult_n_O.    


(* You can prove a disjunction by proving either left disjunct or 
   the right disjunct. *)
Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  + left. reflexivity.
  + right. reflexivity.
Qed. 

(* Need this lemma later *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. Admitted.


(* ================================================================= *)
(** ** Falsehood and Negation *)


(* How do you encode Negation? *)






Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End MyNot.

Check False.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P [].
Qed.


Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P np Q hp.
  unfold not in np.
  apply np in hp.
  exfalso. apply hp.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
Admitted.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P hp.
  unfold not.
  intros H1.
  apply H1. assumption.
Qed.

Check True.
(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.
    
(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros.
  split.
  + destruct H. assumption.
  + destruct H. assumption.
Qed. 

(* ================================================================= *)
(** ** Using Logical Equivalence for rewriting *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we have
    to import the Coq library that supports it: *)

From Coq Require Import Setoids.Setoid.


(* We need the following two theorems for demonstration. *)
Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(* Demonstration *)
Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
Admitted.

Example and_exercise2 :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof. 
  intros n m.
  split.
  + destruct n as [| n'].
    - reflexivity.
    - discriminate.
  + destruct m as [| m'].
    - reflexivity.
    - rewrite add_comm in H. simpl in H. discriminate.  
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

Definition Even x := exists n : nat, x = double n.
Check Even.

Lemma four_is_even : Even 4.
Proof.
  unfold Even.
  exists 2. reflexivity.
Qed.
  

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  destruct H.
  exists (2+x).
  simpl in H.
  simpl. assumption.
  
Qed.

(* ################################################################# *)
(** * Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  unfold In.
  right. right. right. left. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
 intros.
 induction l as [|h t].
 + simpl. destruct H.
 + simpl. simpl in H. destruct H.
   - left. apply f_equal. assumption.
   - right. apply IHt. assumption.
Qed.      


(** Recursive definitions vs Inductive definitions of propositions *)


(* ================================================================= *)
(** ** Propositions vs. Booleans

    We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
*)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Since [Prop] includes _both_ decidable and undecidable properties,
    we have two choices when when we are dealing with a property that
    happens to be decidable: we can express it as a boolean
    computation or as a function into [Prop].

    For instance, to claim that a number [n] is even, we can say
    either... *)

(** ... that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.


(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** The following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.


Theorem excluded_middle_conseq: forall P:Prop,
(P \/ ~P) -> (~~P) -> P.
Proof.
  intros P H1 H2.
  unfold not at 1 in H2.
  destruct H1.
  - assumption.
  - exfalso. apply H2. assumption.
Qed. 

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P,
    (exists b, P <-> b = true) -> P \/ ~ P.
Proof.
  intros P H.
  destruct H. destruct x.
  + left. rewrite H. reflexivity.
  + right. rewrite H. unfold "<>". intros contra. discriminate contra.  
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Lemma eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
Admitted. (** HOMEWORK!! *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle).
  exists (n =? m).
  symmetry.
  apply eqb_eq.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq, since it is a standard feature of
    familiar logics like ZFC.  But there is a distinct advantage in
    not assuming the excluded middle: statements in Coq make stronger
    claims than the analogous statements in standard mathematics.
    Notably, when there is a Coq proof of [exists x, P x], it is
    always possible to explicitly exhibit a value of [x] for which we
    can prove [P x] -- in other words, every proof of existence is
    _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that
    [a ^ b] ([a] to the power [b]) is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  [] *)