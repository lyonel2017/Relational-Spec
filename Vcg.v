From Coq Require Import PeanoNat.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.

From Coq Require Import Lia.

Definition set: (Loc.t -> nat) -> Loc.t -> nat -> Loc.t -> nat.
Proof.
intros m x y.
intros x'.
destruct (Loc.eq_dec x x') as [H|H].
exact y.
exact (m x').
Defined.

Lemma set'def:
  forall (f: Loc.t -> nat ) (x: Loc.t) (v:nat) (y: Loc.t),
  ((y = x) -> ((set f x v y) = v)) /\ (~ (y = x) -> ((set f x v y) = (f y))).
Proof.
intros f x v y.
split.
+ intros.
 unfold set.
 destruct (Loc.eq_dec x y).
  * reflexivity.
  * contradiction n.
    rewrite H. reflexivity.
+ intros. 
  unfold set.
 destruct (Loc.eq_dec x y).
  * contradiction H.
    rewrite e. reflexivity.
  * reflexivity.
Qed.


Lemma set''def:
  forall (f: Loc.t -> nat ) (x: Loc.t) (v w:nat) (y: Loc.t),
  (y = x -> v = w -> ((set f x v y) = w)).
Proof.
intros f x v w y H1 H2.
unfold set.
destruct (Loc.eq_dec x y).
  * rewrite H2. reflexivity.
  * contradiction n.
    rewrite H1. reflexivity.
Qed.

(** Definition of Precondtion **)

Definition precondition : Type := assertion.

Definition empty_precondition : precondition := (fun _ => True).

(** Defintion of Postcondtion **)

Definition postcondition : Type := assertion.

Definition empty_postcondition :  postcondition := (fun _ => True).

(** Definition of a contract **)

Definition clause : Type := precondition * postcondition.

Definition empty_clause : clause := (empty_precondition, empty_postcondition). 

Module Phi.

  (** The programs that can be called is a maps from procedure to program **)

  Definition phi : Type := Proc.t -> clause.

  Definition update_psi (x:Proc.t) (v: clause) (l:phi): phi :=
  fun (x': Proc.t) => if Proc.eqb x' x then v else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100, v at next level, right associativity).

  Definition get_pre (an:clause) := 
          let (pre,post) := an in
          pre.

  Definition get_post (an:clause) := 
          let (pre,post) := an in
          post.

End Phi.

Inductive branch (A B C : Prop) : Prop :=  
  | Then : A -> B -> branch A B C
  | Else : ~ A -> C -> branch A B C.

Definition bassn b :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false ->  ~((bassn b) st).
Proof. congruence. Qed.

Fixpoint tc (c : com) (m : Sigma.sigma)
            (ps: Phi.phi) (suite : Sigma.sigma -> Prop) : Prop :=
    match c with
    | CSkip => forall m', m = m' -> suite m'
    | CAss x a => forall m', (m' = set m x (aeval m a)) -> suite m'
    | CAssert b => forall m', b m -> m = m' -> suite m'
    | CSeq p1 p2 => tc p1 m ps (fun m' => tc p2 m' ps suite)
    | CIf b p1 p2 =>
                (*tc p1 m ps (fun m1' => 
                tc p2 m ps (fun m2' => forall m',
                branch (bassn b m) (m' = m1') (m' = m2') -> suite m'))*)
    (bassn b m -> tc p1 m ps suite) /\  (~bassn b m  -> tc p2 m ps suite)
    (*| CWhile b p inv _ => inv m -> inv m' -> beval m b = false -> suite *)
    end.

Definition empty_phi: Phi.phi := fun _ => empty_clause.

Lemma test1 : forall m,  m EAX = 1 -> tc plus2 m empty_phi (fun m' => m' EAX = 3) .
Proof.
simpl.
intros.
rewrite H0.
rewrite H.
simpl.
apply set'def.
reflexivity.
Qed.

Definition plus3 : com := CSeq (CAss EAX (APlus (AId EAX) (ANum 2)))
                                (CAss EAX (APlus (AId EAX) (ANum 2))).

Lemma test2 : forall m , m EAX = 1 -> tc plus3 m empty_phi (fun m' => m' EAX = 5).
Proof.
simpl.
intros.
rewrite H1.
rewrite H0.
rewrite H.
simpl.
apply set'def.
reflexivity.
Qed.

Definition if2 : com := CIf (BEq (AId EAX) (ANum 4)) plus2 plus2.

Lemma test3 : forall m, m EAX = 1 -> tc if2 m empty_phi (fun m' => m' EAX = 3).
Proof.
(* simpl.
 intros.
 destruct H2.
 + rewrite H3.
   rewrite H0.
   rewrite H.
   apply set'def.
   reflexivity.
 + rewrite H3.
   rewrite H1.
   rewrite H.
   apply set'def.
   reflexivity.
*)

  simpl.
  intros.
  split;intros.
  + rewrite H1.
    rewrite H.
    apply set'def.
    reflexivity.
  + rewrite H1.
    rewrite H.
    apply set'def.
    reflexivity.
Qed.

Definition if3 : com := CSeq (CAss EAX (APlus (AId EAX) (ANum 2)))
                            (CSeq (CIf (BEq (AId EAX) (ANum 4)) plus2 plus2) plus2).

Lemma test4 : forall m, m EAX = 1 -> tc if3 m empty_phi (fun m' => m' EAX = 7).
Proof.
 (* simpl.
  intros.
  rewrite H4.
  destruct H3.
  * rewrite H5.
    rewrite H1.
    rewrite H0.
    rewrite H.
    apply set'def.
    reflexivity.
  * rewrite H5.
    rewrite H2.
    rewrite H0.
    rewrite H.
    apply set'def.
    reflexivity.*)
 simpl.
 intros.
 split.
 * intros.
   rewrite H3.
   rewrite H2.
   rewrite H0.
   rewrite H.
   apply set'def.
   reflexivity.
 * intros.
   rewrite H3.
   rewrite H2.
   rewrite H0.
   rewrite H.
   apply set'def.
   reflexivity.
Qed.

Lemma test5 : forall m1 m2, m1 EAX = m2 EAX -> 
                              tc plus2 m1 empty_phi ( fun m1' => tc plus2 m2 empty_phi (fun m2' => m1' EAX = m2' EAX)).
Proof.
  simpl.
  intros.
  rewrite H1.
  rewrite H0.
  rewrite H.
  apply set'def.
  reflexivity.
Qed.

Fixpoint tc' (c : com) (m : Sigma.sigma)
            (ps: Phi.phi) (suite : Sigma.sigma -> Prop) : Prop :=
    match c with
    | CSkip => tc c m ps suite
    | CAss x a => tc c m ps suite
    | CAssert b => b m /\ tc c m ps suite
    | CSeq p1 p2 => tc' p1 m ps (fun m' => tc' p2 m' ps suite)
    | CIf b p1 p2 => 
         (bassn b m -> tc' p1 m ps (fun _ => True)) /\
         (~bassn b m -> tc' p2 m ps (fun _ => True)) /\
          tc c m ps suite
    (*| CWhile b p inv _ => 
      (beval m b = true -> inv m ) /\ 
      (beval m b = true -> forall mi, inv mi -> 
                           tp p m ps (fun mf => inv mf)) /\ 
      (beval m b = true -> forall mi, inv mi -> tp' p m ps) /\ 
      tc c m m' ps suite*)
    end.

Definition truc3 : com := CSeq (CAssert (fun m => m EAX = 2))
                          (CAssert (fun m => m EAX = 2)).

Lemma test6 : forall m, (m EAX = 2) -> tc' truc3 m  empty_phi (fun _ => True).
Proof.
intros.
simpl.
intros.
split. 
  * assumption.
  * intros. split.
    - rewrite <- H1. assumption.
    - intros. auto. 
Qed.

Definition if4 : com := CIf (BEq (AId EAX) (ANum 2)) (CAssert (fun m => m EAX = 2)) CSkip.

Lemma test7 : forall m, (m EAX = 2) -> tc' if4 m  empty_phi (fun _ => True).
Proof.
intros.
simpl.
split. 
  * split. all: try auto.
  * split.
    - auto.
    - split. all: try auto.
Qed.