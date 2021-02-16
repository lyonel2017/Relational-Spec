From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.

(* Redefintion the definition of set from Why3 *)

Module Why3_Set.

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

End Why3_Set.

Import Why3_Set.
(* Boolean evaluation as Prop *)

Definition bassn b :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false ->  ~((bassn b) st).
Proof. congruence. Qed.

(* Defintion of a verification condition generator *)

Fixpoint tc (c : com) (m : Sigma.sigma)
            (ps: Psi.psi) (suite : Sigma.sigma -> Prop) : Prop :=
    match c with
    | CSkip => forall m', m = m' -> suite m'
    | CAss x a => forall m', (m' = set m x (aeval m a)) -> suite m'
    | CAssert b => forall m', b m -> m = m' -> suite m'
    | CSeq p1 p2 => tc p1 m ps (fun m' => tc p2 m' ps suite)
    | CIf b p1 p2 => (bassn b m -> tc p1 m ps suite) /\ 
                     (~bassn b m  -> tc p2 m ps suite)
    | CWhile b p inv => inv m ->
                        forall m', inv m' -> beval m' b = false -> suite m'
    | CCall f => (get_pre (snd (ps f))) m ->
                  forall m',  (get_post (snd (ps f))) m' -> suite m'
    end.

(* Some facts about tc*)
Scheme com_ind_max := Induction for com Sort Prop. 

Lemma consequence_tc_suite :
forall p ps m (suite1 suite2 : Sigma.sigma -> Prop),
(forall s, suite1 s -> suite2 s) ->
tc p m ps suite1 -> tc p m ps suite2.
Proof.
intros p ps.
induction p.
  * intros. simpl. simpl in H0.
    intros.
    apply H.
    apply H0.
    assumption.
  * intros. simpl. simpl in H0.
    intros.
    apply H.
    apply H0.
    assumption.
  * intros. simpl. simpl in H0.
    intros.
    apply H.
    apply H0.
    assumption.
    assumption.
  * intros.
    simpl. simpl in H0.
    eapply IHp1.
    - intros.
      eapply IHp2.
       + apply H.
       + apply H1.
    - assumption.
  * intros.
    simpl. simpl in H0.
    intros. destruct H0.
    split.
    - intros.
      eapply IHp1.
      apply H. apply H0. assumption.
    -intros.
      eapply IHp2.
      apply H. apply H1. assumption.
  * intros.
    simpl. simpl in H0.
    intros. apply H.
    apply H0.
    all : try assumption.
  * intros. simpl. simpl in H0.
    intros. apply H.
    apply H0.
    all : try assumption.
Qed.

Lemma tc_split :
forall p ps m (suite1 suite2 : Sigma.sigma -> Prop),
tc p m ps suite1 -> tc p m ps suite2 ->
tc p m ps (fun m' => suite1 m' /\ suite2 m').
Proof.
intros p ps.
induction p.
+ simpl. intros.
  split.
  apply H. subst. reflexivity.
  apply H0. subst. reflexivity.
+ simpl. intros.
  split.
  apply H. subst. reflexivity.
  apply H0. subst. reflexivity.
+ simpl. intros.
  split.
  apply H. assumption. subst. reflexivity.
  apply H0. assumption. subst. reflexivity.
+ simpl. intros.
  apply (consequence_tc_suite _ _ _ (fun m => tc p2 m ps suite1 /\ tc p2 m ps suite2)).
  * intros. destruct H1. apply IHp2. assumption. assumption.
  * apply IHp1. assumption. assumption.
+ intros.
  simpl. simpl in H, H0.
  split.
  * intros.
    apply IHp1.
    apply H. assumption.
    apply H0. assumption.
  * intros.
    apply IHp2.
    apply H. assumption.
    apply H0. assumption.
+ simpl. intros.
  split. 
    * apply H.
      all: try assumption.
    * apply H0.
      all: try assumption.
+ simpl. intros.
  split.
    * apply H.
      all: try assumption.
    * apply H0.
      all: try assumption.
Qed.

(* Definition of a verification condition generator for the auxiliary goals *)

Fixpoint tc' (c : com) (m : Sigma.sigma)
            (ps: Psi.psi) : Prop :=
    match c with
    | CSkip => True
    | CAss x a => True
    | CAssert b => b m 
    | CSeq p1 p2 => tc' p1 m ps /\
                    tc p1 m ps (fun m' => tc' p2 m' ps)
    | CIf b p1 p2 => 
                    (bassn b m -> tc' p1 m ps) /\ 
                    (~bassn b m -> tc' p2 m ps)
    | CWhile b p inv => inv m /\
                          (forall m', bassn b m' -> tc' p m' ps) /\
                          (forall m', inv m'  -> tc p m' ps inv)
    | CCall f => (get_pre (snd (ps f))) m
    end.

Definition tc_p (ps : Psi.psi) : Prop :=
    forall f m, (get_pre (snd (ps f))) m -> tc' (fst (ps f)) m ps /\
                tc (fst (ps f)) m ps (get_post (snd (ps f))). 

Lemma tc_p_empty_psi :  tc_p Psi.empty_psi.
Proof.
unfold tc_p.
intros.
split.
* auto.
* simpl. intros. unfold empty_postcondition. auto.
Qed.