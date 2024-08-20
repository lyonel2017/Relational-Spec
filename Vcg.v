From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Hoare_Triple.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Coq Require Import Lists.List.
Import ListNotations.

(** Redefinition of set from Why3 **)

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

(** Boolean evaluation as Prop **)

Module Assn_b.

Import Bool.Bool.

Definition bassn b :=
  fun st => (Is_true (beval st b)).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
intros. unfold bassn. apply Is_true_eq_left. auto.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false ->  ~((bassn b) st).
Proof.
intros. unfold bassn. apply negb_prop_elim.
apply Is_true_eq_left.
apply negb_true_iff. auto.
Qed.

End Assn_b.

Import Assn_b.

(** Definition of a verification condition generator **)

Definition history: Type := list Sigma.sigma.

Definition empty_history: history := [].

Definition suite : Type := Sigma.sigma -> history -> Prop.

Fixpoint tc (c : com) (m : Sigma.sigma) (h : history)
            (cl: Phi.phi) (s : suite) : Prop :=
    match c with
    | CSkip => forall m', m = m' -> s m' (m :: h)
    | CAss x a => forall m', (m' = set m x (aeval m a)) -> s m' (m :: h)
    | CAssr x a => forall m', (m' = set m (m x) (aeval m a)) -> s m' (m :: h)
    | CAssert b => forall m', b (m :: h) -> m = m' -> s m' (m :: h)
    | CSeq p1 p2 => tc p1 m h cl (fun m' h => tc p2 m' h cl s)
    | CIf b p1 p2 => (bassn b m -> tc p1 m h cl (fun m' _ => s m' (m :: h))) /\
                     (~bassn b m  -> tc p2 m h cl (fun m' _ => s m' (m :: h)))
    | CWhile b p inv _ => inv (m :: h) ->
                        forall m', inv (m' :: h) -> beval m' b = false -> s m' (m :: h)
    | CCall f => (get_pre (cl f)) m ->
                  forall m',  (get_post (cl f)) m' m -> s m' (m :: h)
    end.

(** Facts about verification condition generator **)

Ltac ltc1 := intros m l s1 s2 H H0;
             simpl; intros;
             simpl in H0;
             apply H; apply H0; assumption.

Lemma consequence_tc_suite :
forall p cl m l (s1 s2 : suite),
(forall s l, s1 s l -> s2 s l) ->
tc p m l cl s1 -> tc p m l cl s2.
Proof.
intros p cl.
induction p.
  * ltc1.
  * ltc1.
  * ltc1.
  * ltc1.
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
      specialize (IHp1 m l (fun (m' : sigma) (_ : list sigma) => s1 m' (m :: l)) 
      (fun (m' : sigma) (_ : list sigma) => s2 m' (m :: l))).
      apply IHp1.
      + intros. apply H. apply H3.
      + apply H0. assumption.
     - intros.
       specialize (IHp2 m l (fun (m' : sigma) (_ : list sigma) => s1 m' (m :: l)) 
      (fun (m' : sigma) (_ : list sigma) => s2 m' (m :: l))).
        apply IHp2.
      + intros. apply H. apply H3.
      + apply H1. assumption.
  * ltc1.
  * ltc1.
Qed.

Ltac ltc2 := intros m l s1 s2 H H0;
             simpl; intros;
             split;[ apply H; try assumption; subst; reflexivity
                   | apply H0; try assumption; subst; reflexivity].

Lemma tc_split :
forall p cl m l (s1 s2 : suite),
tc p m l cl s1 -> tc p m l cl s2 ->
tc p m l cl (fun m' h => s1 m' h /\ s2 m' h).
Proof.
intros p cl.
induction p.
+ ltc2.
+ ltc2.
+ ltc2.
+ ltc2.
+ simpl. intros.
  apply (consequence_tc_suite _ _ _ _ (fun m h => tc p2 m h cl s1 /\ tc p2 m h cl s2)).
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
+ ltc2.
+ ltc2.
Qed.

(** Definition of a verification condition generator for the auxiliary goals **)

Fixpoint tc' (c : com) (m : Sigma.sigma) (h : history)
            (cl: Phi.phi) : Prop :=
    match c with
    | CSkip => True
    | CAss x a => True
    | CAssr x a => True
    | CAssert b => b (m :: h)
    | CSeq p1 p2 => tc' p1 m h cl /\
                    tc p1 m h cl (fun m' h => tc' p2 m' h cl)
    | CIf b p1 p2 =>
                    (bassn b m -> tc' p1 m h cl) /\
                    (~bassn b m -> tc' p2 m h cl)
    | CWhile b p inv _ => inv (m :: h) /\
                     (forall m', bassn b m' -> inv (m' :: h)-> tc' p m' h cl) /\
                     (forall m', bassn b m' -> inv (m' :: h) ->
                                  tc p m' h cl (fun m'' _ => inv (m'' :: h)))
    | CCall f => (get_pre (cl f)) m
    end.

(** Definition of a verification condition generator for procedures **)

Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m, (get_pre (cl f)) m ->
    tc' (ps f) m empty_history cl /\
    tc (ps f) m empty_history cl (fun m' _ => get_post (cl f) m' m).

(** Facts about verification condition generator for procedures **)

Lemma tc_p_empty_psi : forall psi, tc_p psi Phi.empty_phi.
Proof.
unfold tc_p.
intros.
simpl in H.
unfold empty_precondition in H.
contradiction.
Qed.

(** Verification of trivial procedure contract **)
Module Trivial_proc.

Parameter f : Proc.t.

Definition f_psi (x': Proc.t) :=
        if Proc.eqb x' f then CSkip else Psi.empty_psi x'.

Definition f_phi (x': Proc.t) :=
        if Proc.eqb x' f then 
        ((fun _ => True), (fun _ _ => True)) 
        else Phi.empty_phi x'.

Example tc_p_update : tc_p f_psi f_phi.
Proof.
unfold tc_p.
unfold f_psi, f_phi.
intros.
destruct (Proc.eqb f0 f).
- split.
  * simpl in H.
    simpl. apply H.
  * simpl in H.
    simpl. intros. apply H.
- intros.
  simpl in H.
  unfold empty_precondition in H.
  contradiction.
Qed.

End Trivial_proc.
