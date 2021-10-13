From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Hoare_Triple.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.

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

(** Defintion of a verification condition generator **)

Fixpoint tc (c : com) (m : Sigma.sigma)
            (cl: Phi.phi) (suite : assertion) : Prop :=
    match c with
    | CSkip => forall m', m = m' -> suite m'
    | CAss x a => forall m', (m' = set m x (aeval m a)) -> suite m'
    | CAssr x a => forall m', (m' = set m (m x) (aeval m a)) -> suite m'
    | CAssert b => forall m', b m -> m = m' -> suite m'
    | CSeq p1 p2 => tc p1 m cl (fun m' => tc p2 m' cl suite)
    | CIf b p1 p2 => (bassn b m -> tc p1 m cl suite) /\
                     (~bassn b m  -> tc p2 m cl suite)
    | CWhile b p inv => inv m ->
                        forall m', inv m' -> beval m' b = false -> suite m'
    | CCall f => (get_pre (cl f)) m ->
                  forall m',  (get_post (cl f)) m' -> suite m'
    end.

(** Facts about verification condition generator **)

Ltac ltc1 := intros m suite1 suite2 H H0;
             simpl; intros;
             simpl in H0;
             apply H; apply H0; assumption.

Lemma consequence_tc_suite :
forall p cl m (suite1 suite2 : assertion),
  (forall s, suite1 s -> suite2 s) ->
  tc p m cl suite1 -> tc p m cl suite2.
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
      eapply IHp1.
      apply H. apply H0. assumption.
    - intros.
      eapply IHp2.
      apply H. apply H1. assumption.
  * ltc1.
  * ltc1.
Qed.

Ltac ltc2 := intros m suite1 suite2 H H0;
             simpl; intros;
             split;[ apply H; try assumption; subst; reflexivity
                   | apply H0; try assumption; subst; reflexivity].

Lemma tc_split :
forall p cl m (suite1 suite2 : assertion),
  tc p m cl suite1 -> tc p m cl suite2 ->
  tc p m cl (fun m' => suite1 m' /\ suite2 m').
Proof.
intros p cl.
induction p.
+ ltc2.
+ ltc2.
+ ltc2.
+ ltc2.
+ simpl. intros.
  apply (consequence_tc_suite _ _ _ (fun m => tc p2 m cl suite1 /\ tc p2 m cl suite2)).
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

Fixpoint tc' (c : com) (m : Sigma.sigma) (cl: Phi.phi) : Prop :=
    match c with
    | CSkip => True
    | CAss x a => True
    | CAssr x a => True
    | CAssert b => b m
    | CSeq p1 p2 => tc' p1 m cl /\
                    tc p1 m cl (fun m' => tc' p2 m' cl)
    | CIf b p1 p2 =>
                    (bassn b m -> tc' p1 m cl) /\
                    (~bassn b m -> tc' p2 m cl)
    | CWhile b p inv => inv m /\
                     (forall m', bassn b m' -> inv m' -> tc' p m' cl) /\
                     (forall m', bassn b m' -> inv m'  -> tc p m' cl inv)
    | CCall f => (get_pre (cl f)) m
    end.

(** Definition of a verification condition generator for procedures **)

Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m, (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m cl (get_post (cl f)).

(** Facts about verification condition generator for procedures **)

Lemma tc_p_empty_psi : tc_p Psi.empty_psi Phi.empty_phi.
Proof.
unfold tc_p.
intros.
split.
* auto.
* simpl. intros. unfold empty_postcondition. auto.
Qed.

(** Verification of trivial procedure contract **)

Parameter f : Proc.t.
Definition cli_1 (x': Proc.t) :=
        if Proc.eqb x' f then CSkip else Psi.empty_psi x'.

Definition phi_1 (x': Proc.t) :=
        if Proc.eqb x' f then empty_clause else Phi.empty_phi x'.

Example tc_p_update : tc_p cli_1 phi_1.
Proof.
unfold tc_p.
unfold cli_1, phi_1.
intros.
destruct (Proc.eqb f0 f).
- split.
  * now auto.
  * simpl. intros. unfold empty_postcondition. auto.
- apply tc_p_empty_psi.
  assumption.
Qed.
