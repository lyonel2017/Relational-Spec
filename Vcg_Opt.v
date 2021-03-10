From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Vcg.
From Rela Require Import Hoare_Triple.

Import Vcg.Why3_Set.
Import Vcg.Assn_b.

Inductive branch (A B C : Prop) : Prop :=
  | Then : A -> B -> branch A B C
  | Else : ~ A -> C -> branch A B C.

Lemma branch_simpl : forall A B C,
branch A B C -> (A -> B) /\ (~A -> C).
Proof.
intros.
destruct H.
+ split.
  * auto.
  * intros. contradiction H1.
+ split.
  * intros. contradiction H1.
  * auto.
Qed.

Fixpoint tc (c : com) (m : Sigma.sigma)
            (cl: Phi.phi) (suite : Sigma.sigma -> Prop) : Prop :=
    match c with
    | CSkip => forall m', m = m' -> suite m'
    | CAss x a => forall m', (m' = set m x (aeval m a)) -> suite m'
    | CAssert b => forall m', b m -> m = m' -> suite m'
    | CSeq p1 p2 => tc p1 m cl (fun m' => tc p2 m' cl suite)
    | CIf b p1 p2 =>
               tc p1 m cl (fun m1' =>
               tc p2 m cl (fun m2' =>
               forall m',
               branch (bassn b m) (m' = m1') (m' = m2') -> suite m'))
    | CWhile b p inv => inv m ->
                        forall m', inv m' -> beval m' b = false -> suite m'
    | CCall f => (get_pre (cl f)) m ->
                  forall m',  (get_post (cl f)) m' -> suite m'
    end.

Lemma consequence_tc_suite :
forall p cl m (suite1 suite2 : Sigma.sigma -> Prop),
(forall s, suite1 s -> suite2 s) ->
tc p m cl suite1 -> tc p m cl suite2.
Proof.
intros p cl.
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
  * intros.  simpl. simpl in H0.
    eapply IHp1.
    - intros.
      eapply IHp2.
       + apply H.
       + apply H1.
    - assumption.
  * intros. simpl. simpl in H0.
    intros.
    eapply IHp1.
    - intros.
      eapply IHp2.
       + intros. apply H.
        generalize H3. generalize m'. apply H2.
       + apply H1. 
     - apply H0.
  * intros. simpl. simpl in H0.
    intros. apply H.
    apply H0.
    all : try assumption.
  * intros. simpl. simpl in H0.
    intros. apply H.
    apply H0.
    all : try assumption.
Qed.

Lemma split_tc :
forall p m cl (suite1 suite2 : Sigma.sigma -> Prop),
tc p m cl (fun m' => suite1 m' /\ suite2 m') ->
tc p m cl suite1 /\ tc p m cl suite2.
Proof.
intros.
split.
* apply (consequence_tc_suite _ _ _ (fun m' => suite1 m' /\ suite2 m')).
  + intros.
    destruct H0.
    assumption.
  + assumption.
* apply (consequence_tc_suite _ _ _ (fun m' => suite1 m' /\ suite2 m')).
  + intros.
    destruct H0.
    assumption.
  + assumption.
Qed.

Lemma opt_1_true:
forall p1 p2 b m cl (suite : Sigma.sigma -> Prop),
bassn b m ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m', branch (bassn b m) (m' = m1') (m' = m2') -> suite m')) ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m', m' = m1' -> suite m')).
Proof.
intros.
apply (consequence_tc_suite _ _ _ (fun m1' => tc p2 m cl (fun m2' => forall m', branch (bassn b m) (m' = m1') (m' = m2') -> suite m'))).
* intros.
  apply (consequence_tc_suite _ _ _ (fun m2' : sigma => forall m' : sigma, branch (bassn b m) (m' = s) (m' = m2') -> suite m')).
  -  intros. apply H2.
    apply Then.
    assumption.
    assumption.
  - assumption.
* assumption.
Qed.

Lemma opt_1_false:
forall p1 p2 b m cl (suite : Sigma.sigma -> Prop),
~bassn b m ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m', branch (bassn b m) (m' = m1') (m' = m2') -> suite m')) ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m', m' = m2' -> suite m')).
Proof.
intros.
apply (consequence_tc_suite _ _ _ (fun m1' => tc p2 m cl (fun m2' => forall m', branch (bassn b m) (m' = m1') (m' = m2') -> suite m'))).
* intros.
  apply (consequence_tc_suite _ _ _ (fun m2' : sigma => forall m' : sigma, branch (bassn b m) (m' = s) (m' = m2') -> suite m')).
  -  intros. apply H2.
    apply Else.
    assumption.
    assumption.
  - assumption.
* assumption.
Qed.

Lemma opt_2_true:
forall p1 p2 m cl (suite : Sigma.sigma -> Prop),
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m',  m' = m1' -> suite m')) ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  suite m1')).
Proof.
intros.
apply (consequence_tc_suite _ _ _ (fun m1' => 
                                      tc p2 m cl (fun m2' =>  forall m',  m' = m1'-> suite m'))).
  + intros.
    eapply consequence_tc_suite in H0.
    - apply H0.
    - simpl. intros.
      apply H1.
        reflexivity.
  + assumption.
Qed.

Lemma opt_2_false:
forall p1 p2 m cl (suite : Sigma.sigma -> Prop),
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  forall m',  m' = m2' -> suite m')) ->
tc p1 m cl (fun m1' => 
tc p2 m cl (fun m2' =>  suite m2')).
Proof.
intros.
apply (consequence_tc_suite _ _ _ (fun m1' => 
                                      tc p2 m cl (fun m2' =>  forall m',  m' = m2'-> suite m'))).
  + intros.
    eapply consequence_tc_suite in H0.
    - apply H0.
    - simpl. intros.
      apply H1.
        reflexivity.
  + assumption.
Qed.

Lemma tc_split :
forall p cl m (suite1 suite2 : Sigma.sigma -> Prop),
tc p m cl suite1 -> tc p m cl suite2 ->
tc p m cl (fun m' => suite1 m' /\ suite2 m').
Proof.
intros p cl.
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
  apply (consequence_tc_suite _ _ _ (fun m => tc p2 m cl suite1 /\ tc p2 m cl suite2)).
  * intros. destruct H1. apply IHp2. assumption. assumption.
  * apply IHp1. assumption. assumption.
+ intros.
  simpl.
  destruct (beval m b) eqn:H1.
  * apply bexp_eval_true in H1.
    simpl in H, H0.
    apply opt_1_true in H.
    apply opt_1_true in H0.
    apply opt_2_true in H.
    apply opt_2_true in H0.
    apply (consequence_tc_suite _ _ _ 
        (fun m' => tc p2 m cl ( fun _ => suite1 m' /\ suite2 m'))).
        - intros s. apply consequence_tc_suite.
          intros. destruct H3.
          ++ subst. assumption.
          ++ contradiction H3.
        - apply (consequence_tc_suite _ _ _ 
        (fun m' => tc p2 m cl ( fun _ => suite1 m') /\ tc p2 m cl ( fun _ => suite2 m'))).
          ++ intros.  destruct H2. apply IHp2. assumption. assumption.
          ++ apply IHp1. assumption. assumption.
        - assumption.
        - assumption.
  * apply bexp_eval_false in H1.
    simpl in H, H0.
    apply opt_1_false in H.
    apply opt_1_false in H0.
    apply opt_2_false in H.
    apply opt_2_false in H0.
    apply (consequence_tc_suite _ _ _ 
        (fun _ => tc p2 m cl ( fun m' => suite1 m' /\ suite2 m'))).
        - intros s. apply consequence_tc_suite.
          intros. destruct H3.
          ++ contradiction H3.
          ++ subst. assumption.
        - apply (consequence_tc_suite _ _ _ 
        (fun _ => tc p2 m cl ( fun m' => suite1 m') /\ tc p2 m cl ( fun m' => suite2 m'))).
          ++ intros.  destruct H2. apply IHp2. assumption. assumption.
          ++ apply IHp1. assumption. assumption.
        - assumption.
        - assumption.
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

Fixpoint tc' (c : com) (m : Sigma.sigma)
            (cl: Phi.phi) : Prop :=
    match c with
    | CSkip => True
    | CAss x a => True
    | CAssert b => b m
    | CSeq p1 p2 => tc' p1 m cl /\
                    tc p1 m cl (fun m' => tc' p2 m' cl)
    | CIf b p1 p2 =>
      (bassn b m -> tc' p1 m cl) /\ (~bassn b m -> tc' p2 m cl)
   | CWhile b p inv => inv m /\
                          (forall m', bassn b m' -> tc' p m' cl) /\
                          (forall m', inv m'  -> tc p m' cl inv)
   | CCall f => (get_pre (cl f)) m
    end.

Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m, (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m cl (get_post (cl f)).

  (* use relational properties : module Opt to an proper file*)

(*Lemma simpl_tc :
forall p cl suite, forall m, tc p m cl (fun _ => suite) -> suite.
Proof.
intros p cl suite.
induction p.
* simpl in H. specialize (H m). apply H. reflexivity.
* simpl in H. specialize (H (set m x (aeval m a))). apply H. reflexivity.
* simpl in H. specialize (H m). apply H. apply H. reflexivity.
* simpl in H, H0.
  destruct H.
   specialize 
    (tc_split p1 cl m (fun m' : sigma => tc' p2 m' cl) (fun m' : sigma => tc p2 m' cl (fun _ : sigma => suite))).
     intros.
     specialize (H2 H1 H0).
  eapply (consequence_tc_suite _ _ _ _ (fun m' : sigma => tc' p2 m' cl /\suite)) in H2.
  + apply split_tc in H2.
    destruct H2.
    eapply IHp1.
    - apply H.
    - apply H3.
  + intros. destruct H3. split.
     - assumption.
     - eapply IHp2.
      ** apply H3.
      ** assumption. 
* simpl in H, H0.
 destruct (beval m b) eqn:H1.
  + apply bexp_eval_true in H1.
    apply opt_1_true in H0.
    apply opt_2_true in H0.
    eapply (consequence_tc_suite _ _ _ _ (fun _ : sigma => suite)) in H0.
    - eapply IHp1. apply H. apply H1. apply H0.
    -
    Abort.
 (*    apply H0.
    - intros. eapply IHp2. apply H. 
 
 
        apply H1.  apply H0.
    - assumption.
   + apply bexp_eval_false in H1.
    apply opt_1_false in H.
    apply opt_2_false in H.
    eapply (consequence_tc_suite _ _ _ _ (fun _ : sigma => suite)) in H.
    - eapply IHp1. apply H.
    - intros. eapply IHp2. apply H0.
    - assumption.
Qed.*)
*)


