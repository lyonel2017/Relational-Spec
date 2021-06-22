From Rela Require Import Vcg.
From Rela Require Import Hoare_Triple.
From Rela Require Import Com.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Loc.
Import Why3_Set.
Import Assn_b.

(** Proof that one can use a verification condition generator to proof Hoare Triples **)

Lemma correct :
  forall p cl ps,
  forall (P Q: assertion),
    (forall m, P m -> tc' p m cl) ->
    (forall m, P m -> tc p m cl Q) ->
    hoare_triple_ctx cl ps P Q p.
Proof.
  unfold hoare_triple_ctx.
  intros p cl ps.
  induction p.
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2.
    apply H. apply H2. inversion H3;subst. reflexivity.
  * intros P Q Htc' Htc Hproc. eapply seq_hoare_triple.
  + apply IHp1.
  - apply Htc'.
  - simpl in Htc', Htc.
    intros.
    specialize (Htc' m H).
    destruct Htc'.
    specialize (Htc m H).
    specialize
      (tc_split p1 cl m
                (fun m' : sigma => tc' p2 m' cl) (fun m' : sigma => tc p2 m' cl Q)).
    intros.
    apply H2. assumption. assumption.
  - assumption.
    + apply IHp2.
  - intros. destruct H. assumption.
  - intros. destruct H. assumption.
  - assumption.
    * intros P Q Htc' Htc Hproc. apply if_hoare_triple.
    + apply IHp1.
  - intros. apply Htc'. apply H. apply bexp_eval_true. apply H.
  - intros. simpl in Htc. destruct H. specialize (Htc m H). destruct Htc.
    apply H1. apply bexp_eval_true. assumption.
  - assumption.
    + apply IHp2.
  - intros. apply Htc'. apply H. destruct H. apply bexp_eval_false in H0. apply H0.
  - intros. simpl in H. destruct H. specialize (Htc m H). destruct Htc.
    apply H2. apply bexp_eval_false. assumption.
  - assumption.
    * intros  P Q Htc' Htc.
      specialize (IHp (fun s => inv s /\ beval s b = true) inv).
      intros Hproc s s' Pre.
      apply
        (consequence_hoare_post _ _ P _ (fun s : sigma => inv s /\ beval s b = false)).
    + apply (consequence_hoare_pre _ _ _ inv).
  - apply while_hoare_triple.
    specialize (Htc s Pre).
    specialize (Htc' s Pre).
    simpl in Htc, Htc'.
    destruct Htc'.
    destruct H0.
    apply IHp.
    ** intros.
       apply H0.
       destruct H2.
       apply bexp_eval_true in H3.
       assumption.
    ** intros.
       apply H1.
       apply H2.
    ** assumption.
  - intros.
    specialize (Htc' s0 H).
    apply Htc'.
    + intros.
      specialize (Htc s Pre).
      apply Htc.
      specialize (Htc' s Pre).
      apply Htc'.
      apply H.
      apply H.
    + assumption.
 * intros P Q Htc' Htc Hproc.
  intros s s' Pre.
   apply (consequence_hoare_post _ _ P _ (get_post (cl f))).
    + apply (consequence_hoare_pre _ _ _ (get_pre (cl f))).
      - apply Hproc.
      - apply Htc'.
    + eapply Htc.
      apply Pre.
      apply Htc'.
      assumption.
    + assumption.
Qed.

Lemma correct_proc :
  forall cl ps,
    tc_p cl ps ->
    hoare_triple_proc_ctx ps cl.
Proof.
  intros cl ps Htc.
  unfold hoare_triple_proc_ctx.
  intros.
  apply correct.
  * apply Htc.
  * apply Htc.
Qed.
