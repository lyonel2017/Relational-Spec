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

Theorem correct :
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
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2.
    apply H. apply H2. inversion H3;subst. reflexivity.
  * intros P Q Htc' Htc Hproc. eapply seq_hoare_triple2.
    apply IHp1; [ apply Htc' | | apply Hproc].
    - intros.
      apply (consequence_tc_suite _ _ _ 
      (fun m' => tc' p2 m' cl /\ tc p2 m' cl (fun m'' => Q m''))).
      + intros s H0 s''.
        generalize dependent H0.
        generalize dependent s''.
        generalize dependent s.
        apply IHp2.
        ** intros. apply H0.
        ** intros. apply H0.
        ** apply Hproc.
      + apply tc_split.
        ** apply Htc'. apply H.
        ** apply Htc. apply H.
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
 * intros P Q Htc' Htc.
   specialize (IHp (fun s => inv s /\ beval s b = true) inv).
   intros Hproc s s' Pre Heval.
   specialize (Htc' s Pre).
   simpl in Htc'.
   destruct Htc'.
   specialize (Htc s Pre H).
   assert (H1 : inv s' /\ beval s' b = false -> Q s').
   { intros. apply Htc. apply H1. apply H1. }
   apply H1.
   generalize Heval.
   generalize H.
   apply while_hoare_triple.
   destruct H0.
   apply IHp.
   ** intros.
      apply H0.
      destruct H3.
      apply bexp_eval_true in H4.
      assumption.
      apply H3.
   ** intros.
      apply H2.
      destruct H3.
      apply bexp_eval_true in H4.
      assumption.
      apply H3.
   ** assumption.
 * intros P Q Htc' Htc Hproc.
   intros s s' Pre Heval.
   specialize (Htc' s Pre).
   specialize (Htc s Pre).
   apply Htc; [apply Htc' | ].
   generalize Heval.
   generalize dependent Htc'.
   apply Hproc.
Qed.

(** Proof that one can use a verification condition 
    generator to proof procedure contract **)

Theorem correct_proc :
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