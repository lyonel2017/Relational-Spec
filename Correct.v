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

(** Examples of proofs of Hoare Triples **)

Import ComNotations.
Import AexpNotations.
Import BexpNotations.

Example Hoare1 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) plus2 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros. auto.
  + simpl;intros.
    rewrite H0.
    rewrite H.
    simpl.
    apply set'def.
    reflexivity.
Qed.

Definition plus3 : com := <[ °EAX := EAX + 2; °EAX := EAX + 2 ]>.

Example Haore2 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 5) plus3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros. auto.
  + simpl;intros.
    rewrite H1.
    rewrite H0.
    rewrite H.
    simpl.
    apply set'def.
    reflexivity.
Qed.

Definition if2 : com := <[ if EAX = 4 then { plus2 } else { plus2 } end ]>.

Example Hoare3 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) if2 Psi.empty_psi .
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl; intros. auto.
  + simpl;intros.
    destruct (beval m (BEq (AId EAX) (ANum 4))) eqn:Hcond.
    - split;intros.
      ** rewrite H1.
         rewrite H.
         apply set'def.
         reflexivity.
      ** apply bexp_eval_true in Hcond.
         contradiction H0.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H0.
      ** rewrite H1.
         rewrite H.
         apply set'def.
         reflexivity.
Qed.

Definition if3 : com := <[ EAX := EAX + 2 ; 
                          if EAX = 4 then { plus2 } else { plus2 } end; 
                          { plus2 } ]>.

Example Hoare4 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 7) if3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* eapply correct.
  + simpl;intros. auto.
  + simpl;intros.
    destruct (beval m' (BEq (AId EAX) (ANum 4))) eqn:Hcond.
    - split;intros.
      ** rewrite H3.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply set'def.
         reflexivity.
      ** apply bexp_eval_true in Hcond.
         contradiction H1.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H1.
      ** rewrite H3.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply set'def.
         reflexivity.
Qed.

Definition assert3 : com := <[ assert (fun m => m EAX = 2) ; 
                               assert (fun m => m EAX = 2) ]>.

Example Hoare6 : hoare_triple (fun m => m EAX = 2) (fun _ => True) assert3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros.
    split.
    - assumption.
    - intros.
      rewrite <- H1.
      assumption.
  + simpl; intros. auto.
Qed.

Definition if4 : com := <[ if EAX = 2 then assert (fun m => m EAX = 2) else skip end ]>.

Example Hoare7 : hoare_triple (fun m => m EAX = 2) (fun m' => m' EAX = 2) if4 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros.
    split.
    - intros.
      assumption.
    - auto.
  + simpl;intros.
    destruct (beval m (BEq (AId EAX) (ANum 2))) eqn:Hcond.
    - split;intros.
      ** rewrite <- H2.
         assumption.
      ** apply bexp_eval_true in Hcond.
         contradiction H0.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H0.
      ** rewrite <- H1.
         assumption.
Qed.