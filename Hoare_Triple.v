From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Loc.
Import Why3_Set.

(*Defintion of a Hoare Triple*)

Definition hoare_triple (P Q: assertion) (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval c s ps s' -> Q s'.

(* Some facts about Hoare Triples *)

Lemma seq_hoare_triple :
forall p1 p2 ps (P Q R: assertion),
hoare_triple P R p1 ps ->
hoare_triple R Q p2 ps ->
hoare_triple P Q (CSeq p1 p2) ps.
Proof.
unfold hoare_triple.
intros p1 p2 ps P Q R H1 H2 s s' Pre H12. inversion H12; subst.
eapply H2. eapply H1. apply Pre. apply H3. apply H7.
Qed.

Lemma if_hoare_triple :
forall p1 p2 b ps (P Q: assertion),
hoare_triple (fun s => P s /\ beval s b = true) Q p1 ps ->
hoare_triple (fun s => P s /\ beval s b = false) Q p2 ps ->
hoare_triple P Q (CIf b p1 p2) ps.
Proof.
intros p1 p2 b ps P Q HTrue HFalse s s' HP HE.
inversion HE;subst. 
- unfold hoare_triple in HTrue.
  eapply HTrue.
  + split. 
      * apply HP. 
      * assumption.
  + apply H6.
- unfold hoare_triple in HFalse.
  eapply HFalse.
  + split. 
      * apply HP. 
      * assumption.
  + apply H6.
Qed.

Lemma consequence_hoare_pre :
forall p ps (P P' Q: assertion),
hoare_triple P' Q p ps ->
(forall s, P s -> P' s)->
hoare_triple P Q p ps.
Proof.
unfold hoare_triple.
intros.
eapply H.
apply H0.
apply H1.
apply H2.
Qed.

Lemma consequence_hoare_post :
forall p ps (P Q Q': assertion),
hoare_triple P Q' p ps ->
(forall s, Q' s -> Q s)->
hoare_triple P Q p ps.
Proof.
unfold hoare_triple.
intros.
apply H0.
eapply H.
apply H1.
apply H2.
Qed.

(* Proof that one can use a verification condition generator to proof Hoare Triples *)

Lemma correct :
forall p ps,
forall (P Q: assertion),
(forall m, P m -> tc' p m ps) ->
(forall m, P m -> tc p m ps Q) ->
hoare_triple P Q p ps.
Proof.
intros p ps.
induction p.
* unfold hoare_triple. intros. eapply H0. apply H1. inversion H2;subst. reflexivity.
* unfold hoare_triple. intros. eapply H0. apply H1. inversion H2;subst. reflexivity.
* unfold hoare_triple. intros. eapply H0. apply H1. 
  apply H. apply H1. inversion H2;subst. reflexivity. 
* intros. eapply seq_hoare_triple.
  + apply IHp1.
    - apply H.
    - simpl in H0, H.
     intros.
     specialize (H m H1).
     destruct H.
     specialize (H0 m H1). 
     specialize 
     (tc_split p1 ps m (fun m' : sigma => tc' p2 m' ps) (fun m' : sigma => tc p2 m' ps Q)).
     intros.
     apply H3. assumption. assumption.
  + apply IHp2.
    - intros. destruct H1. assumption.
    - intros. destruct H1. assumption.
* intros. apply if_hoare_triple.
  + apply IHp1.
    - intros. apply H. apply H1. apply H1.
    - intros. simpl in H. destruct H1. specialize (H0 m H1). destruct H0.
      apply H0. apply bexp_eval_true. assumption.
  + apply IHp2.
    - intros. apply H. apply H1. destruct H1. apply bexp_eval_false in H2. apply H2.
    - intros. simpl in H. destruct H1. specialize (H0 m H1). destruct H0.
      apply H3. apply bexp_eval_false. assumption.
 Qed.

(* Examples of proofs of Hoare Triples *)

Example Hoare1 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) plus2 Psi.empty_psi.
Proof.
apply correct.
+ simpl;intros. auto.
+ simpl;intros.
  rewrite H0.
  rewrite H.
  simpl.
  apply set'def.
  reflexivity.
Qed.

Definition plus3 : com := CSeq (CAss EAX (APlus (AId EAX) (ANum 2)))
                                (CAss EAX (APlus (AId EAX) (ANum 2))).

Example Haore2 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 5) plus3 Psi.empty_psi.
Proof.
apply correct.
+ simpl;intros. auto.
+ simpl;intros.
  rewrite H1.
  rewrite H0.
  rewrite H.
  simpl.
  apply set'def.
  reflexivity.
Qed.

Definition if2 : com := CIf (BEq (AId EAX) (ANum 4)) plus2 plus2.

Example Hoare3 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) if2 Psi.empty_psi .
Proof.
apply correct.
+ simpl; intros.
  auto.
+ simpl;intros.
  destruct (beval m (BEq (AId EAX) (ANum 4))) eqn:Hcond.
  * split;intros.
    - rewrite H1.
      rewrite H.
      apply set'def.
      reflexivity.
    - apply bexp_eval_true in Hcond.
      contradiction H0.
   * split;intros.
    - apply bexp_eval_false in Hcond.
      contradiction H0.
    - rewrite H1.
      rewrite H.
      apply set'def.
      reflexivity.
Qed.

Definition if3 : com := CSeq (CAss EAX (APlus (AId EAX) (ANum 2)))
                            (CSeq (CIf (BEq (AId EAX) (ANum 4)) plus2 plus2) plus2).

Example Hoare4 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 7) if3 Psi.empty_psi.
Proof.
apply correct.
+ simpl;intros. auto.
+ simpl;intros.
  destruct (beval m' (BEq (AId EAX) (ANum 4))) eqn:Hcond.
  * split;intros.
    - rewrite H3.
      rewrite H2.
      rewrite H0.
      rewrite H.
      apply set'def.
      reflexivity.
    - apply bexp_eval_true in Hcond.
      contradiction H1.
  * split;intros.
    - apply bexp_eval_false in Hcond.
      contradiction H1.
    - rewrite H3.
      rewrite H2.
      rewrite H0.
      rewrite H.
      apply set'def.
      reflexivity.
Qed.

Definition assert3 : com := CSeq (CAssert (fun m => m EAX = 2))
                          (CAssert (fun m => m EAX = 2)).
                          
Example Hoare6 : hoare_triple (fun m => m EAX = 2) (fun _ => True) assert3 Psi.empty_psi.
Proof.
apply correct.
+ simpl;intros.
  split.
   * assumption.
   * intros.
      rewrite <- H1.
      assumption.
+ simpl; intros. auto.
Qed.

Definition if4 : com := CIf (BEq (AId EAX) (ANum 2)) (CAssert (fun m => m EAX = 2)) CSkip.

Example Hoare7 : hoare_triple (fun m => m EAX = 2) (fun m' => m' EAX = 2) if4 Psi.empty_psi.
Proof.
apply correct.
+ simpl;intros. 
  split.
    * intros.
      assumption.
    * auto.
+ simpl;intros.
  destruct (beval m (BEq (AId EAX) (ANum 2))) eqn:Hcond.
  * split;intros.
    - rewrite <- H2.
      assumption.
    - apply bexp_eval_true in Hcond.
      contradiction H0.
  * split;intros.
    - apply bexp_eval_false in Hcond.
      contradiction H0.
    - rewrite <- H1.
      assumption.
Qed.