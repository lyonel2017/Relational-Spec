From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Bexp.
From Rela Require Import Sigma.


Definition hoare_triple (P Q: assertion) (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval c s ps s' -> Q s'.

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

Lemma correct :
forall p ps pi,
forall (P Q: assertion),
(forall m, P m -> tc p m pi Q) -> 
hoare_triple P Q p ps.
Proof.
intros p ps pi.
induction p.
* unfold hoare_triple. intros. eapply H. apply H0. inversion H1;subst. reflexivity.
* unfold hoare_triple. intros. eapply H. apply H0. inversion H1;subst. reflexivity.
* intros. eapply seq_hoare_triple.
  + apply IHp1. simpl in H. apply H.
  + apply IHp2. eauto.
* intros. apply if_hoare_triple.
  +  apply IHp1.
    intros. simpl in H. destruct H0. specialize (H m H0). destruct H.
    apply H. apply bexp_eval_true. assumption.
  +  apply IHp2.
    intros. simpl in H. destruct H0. specialize (H m H0). destruct H.
    apply H2. apply bexp_eval_false. assumption.
 Qed.