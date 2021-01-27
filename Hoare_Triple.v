From Rela Require Import Vcg.

Locate set.

From Rela Require Import Com.
From Rela Require Import Bexp.
From Rela Require Import Lambda.
From Rela Require Import Label.
From Rela Require Import Sigma.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

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

Fixpoint well (c : com) : Prop :=
match c with
| CSkip => True
| CSeq p1 p2 => well p1 /\ well p2
| CIf _ p1 p2 => well p1 /\ well p2
| _ => False
end.

Lemma correct :
forall p ps pi,
well p ->
forall (P Q: assertion),
(forall m, P m -> tc p m pi (fun m' => Q m')) -> 
hoare_triple P Q p ps.
Proof.
intros p ps pi well.
induction p.
* unfold hoare_triple. intros. eapply H. apply H0. inversion H1;subst. reflexivity.
* contradiction well.
* contradiction well.
* intros. eapply seq_hoare_triple.
  + apply IHp1.
    - simpl in well. destruct well. assumption.
    - simpl in H. apply H.
   + apply IHp2.
    - simpl in well. destruct well. assumption.
    - eauto.
* intros. apply if_hoare_triple.
  +  apply IHp1.
    - simpl in well. destruct well. assumption.
    - intros. simpl in H. destruct H0. specialize (H m H0). destruct H.
    ** apply H2.
    ** apply bexp_eval_true in H1. contradiction H1.
  +  apply IHp2.
    - simpl in well. destruct well. assumption.
    - intros. simpl in H. destruct H0. specialize (H m H0). destruct H.
    ** apply bexp_eval_false in H1. contradiction H1.
    ** apply H2.
 Qed.

(************ TRASH **************************)

(*Lemma seq_vc :
forall c l p ps (P Q R: lambda -> Prop),
forall la m m' m'',  
((P (Pre |-> m ; la ) -> tc c l la m m'' ps -> R (Post |-> m'' ; (Pre |-> m ; (l |-> m ; la ) ))) /\ 
(R (Post |-> m'' ; (Pre |-> m ; (l |-> m ; la ) )) -> tp p (l |-> m ; la ) m'' (fun (m0 : sigma) (_ : lambda) => m0 = m') ps -> Q (Post |-> m' ; (Pre |-> m ; la )))) ->
(P (Pre |-> m; la) -> tp (pconst l c p) la m (fun (m0 : sigma) (_ : lambda) => m0 = m') ps -> Q (Post |-> m'; Pre |-> m; la)).
Proof.
intros c l p ps P Q R la m m' m'' H Pre H12.
simpl in H12.
specialize (H12 m'').
destruct H12.
destruct H.
apply H2.
apply H.
all: try assumption.
Abort.*)