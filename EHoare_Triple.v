From Rela Require Import EVcg.

Locate set.

From Rela Require Import ECom.
From Rela Require Import Bexp.
From Rela Require Import Lambda.
From Rela Require Import Label.
From Rela Require Import Sigma.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

Definition hoare_triple_c (P Q: assertion) (c : com) (l: Label.t) (ps : Psi.psi) : Prop :=
  forall s la s',  P s la -> ceval_c c s la l ps s' -> Q s' (l |-> s ; la ).

Definition hoare_triple_p (P Q: assertion) (p : prog) (ps : Psi.psi) : Prop :=
  forall s la s' la',  P s la -> ceval_p p s la ps s' la' -> Q s' la'.

Definition clause_p (P Q: assertion) (p : prog) (l: Label.t) (ps : Psi.psi) : Prop :=
  forall s la s' la',  P s la -> ceval_p p s (l |-> s ; la ) ps s' la' -> Q s' (l |-> s ; la ).
  
  (*clause et hoare ne sont pas compatible*)

Lemma seq_hoare_triple :
forall c l p ps (P Q R: assertion),
hoare_triple_c P R c l ps ->
hoare_triple_p R Q p ps ->
hoare_triple_p P Q (pconst l c p) ps.
Proof.
unfold hoare_triple_c.
unfold hoare_triple_p.
intros c l p ps P Q R H1 H2 s la s' la' Pre H12. inversion H12; subst.
eapply H2. eapply H1. apply Pre. apply H9. apply H10.
Qed.

Definition bassn b :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false ->  ~((bassn b) st).
Proof. congruence. Qed.

Lemma if_hoare_triple :
forall p1 p2 l b ps (P Q: assertion),
clause_p (fun s la => P s la /\ beval s b = true) Q p1 l ps ->
clause_p (fun s la => P s la /\ beval s b = false) Q p2 l ps ->
hoare_triple_c P Q (CIf b p1 p2) l ps.
Proof.
intros p1 p2 l b ps P Q HTrue HFalse s la s' HP HE.
inversion HE;subst. 
- unfold clause_p in HTrue.
  eapply HTrue.
  + split. 
      * apply HP. 
      * assumption.
  + apply H8.
- unfold clause_p in HFalse.
  eapply HFalse.
  + split. 
      * apply HP. 
      * assumption.
  + apply H8.
Qed.

Definition well_c (c : com) : Prop :=
match c with
| CSkip => True
| _ => False
end.

Fixpoint well_p (p : prog) : Prop :=
match p with 
| pnil => True
| pconst _ c q => well_c c /\ well_p q
end.

Lemma correct :
forall p ps pi,
well_p p ->
forall (P Q: assertion),
(forall m la, P m la -> tp p la m pi (fun m' la' => Q m' la')) -> 
hoare_triple_p P Q p ps.
Proof.
intros p ps pi.
elim p using prog_com_ind with 
  (P :=  fun c : com =>
  well_c c ->
  forall l (P Q: assertion),
  (forall la m m', P m la ->  tc c l la m m' pi (Q  m' (l |-> m ; la ))) -> 
    hoare_triple_c P Q c l ps).
* intros. unfold hoare_triple_c. intros. apply (H0 la s s').
  + assumption.
  + inversion H2;subst. reflexivity.
* intros. unfold hoare_triple_c. intros. apply (H0 la s s').
  + assumption.
  + inversion H2;subst. 
    unfold set.
 
    unfold update_sigma.
    (* reflexivity. *) contradiction H.
* intros.  contradiction H.
* intros. contradiction H1. (*apply if_hoare_triple.*)
  
* intros. contradiction H0.
* intros. unfold hoare_triple_p. intros. eapply H0. inversion H2;subst. assumption.
* intros.
  apply (seq_hoare_triple _ _ _ _ _ _ 
    (fun m la => tp p0 la m pi (fun (m'0 : sigma) (la' : lambda) => Q m'0 la'))).
  +  apply H.
    - simpl in H1. destruct H1. assumption.
    - intros. simpl in H2. apply H2. assumption. 
  + apply H0. 
    - simpl in H1. destruct H1. assumption.
    - eauto.
Qed.

Lemma seq_vc :
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
Abort.

  