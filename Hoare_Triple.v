From Rela Require Import EBexp.
From Rela Require Import ECom.
From Rela Require Import Sigma.
From Rela Require Import Lambda.
From Rela Require Import Vcg.
From Rela Require Import Label.

Parameter i :nat.

Definition ceval_f_i_p (s : sigma) (la: lambda) (ps: Psi.psi) (p : prog) (Q : lambda -> Prop) := 
  match ceval_prog s la ps p i True with
  | None => True
  | Some (s',_) => Q (Post |-> s' ; (Pre |-> s ; la ))
  end.

Definition hoare_triple_p (P Q: lambda -> Prop) (p : prog) (ps : Psi.psi) : Prop :=
  forall s la,  P (Pre |-> s ; la ) ->  ceval_f_i_p s la ps p Q .

Definition ceval_f_i_c (s : sigma) (la: lambda) (l: Label.t) (ps: Psi.psi) (c : com) (Q : lambda -> Prop) := 
  match ceval_com s l la ps c i True with
  | None => True
  | Some (s',_) => Q (Post |-> s' ; (Pre |-> s ; la ))
  end.

Definition hoare_triple_c (P Q: lambda -> Prop) (c : com) (l: Label.t) (ps : Psi.psi) : Prop :=
  forall s la,  P (Pre |-> s ; la ) ->  ceval_f_i_c s la l ps c Q.

Fixpoint well_c (c : com) : Prop :=
match c with
| CSkip => True
| _ => False
end
with well_p (p : prog) : Prop :=
match p with 
| pnil => True
| pconst _ c q => well_c c /\ well_p q
end.

Lemma correct :
forall p ps,
well_p p ->
forall (P Q: lambda -> Prop),
(forall la m m', P (Pre |-> m ; la ) -> tp p la m (fun m _ => m = m') ps -> Q (Post |-> m' ; (Pre |-> m ; la ))) -> 
hoare_triple_p P Q p ps.
Proof.
intros p ps.
elim p using prog_com_ind with 
  (P :=  fun c : com =>
  well_c c ->
  forall l (P Q: lambda -> Prop),
  (forall la m m', P (Pre |-> m ; la ) -> tc c l la m m' ps -> Q (Post |-> m' ; (Pre |-> m ; la ))) -> 
    hoare_triple_c P Q c l ps).
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i. 
  + simpl. auto.
  + simpl. simpl in H0. apply H0. assumption. reflexivity.
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i.
  + simpl. auto.
  + contradiction H.
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i.
  + simpl. auto.
  + contradiction H.
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i.
  + simpl. auto.
  + contradiction H1.
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i.
  + simpl. auto.
  + contradiction H0.
* intros. unfold hoare_triple_c. intros.  unfold ceval_f_i_c. destruct i.
  + simpl. auto.
  + contradiction H.
* intros. unfold hoare_triple_p. intros.  unfold ceval_f_i_p. destruct i.
  + simpl. auto.
  + simpl. apply H0. assumption.  reflexivity.
* intros. simpl in H2.



(* unfold hoare_triple_p. intros.  unfold ceval_f_i_p.  destruct i.
  + simpl. auto.
  + simpl. destruct n.
    - simpl. auto.
    - simpl in H2.*)
