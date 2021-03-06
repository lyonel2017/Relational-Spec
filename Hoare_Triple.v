From Rela Require Import Com.
From Rela Require Import Inliner.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Proc.
From Coq Require Import Lists.List.
Import ListNotations.

(** Definition of Precondtion **)

Definition precondition : Type := sigma -> Prop.

Definition empty_precondition : precondition := (fun _ => False).

(** Definition of Postcondtion **)

Definition postcondition : Type := sigma -> sigma -> Prop.

Definition empty_postcondition :  postcondition := (fun _ _ => True).

(** Defintion of a Hoare Triple **)

Definition hoare_triple (P : precondition) (Q: postcondition) (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval c s ps s' -> Q s' s.

(** Facts about Hoare Triples **)

Lemma seq_hoare_triple :
  forall p1 p2 ps (P:precondition) (Q: postcondition),
    hoare_triple P (fun s' s => forall s'', ceval p2 s' ps s'' -> Q s'' s) p1 ps ->
    hoare_triple P Q (CSeq p1 p2) ps.
Proof.
  unfold hoare_triple.
  intros. inversion H1;subst.
  specialize (H s s'0 H0 H4).
  apply H.
  apply H8.
Qed.

Lemma if_hoare_triple :
  forall p1 p2 b ps (P: precondition) (Q: postcondition),
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

Lemma while_triple :
  forall (inv: assertion) b c ps l,
    (forall s1 s2, inv (s1 :: l) /\ beval s1 b = true -> 
                     ceval c s1 ps s2 -> inv (s2 :: l)) ->
    hoare_triple (fun s => inv (s :: l)) 
                ( fun s' _ => inv (s' :: l) /\ beval s'  b = false ) 
                (CWhile b c inv) ps.
Proof.
  intros P b c ps l st Hhoare st' HP Heval.
  remember (CWhile b c P) as original_command eqn:Horig.
  induction Heval; try inversion Horig.
  * inversion Horig;subst. eauto.
  * inversion Horig;subst.
    eauto.
Qed.

(** Definition of a procedure contract **)

Definition clause : Type := precondition * postcondition.

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition get_pre (an:clause) :=
          let (pre,post) := an in
          pre.

Definition get_post (an:clause) :=
          let (pre,post) := an in
          post.

(** Defintion of contract environments :
    a map from procedure name to clauses **)

Module Phi.

  Definition phi : Type := Proc.t -> clause.

  Definition empty_phi: phi := fun _ => empty_clause.

End Phi.

(** Defintion of a Hoare Triple with inliner **)

Definition i_hoare_triple (n: nat) 
  (P: precondition) (Q: postcondition) 
  (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval c s (k_inliner_ps n ps) s'  -> Q s' s.

Lemma i_hoare_triple_hoare_triple :
  forall P Q p ps,
  hoare_triple P Q p ps <-> forall n, i_hoare_triple n P Q p ps.
Proof.
unfold hoare_triple, i_hoare_triple;split;intros H.
* intros n s s' Pre Heval.
  eapply H.
  apply Pre.
  apply n_inline_ps_ceval in Heval.
  assumption.
* intros s s' HPre Heval.
  apply ceval_n_inline_ps in Heval.
  destruct Heval.
  eapply H.
  + apply HPre.
  + apply H0.
Qed.

(** Hoare triple for a com with procedure context **)

Definition hoare_triple_ctx (cl : Phi.phi) (ps: Psi.psi)
      (P: precondition) (Q: postcondition)  (c: com) :=
    (forall p, hoare_triple (get_pre (cl p)) (get_post (cl p)) (CCall p) ps) ->
      hoare_triple P Q c ps.

(** Hoare triple for a procedure with procedure context **)

Definition hoare_triple_proc_ctx (cl : Phi.phi) (ps_init :Psi.psi):=
  forall p ps, hoare_triple_ctx cl ps (get_pre (cl p)) (get_post (cl p)) (ps_init p).

Lemma recursive_proc ps cl:
    hoare_triple_proc_ctx cl ps ->
   (forall p, hoare_triple (get_pre (cl p)) (get_post (cl p)) (CCall p) ps).
Proof.
intros.
apply i_hoare_triple_hoare_triple.
intros n.
generalize dependent p.
induction n.
* intros p s s' HPre Heval.
  inversion Heval;subst.
  apply ceval_inf_loop in H1.
  contradiction H1.
* intros p s s' HPre Heval.
  eapply H.
  + apply IHn.
  + apply HPre.
  + apply n_inline_ps_inline in Heval.
    apply Heval.
Qed.

(** Modular Hoare Triple Verification **)

Theorem recursion_hoare_triple :
  forall P Q p ps cl,
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple_ctx cl ps P Q p ->
    hoare_triple P Q p ps.
Proof.
intros.
apply H0.
apply recursive_proc.
assumption.
Qed.

(** Corollaire from recursion_hoare_triple **)

Theorem procedure_hoare_triple :
  forall p cl ps,
    hoare_triple_proc_ctx cl ps  ->
    hoare_triple (get_pre (cl p)) (get_post (cl p)) (ps p) ps.
Proof.
intros.
apply recursion_hoare_triple with cl.
assumption.
apply H.
Qed.