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

(** Defintion of functional correcness i.e Hoare Triples **)

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
  forall (inv: assertion) (var: variant) b c ps l,
    (forall s1 s2, inv (s1 :: l) /\ beval s1 b = true ->
                     ceval c s1 ps s2 -> inv (s2 :: l)) ->
    hoare_triple (fun s => inv (s :: l))
                ( fun s' _ => inv (s' :: l) /\ beval s'  b = false )
                (CWhile b c inv var) ps.
Proof.
  intros P var b c ps l Hhoare st st' HP Heval.
  remember (CWhile b c P var) as original_command eqn:Horig.
  induction Heval; inversion Horig.
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

(** Defintion of contract environments : *)
(*     a map from procedure name to clauses **)

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
  eapply (n_inline_ps_ceval _ _ _ _ _ Heval).
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
- intros p s s' HPre Heval.
  inversion Heval;subst.
  apply ceval_inf_loop in H1.
  contradiction H1.
- intros p s s' HPre Heval.
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
eapply (recursive_proc _ _ H).
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

(** Definition of total correcness **)

Definition total (P : precondition) (Q: postcondition) (c : com) (ps : Psi.psi) : Prop :=
  forall s ,  P s -> (exists s', ceval c s ps s' /\ Q s' s).

(** Facts about Hoare Triples **)

Lemma hoare_total (P : precondition) (Q: postcondition) (c : com) (ps : Psi.psi) :
  hoare_triple P Q c ps ->
 (forall s ,  P s -> (exists s', ceval c s ps s')) ->
 total P Q c ps.
Proof.
  intros Hp Hf s HPre.
  specialize (Hf s HPre).
  destruct Hf.
  exists x. split. assumption.
  apply (Hp _ _ HPre H).
Qed.

Lemma total_hoare (P : precondition) (Q: postcondition) (c : com) (ps : Psi.psi) :
 total P Q c ps ->
 hoare_triple P Q c ps.
Proof.
  intros Ht s s' HPre Heval.
  specialize (Ht s HPre).
  destruct Ht.
  destruct H.
  erewrite (ceval_det s _ _ s' x).
  apply H0.
  apply Heval.
  apply H.
Qed.

(** Function for recursive loop unrolling **)

Fixpoint unroll n b p :=
  match n with
  | 0 => CSkip
  | S n => CSeq (unroll n b p) (CIf b p CSkip)
  end.

Lemma total_unroll_c (inv: assertion) (var: variant) b c ps l:
    total (fun s1 => inv (s1 :: l) /\ beval s1 b = true)
      (fun s2 s1 => inv (s2 :: l) /\ var s2 < var s1) c ps ->
    forall n,
    total (fun s1 => inv (s1 :: l) /\ beval s1 b = true)
      (fun s2 s1 => inv (s2 :: l) /\ (beval s2 b = true -> var s2 <= var s1 - n))
      (unroll n b c) ps.
Proof.
  intros.
  induction n;intros s HPre.
  - exists s. simpl.
    split.
    + apply E_Skip.
    + auto. split. apply HPre. Lia.lia.
  - specialize (IHn s HPre).
    destruct IHn.
    destruct (beval x b) eqn : Hbx.
    + assert (HPrex: inv (x :: l) /\ beval x b = true).
      { split;[ apply H0 | assumption ]. }
      specialize (H x HPrex).
      destruct H.
      exists x0;simpl.
      split.
      * eapply E_Seq.
        -- apply H0.
        -- apply E_IfTrue;[assumption|apply H].
      * split. apply H. Lia.lia.
    + exists x;simpl.
      split.
      * eapply E_Seq.
        -- apply H0.
        -- apply E_IfFalse ;[assumption|apply E_Skip].
      * split.
        -- apply H0.
        -- intros. rewrite H1 in Hbx. inversion Hbx.
Qed.

Lemma unroll_while_while n b c P v ps: forall s s',
   ceval (CSeq (unroll n b c) (CWhile b c P v)) s ps s' ->
   ceval (CWhile b c P v) s ps s'.
Proof.
  induction n;intros.
  - simpl in H.
    inversion H;subst.
    inversion H2;subst.
    assumption.
  - apply IHn.
    inversion H;subst.
    inversion H2;subst.
    eapply E_Seq.
    apply H3.
    inversion H8;subst.
    + eapply E_WhileTrue.
      apply H10.
      apply H11.
      apply H6.
    + inversion H11;subst.
      apply H6.
Qed.

Lemma while_total :
  forall (inv: assertion) (var: variant) b c ps l,
    total (fun s1 => inv (s1 :: l) /\ beval s1 b = true)
          (fun s2 s1 => inv (s2 :: l) /\ var s2 < var s1) c ps ->
    (forall s1, inv (s1 :: l) -> 1 <= var s1) ->
    total (fun s => inv (s :: l))
                (fun s' _ => inv (s' :: l) /\ beval s'  b = false)
                (CWhile b c inv var) ps.
Proof.
  intros P v b c ps l Hhoare Hvariant.
  apply hoare_total.
  - apply total_hoare in Hhoare.
    apply while_triple.
    apply Hhoare.
  - intros st HPre.
    destruct (beval st b) eqn: Hb;[ | exists st; apply E_WhileFalse; assumption].
    assert (HPreb: P(st :: l) /\ beval st b = true). { split;repeat assumption. }
    specialize (total_unroll_c _ _ _ _ _ _ Hhoare (v st) st HPreb).
    intros.
    destruct H.
    exists x.
    apply (unroll_while_while (v st)).
    eapply E_Seq.
    apply H.
    destruct (beval x b) eqn: Hbx.
    + destruct H.
      destruct H0.
      specialize (Hvariant x H0).
      assert (H2: v x <= v st - v st).
      { apply H1. reflexivity. }
      replace (v st - v st) with 0 in H2.
      Lia.lia.
      Search( _ - _ = 0).
      rewrite Proc.sub_diag.
      reflexivity.
    + apply E_WhileFalse.
      assumption.
Qed.


(* Lemma func_total : *)
(*   forall (inv: assertion) (var: variant) b c ps l, *)
(*     total (fun s1 => inv (s1 :: l) /\ beval s1 b = true) *)
(*           (fun s2 s1 => inv (s2 :: l) /\ var s2 < var s1) c ps -> *)
(*     (forall s1, inv (s1 :: l) -> 1 <= var s1) -> *)
(*     total (fun s => inv (s :: l)) *)
(*                 (fun s' _ => inv (s' :: l) /\ beval s'  b = false) *)
(*                 (CWhile b c inv var) ps. *)
(* Proof. *)
