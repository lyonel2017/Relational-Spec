From Rela Require Import Com.
From Rela Require Import Sem.
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

(** Definition of Postcondition **)

Definition postcondition : Type := sigma -> sigma -> Prop.

Definition empty_postcondition :  postcondition := (fun _ _ => True).

(** Definition of functional correcness / Hoare Triples / Partial correcness **)

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

Module SF.

  Lemma while_triple :
    forall (inv: assertion) (var: variant) b c ps l id si,
      hoare_triple (fun s => inv (s :: (si :: l)) /\ beval s b = true)
        (fun s' _ => inv (s' :: (si :: l))) c ps ->
      hoare_triple (fun s => inv (s :: (si :: l)))
        ( fun s' _ => inv (s' :: (si :: l)) /\ beval s'  b = false )
        (CWhile b c inv var id) ps.
  Proof.
    intros P var b c ps l id si Hhoare st st' HP Heval.
    remember (CWhile b c P var id) as original_command eqn:Horig.
    induction Heval; inversion Horig;subst;eauto.
  Qed.

End SF.

Definition bi_hoare (i: nat) (P: precondition) (Q: postcondition)
  (c : com) (b: bexp) (ps : Psi.psi) : Prop :=
  forall s s', P s -> ceval (unroll i b c) s ps s' -> Q s' s.

Lemma bi_uadruple_quadruple P Q p b inv var id ps:
  hoare_triple P Q (CWhile b p inv var id) ps <->
    forall n, bi_hoare n P Q p b ps.
Proof.
  unfold hoare_triple, bi_hoare;split;intros H.
  * intros i s s' Pre Heval.
    eapply H.
    apply Pre.
    eapply unroll_n_ceval; apply Heval.
  * intros s s' Pre Heval.
    eapply ceval_unroll_n in  Heval.
    destruct Heval.
    eapply (H x).
    apply Pre.
    assumption.
Qed.

Lemma while_triple :
  forall (inv: assertion) (var: variant) b c ps l id si,
    hoare_triple (fun s => inv (s :: (si :: l)) /\ beval s b = true)
      (fun s' _ => inv (s' :: (si :: l))) c ps ->
    hoare_triple (fun s => inv (s :: (si :: l)))
      (fun s' _ => inv (s' :: (si :: l)) /\ beval s'  b = false)
      (CWhile b c inv var id) ps.
Proof.
  intros P var b c ps l id si Hhoare.
  apply bi_uadruple_quadruple.
  intros n.
  induction n;intros st st' HPre Heval.
  - apply ceval_inf_loop in Heval; now auto.
  - inversion Heval; subst.
    inversion H6; subst.
    eauto.
    inversion H6; subst.
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

Module Phi.

  Definition phi : Type := Proc.t -> clause.

  Definition empty_phi: phi := fun _ => empty_clause.

End Phi.

Lemma empty_hoare p c ps:
  hoare_triple (get_pre (Phi.empty_phi p))
    (get_post (Phi.empty_phi p)) c ps.
Proof.
  intros s s' HPre He.
  simpl.
  unfold empty_postcondition;auto.
Qed.

(** Defintion of a Hoare Triple with inliner **)

Definition i_hoare_triple (n: nat)
  (P: precondition) (Q: postcondition)
  (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval c s (Inline1.k_inliner_ps n ps) s'  -> Q s' s.

Lemma i_hoare_triple_hoare_triple :
  forall P Q p ps,
    hoare_triple P Q (CCall p) ps <-> forall n, i_hoare_triple n P Q (CCall p) ps.
Proof.
  unfold hoare_triple, i_hoare_triple;split;intros H.
  * intros n s s' Pre Heval.
    eapply H.
    apply Pre.
    eapply (Inline1.n_inline_ps_ceval _ _ _ _ _ Heval).
  * intros s s' HPre Heval.
    apply Inline1.ceval_n_inline_ps in Heval.
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
    + apply Inline1.n_inline_ps_inline in Heval.
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

Import AexpNotations.
Import BexpNotations.
Import ComNotations.

Section Loop_Proc.
  Variable c : com.
  Variable b: bexp.

  Definition w: com :=
    <[ if {b} then
         {c};
         call(1)
       else
         skip
       end ]>.

  Definition ps (x': Proc.t) :=
    if Proc.eqb x' 1 then  w else Psi.empty_psi x'.

  Variable invar: assertion.

  Variable var: variant.

  Variable l : list sigma.

  Definition pre : precondition := fun s => invar (s :: l).

  Definition post : postcondition := fun s' _ => invar (s' :: l) /\ beval s'  b = false.

  Definition cl (f' : Proc.t) : clause :=
    if (Proc.eqb f' 1)
    then (pre,post)
    else Phi.empty_phi f'.

  Lemma recursive_proc_1:
    hoare_triple_proc_ctx cl ps ->
    hoare_triple (get_pre (cl 1)) (get_post (cl 1)) (CCall 1) ps.
  Proof.
    intros.
    specialize (recursive_proc ps cl H 1).
    auto.
  Qed.

  Lemma inv_proc :
    (forall ps, hoare_triple (fun s => invar (s :: l) /\ beval s b = true)
      (fun s' _ => invar (s' :: l)) c ps) ->
    hoare_triple (get_pre (cl 1)) (get_post (cl 1)) (CCall 1) ps.
  Proof.
    intros.
    apply recursive_proc_1.
    unfold cl, ps, pre,post.
    unfold hoare_triple_proc_ctx.
    unfold hoare_triple_ctx.
    intros.
    destruct (Proc.eqb p 1) eqn: He.
    - unfold w.
      intros s s' HPre Heval.
      simpl.
      inversion Heval;subst.
      + inversion H8;subst.
        specialize (H0 1).
        simpl in H0.
        eapply H0.
        eapply H.
        eauto.
        eauto.
        auto.
      + inversion H8; subst.
        auto.
    - simpl.
      unfold empty_postcondition.
      intros s s' HPre Heval.
      auto.
  Qed.

End Loop_Proc.
