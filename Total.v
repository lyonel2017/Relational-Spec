From Rela Require Import Com.
From Rela Require Import Inliner.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Proc.
From Rela Require Import Hoare_Triple.

From Coq Require Import Lists.List.
Import ListNotations.

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
    (forall s1, inv (s1 :: l) -> 0 <= var s1) ->
    total (fun s => inv (s :: l))
                (fun s' _ => inv (s' :: l) /\ beval s'  b = false)
                (CWhile b c inv var) ps.
Proof.
  intros P v b c ps l Hhoare Hvariant.
  apply hoare_total.
  - apply total_hoare in Hhoare.
    apply while_triple.
    intros s s' HPre Heval.
    apply (Hhoare s s' HPre Heval).
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
      replace (v st - v st) with 0 in H2;[| rewrite Proc.sub_diag;auto].
      assert (HPrex: P(x :: l) /\ beval x b = true). { split;repeat assumption. }
      specialize (Hhoare x HPrex).
      destruct Hhoare.
      Lia.lia.
    + apply E_WhileFalse.
      assumption.
Qed.

(** Total correcness for a com with procedure context **)

Definition total_ctx (cl : Phi.phi) (ps: Psi.psi)
  (P: precondition) (Q: postcondition)  (c: com) :=
  (forall p, total (get_pre (cl p)) (get_post (cl p)) (CCall p) ps) -> total P Q c ps.

(** Total correcness for a procedure with procedure context **)

Definition total_proc_ctx (var: variant) (cl : Phi.phi) (ps_init :Psi.psi) :=
  forall v p ps,
    (forall p, total (fun s => get_pre (cl p) s /\ var s + 1 = v)
            (get_post (cl p))
          (CCall p) ps) ->
    total (fun s => get_pre (cl p) s /\ var s = v) (get_post (cl p))
      (ps_init p) ps.

(** Definition with inliner for total correcness **)

Definition i_total (n: nat)
  (P: precondition) (Q: postcondition)
  (c : com) (ps : Psi.psi) : Prop :=
  forall s ,  P s -> (exists s', ceval (Inline2.k_inliner n c ps) s ps s' /\ Q s' s).

Definition total_proc_ctx_n (n : nat) (var: variant) (cl : Phi.phi) (ps :Psi.psi) :=
  forall v p,
    (forall p, total (fun s => get_pre (cl p) s /\ var s + 1 = v - n )
            (get_post (cl p))
          (CCall p) ps) ->
    i_total n (fun s => get_pre (cl p) s /\ var s = v) (get_post (cl p))
      (CCall p) ps.

Lemma total_proc_ctx_total_proc_ctx_n (var: variant) (cl : Phi.phi) (ps :Psi.psi) :
  total_proc_ctx var cl ps -> forall n, total_proc_ctx_n n var cl ps.
Proof.
  intros H.
  induction n;intros v p H0 s HPre.
  - rewrite Proc.sub_0_r in H0.
    specialize (H v p ps H0 s HPre).
    destruct H.
    destruct H.
    exists x.
    split;[|auto].
    apply E_Call.
    apply H.
  -
    assert (Hi: forall p,
               total (fun s : sigma => get_pre (cl p) s /\ var s + 1 = v )
                 (get_post (cl p)) (CCall p) ps).
    { intros p0 s0 HP.
      specialize (IHn (v - 1) p0).
      replace (v - 1 - n ) with (v - S n ) in IHn by Lia.lia.
      destruct HP.
      apply Proc.add_sub_eq_r in H2.
      symmetry in H2.
      assert (HP : get_pre (cl p0) s0 /\ var s0 = v - 1) by auto.
      specialize (IHn H0 s0 HP).
      destruct IHn.
      exists x.
      destruct H3.
      apply Inline2.n_inline_ceval_ceval in H3.
      split; [apply H3 |  apply H4] .
    }
    specialize (H v p ps Hi s HPre).
    destruct H.
    exists x.
    split;[|apply H].
    apply Inline2.ceval_n_inline_ceval.
    apply E_Call.
    apply H.
Qed.

Lemma total_recursive_proc var ps cl:
    (forall n, total_proc_ctx_n n var cl ps) ->
   (forall p, total (get_pre (cl p)) (get_post (cl p)) (CCall p) ps).
Proof.
  intros.
  intros s Hpre.
  assert (H1:  (forall p : Proc.t,
                   total (fun s0 : sigma => get_pre (cl p) s0 /\ var s0 + 1 = var s - var s)
                     (get_post (cl p)) (CCall p) ps)).
  { intros.
    intros s' HP.
    Lia.lia. }
  assert (HP:  get_pre (cl p) s /\ var s = var s);auto.
  specialize (H (var s) (var s) p H1 s HP).
  destruct H.
  exists x.
  destruct H.
  split;[|auto].
  apply Inline2.n_inline_ceval_ceval in H.
  eauto.
Qed.

(** Modular Verification of Total correcness **)

Theorem recursion_total :
  forall P Q p var ps cl,
    total_proc_ctx var cl ps  ->
    total_ctx cl ps P Q p ->
    total P Q p ps.
Proof.
intros.
apply H0.
eapply total_recursive_proc.
apply total_proc_ctx_total_proc_ctx_n.
apply H.
Qed.
