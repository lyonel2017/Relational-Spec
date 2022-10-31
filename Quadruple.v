From Rela Require Import Proc.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.

From Coq Require Import Lia.
Import Arith.

(** Function for loop inlining in Com **)

Fixpoint inliner c inline:=
  match c with
  | CSeq p1 p2 => CSeq (inliner p1 inline) (inliner p2 inline)
  | CIf b p1 p2 => CIf b (inliner p1 inline) (inliner p2 inline)
  | CWhile b p inv => inline b p inv
  | _ => c
  end.

(** Function for recursive loop inlining in Com **)

Fixpoint k_inliner n c :=
  match n with
  | 0 => CWhile BTrue CSkip (fun _ => True)
  | S n' => inliner c (fun b p inv =>
                        k_inliner n' (CIf b (CSeq p (CWhile b p inv)) CSkip))
  end.

(** Some fact about the inlining **)

Lemma inline_cskip n : k_inliner (S n) CSkip = CSkip.
Proof.
  reflexivity.
Qed.

Lemma inline_cass n x a1: k_inliner (S n) (CAss x a1) = (CAss x a1).
Proof.
  reflexivity.
Qed.

Lemma inline_cassr n x a1: k_inliner (S n) (CAssr x a1) = (CAssr x a1).
Proof.
  reflexivity.
Qed.

Lemma inline_cassert n b: k_inliner (S n) (CAssert b) = (CAssert b).
Proof.
  reflexivity.
Qed.

Lemma inline_cseq n p1 p2: k_inliner (S n) (CSeq p1 p2) =
                           CSeq (k_inliner (S n) p1) (k_inliner (S n) p2).
Proof.
  reflexivity.
Qed.

Lemma inline_cif n b p1 p2: k_inliner (S n) (CIf b p1 p2) =
                            CIf b (k_inliner (S n)  p1)  (k_inliner (S n) p2).
Proof.
  reflexivity.
Qed.

Lemma inline_cwhile n p b inv: k_inliner (S n) (CWhile b p inv) =
                               k_inliner n (CIf b (CSeq p (CWhile b p inv)) CSkip).
Proof.
  reflexivity.
Qed.

Lemma inline_ccall n f:
  k_inliner (S n) (CCall f) = CCall f.
Proof.
  reflexivity.
Qed.

(* ceval is inlining insensitive on command *)

Definition inl b p inv := CIf b (CSeq p (CWhile b p inv)) CSkip.

Lemma ceval_inline p s ps s':
  ceval p s ps s' -> ceval (inliner p inl) s ps s'.
Proof.
  intros.
  induction H.
  + apply E_Skip.
  + apply E_Ass.
    all: try now auto.
  + apply E_Assr.
    all: try now auto.
  + apply E_Assert.
  + simpl. apply E_IfTrue; [now auto | now auto].
  + simpl. apply E_IfFalse; [now auto | now auto].
  + simpl. eapply E_Seq.
  - apply IHceval1.
  - apply IHceval2.
    + simpl. unfold inl. apply E_IfFalse. now auto. apply E_Skip.
    + simpl. unfold inl. apply E_IfTrue. now auto.
      eapply E_Seq.
  - apply H0.
  - apply H1.
    + simpl. apply E_Call. assumption.
Qed.

Lemma inline_ceval p s ps s':
  ceval (inliner p inl) s ps s' -> ceval p s ps s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent ps.
  induction p;intros.
  + inversion H;subst.
    apply E_Skip.
  + inversion H;subst.
    apply E_Ass. all: try now auto.
  + inversion H;subst.
    apply E_Assr. all: try now auto.
  + inversion H;subst.
    apply E_Assert.
  + inversion H;subst.
    eapply E_Seq.
    * apply IHp1. apply H2.
    * apply IHp2. apply H6.
  + inversion H;subst.
    * eapply E_IfTrue.
      assumption.
      apply IHp1. apply H7.
    * eapply E_IfFalse.
      assumption.
      apply IHp2. apply H7.
  + simpl in H. unfold inl in H.
    inversion H; subst.
    * inversion H7;subst.
      eapply E_WhileTrue.
      assumption.
      apply H2.
      apply H8.
    * inversion H7;subst.
      apply E_WhileFalse.
      assumption.
  +  simpl in H. assumption.
Qed.

(* ceval is "n" inlining insensitive on command *)

Lemma inline_n_ceval n p s ps s':
  ceval (k_inliner n p) s ps s' -> ceval p s ps s'.
Proof.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent p.
  induction n.
  * intros.
    apply ceval_inf_loop in H.
    contradiction H.
  * induction p;intros.
  + apply H.
  + apply H.
  + apply H.
  + apply H.
  + inversion H;subst.
    apply E_Seq with s'0.
  - apply IHp1.
    apply H2.
  - apply IHp2.
    apply H6.
    + inversion H;subst.
  - apply E_IfTrue.
    ** assumption.
    ** apply IHp1.
       assumption.
  - apply E_IfFalse.
    ** assumption.
    ** apply IHp2.
       assumption.
    + simpl in H.
      destruct n.
  -
    simpl in H.
    apply ceval_inf_loop in H.
    contradiction H.
  - apply IHn in H.
    inversion H;subst.
    ++ inversion H7;subst.
       eapply E_WhileTrue.
       assumption.
       apply H2.
       apply H8.
    ++ inversion H7;subst.
       apply E_WhileFalse.
       assumption.
    + simpl in H. assumption.
Qed.

Lemma inline_ceval_S n p s  s' ps:
  ceval (k_inliner n p) s ps s' ->
  forall m, n <= m -> ceval (k_inliner m p) s ps s'.
Proof.
  intros.
  generalize dependent s.
  generalize dependent s'.
  generalize dependent p.
  generalize dependent m.
  induction n.
  * intros.
    apply ceval_inf_loop in H.
    contradiction H.
  * destruct m as [| m].
  + intros. inversion H0.
  + induction p;intros.
  - apply H.
  - apply H.
  - apply H.
  - apply H.
  - rewrite inline_cseq in H.
    inversion H;subst.
    rewrite inline_cseq.
    apply E_Seq with s'0.
    ** apply IHp1.
       apply H3.
    ** apply IHp2.
       apply H7.
  - rewrite inline_cif in H.
    inversion H;subst.
    ** rewrite inline_cif.
       apply E_IfTrue.
    ++ assumption.
    ++ apply IHp1.
       apply H8.
       ** rewrite inline_cif.
          apply E_IfFalse.
    ++ assumption.
    ++ apply IHp2.
       apply H8.
  -      simpl in H.
         destruct n.
         **
           simpl in H.
           apply ceval_inf_loop in H.
           contradiction H.
         ** apply (IHn m) in H.
            apply H.
            now apply Le.le_S_n.
  - apply H.
Qed.

Lemma ceval_inline_n p s s' ps:
  ceval p s ps s' -> exists n, ceval (k_inliner n p) s ps s'.
Proof.
  induction 1;intros.
  * exists 1.
    apply E_Skip.
  * exists 1.
    apply E_Ass.
    all: try now auto.
  * exists 1.
    apply E_Assr.
    all: try now auto.
  * exists 1.
    apply E_Assert.
  * destruct IHceval as [n IH].
    exists n.
    destruct n.
  - apply ceval_inf_loop in IH.
    contradiction IH.
  - rewrite inline_cif.
    apply E_IfTrue.
    assumption.
    apply IH.
    * destruct IHceval as [n IH].
      exists n.
      destruct n.
  - apply ceval_inf_loop in IH.
    contradiction IH.
  - rewrite inline_cif.
    apply E_IfFalse.
    assumption.
    apply IH.
    * destruct IHceval1 as [n1 IH1].
      destruct IHceval2 as [n2 IH2].
      exists (max n1 n2).
      destruct n1 as [|n1].
    + apply ceval_inf_loop in IH1.
      contradiction IH1.
    + destruct n2 as [|n2].
  - apply ceval_inf_loop in IH2.
    contradiction IH2.
  - destruct (Nat.max_dec (S n1) (S n2)).
    ** rewrite e. rewrite inline_cseq.
       apply E_Seq with s'.
    ++ apply inline_ceval_S with (S n1); [now auto | reflexivity].
    ++ apply inline_ceval_S with (S n2); [now auto | now apply PeanoNat.Nat.max_l_iff].
       ** rewrite e. rewrite inline_cseq.
          apply E_Seq with s'.
    ++ apply inline_ceval_S with (S n1); [now auto | now apply PeanoNat.Nat.max_r_iff].
    ++ apply inline_ceval_S with (S n2); [now auto | reflexivity].
    * exists 2. simpl.  apply E_IfFalse. auto.  apply E_Skip.
    * destruct IHceval1 as [n1 IH1].
      destruct IHceval2 as [n2 IH2].
      exists (S(max n1 n2)).
      simpl.
      destruct n1 as [|n1].
    + apply ceval_inf_loop in IH1.
      contradiction IH1.
    + destruct n2 as [|n2].
  - apply ceval_inf_loop in IH2.
    contradiction IH2.
  - destruct (Nat.max_dec (S n1) (S n2)).
    ** rewrite e.
       rewrite inline_cif.
       apply E_IfTrue. assumption.
       rewrite inline_cseq.
       apply E_Seq with s'.
       apply IH1.
       apply inline_ceval_S with (S n2); [now auto | now apply PeanoNat.Nat.max_l_iff].
    ** rewrite e.
       rewrite inline_cif.
       apply E_IfTrue. assumption.
       rewrite inline_cseq.
       apply E_Seq with s'.
       apply inline_ceval_S with (S n1); [now auto | now apply PeanoNat.Nat.max_r_iff].
       apply IH2.
    *  destruct IHceval as [n IH].
       exists n.
       destruct n as [|n].
    + apply ceval_inf_loop in IH.
      contradiction IH.
    + rewrite inline_ccall.
      apply E_Call.
      apply H.
Qed.

(** Defintion of a Hoare Triple with inliner **)

Definition i_hoare_triple (n: nat)
           (P: precondition) (Q: postcondition)
           (c : com) (ps : Psi.psi) : Prop :=
  forall s s',  P s -> ceval (k_inliner n c) s ps s'  -> Q s' s.

Lemma i_hoare_triple_hoare_triple :
  forall P Q p ps,
    hoare_triple P Q p ps <-> forall n, i_hoare_triple n P Q p ps.
Proof.
  unfold hoare_triple, i_hoare_triple;split;intros H.
  * intros n s s' Pre Heval.
    eapply H.
    apply Pre.
    eapply (inline_n_ceval _ _ _ _ _ Heval).
  * intros s s' HPre Heval.
    apply ceval_inline_n in Heval.
    destruct Heval.
    eapply (H _ _ _ HPre H0).
Qed.

(** Defintion of relational assertion **)

Definition r_assertion: Type := sigma ->sigma -> Prop.

(** Definition of relational Precondition **)

Definition r_precondition : Type := sigma -> sigma -> Prop.

Definition empty_r_precondition : r_precondition := (fun _ _ => False).

(** Defintion of relational Postcondition **)

Definition r_postcondition : Type :=  sigma -> sigma  -> Prop.

Definition empty_r_postcondition :  r_postcondition := (fun _ _ => True).

(** Definition of quadruple **)

Definition quadruple (P: r_precondition) (Q: r_postcondition)
           (c1 c2: com) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 -> ceval c1 s1 ps s1' -> ceval c2 s2 ps s2' -> Q s1' s2'.

(** Defintion of a relational properties with inliner **)

Definition i_quadruple (n: nat) (P: r_precondition) (Q: r_postcondition)
           (c1 c2 : com) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 ->
                   ceval (k_inliner n c1) s1 ps s1' -> ceval (k_inliner n c2) s2 ps s2' ->
                   Q s1' s2'.

Lemma qceval_n_inline_loop p1 p2 s1 s2 ps  s1' s2':
  ceval p1 s1 ps s1' ->  ceval p2 s2 ps s2' ->
  exists n : nat, ceval (k_inliner n p1) s1 ps s1' /\ ceval (k_inliner n p2) s2 ps s2' .
Proof.
  intros Heval1  Heval2.
  apply ceval_inline_n in Heval1.
  apply ceval_inline_n in Heval2.
  destruct Heval1. destruct Heval2.
  destruct (Nat.max_dec x0 x).
  * exists x0.
    apply PeanoNat.Nat.max_l_iff in e.
    split.
    apply (inline_ceval_S _ _ _ _ _ H x0 e).
    apply H0.
  * exists x.
    apply PeanoNat.Nat.max_r_iff in e.
    split.
    apply H.
    apply (inline_ceval_S _ _ _ _ _ H0 x e).
Qed.

Lemma i_quadruple_quadruple P Q p1 p2 ps:
  quadruple P Q p1 p2 ps <-> forall n, i_quadruple n P Q p1 p2 ps.
Proof.
  unfold quadruple, i_quadruple;split;intros H.
  * intros n s1 s2 s1' s2' Pre Heval1 Heval2.
    eapply H.
    apply Pre.
    eapply (inline_n_ceval _  _ _ _ _ Heval1).
    eapply (inline_n_ceval _  _ _ _ _ Heval2).
  * intros s1 s2 s1' s2' Pre Heval1 Heval2.
    specialize (qceval_n_inline_loop _ _ _ _ _ _ _  Heval1 Heval2).
    intros Heval. destruct Heval as [n Heval]. destruct Heval as (Hevaln1 & Hevaln2).
    eapply (H n _ _ _ _ Pre Hevaln1 Hevaln2).
Qed.

(** Facts about relational Properties **)

Lemma while_quadruple (inv: r_assertion) b1 b2 c1 c2 ps:
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 =  true)
            (fun s1' s2' => inv s1' s2' /\ beval s1' b1 = beval s2' b2 ) c1 c2 ps ->
  quadruple ( fun s1 s2 => inv s1 s2 /\ beval s1 b1 = beval s2 b2 )
            ( fun s1' s2' => inv s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
            (CWhile b1 c1 (fun _=> True)) (CWhile b2 c2 (fun _ => True)) ps.
Proof.
  intros Hinv.
  apply i_quadruple_quadruple.
  intros n.
  induction n.
  * intros s1 s2 s1' s2' HP Heval1 Heval2.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
  * intros s1 s2 s1' s2' HP Heval1 Heval2.
    rewrite inline_cwhile in Heval1.
    rewrite inline_cwhile in Heval2.
    destruct n.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
    rewrite inline_cif in Heval1.
    rewrite inline_cif in Heval2.
    remember (k_inliner (S n) (CSeq c1 (CWhile b1 c1 (fun _ : list sigma => True)))) as ident.
    inversion Heval1;clear Heval1;subst.
  - remember (k_inliner (S n) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    + rewrite inline_cseq in H6.
      rewrite inline_cseq in H8.
      remember (k_inliner (S n) (CWhile b1 c1 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S n) c1) as ident2.
      inversion H6;subst.
      clear H6.
      remember (k_inliner (S n) (CWhile b2 c2 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S n) c2) as ident2.
      inversion H8;subst.
      clear H8.
      eapply IHn.
      eapply Hinv.
      split. apply HP.
      split. assumption. assumption.
      apply inline_n_ceval in H1. apply H1.
      apply inline_n_ceval in H2. apply H2.
      assumption. assumption.
    + destruct HP.
      rewrite H5 in H0.
      rewrite H7 in H0.
      discriminate H0.
  - remember (k_inliner (S n) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    + destruct HP.
      rewrite H5 in H0.
      rewrite H7 in H0.
      discriminate H0.
    + inversion H6;subst.
      inversion H8;subst.
      split. apply HP.
      split. assumption. assumption.
Qed.

Definition bi_quadruple (i: nat) (P: r_precondition) (Q: r_postcondition)
           (c1 c2 : com) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2' n m , i = n + m -> P s1 s2 ->
                   ceval (k_inliner n c1) s1 ps s1' ->
                   ceval (k_inliner m c2) s2 ps s2' ->
                   Q s1' s2'.

Lemma qceval_n_b_inline_loop p1 p2 s1 s2 ps  s1' s2':
  ceval p1 s1 ps s1' ->  ceval p2 s2 ps s2' ->
  exists n m: nat, ceval (k_inliner n p1) s1 ps s1' /\ ceval (k_inliner m p2) s2 ps s2' .
Proof.
  intros Heval1  Heval2.
  apply ceval_inline_n in Heval1.
  apply ceval_inline_n in Heval2.
  destruct Heval1. destruct Heval2.
  exists x. exists x0.
  split.
  apply H.
  apply H0.
Qed.

Lemma bi_quadruple_quadruple P Q p1 p2 ps:
  quadruple P Q p1 p2 ps <-> forall n, bi_quadruple n P Q p1 p2 ps.
Proof.
  unfold quadruple, bi_quadruple;split;intros H.
  * intros i s1 s2 s1' s2' n m Hi Pre Heval1 Heval2.
    eapply H.
    apply Pre.
    eapply (inline_n_ceval _  _ _ _ _ Heval1).
    eapply (inline_n_ceval _  _ _ _ _ Heval2).
  * intros s1 s2 s1' s2' Pre Heval1 Heval2.
    specialize (qceval_n_b_inline_loop _ _ _ _ _ _ _  Heval1 Heval2).
    intros Heval. destruct Heval as [n Heval]. destruct Heval as [m Heval].
    destruct Heval as (Hevaln & Hevalm).
    specialize (H (n + m) s1 s2 s1' s2' n m).
    apply H.
    reflexivity.
    assumption.
    assumption.
    assumption.
Qed.

Definition r_cond: Type := sigma -> sigma -> bool.

Lemma simpl_side_condition b1 b2 L R s1 s2 :
  (beval s1 b1 = beval s2 b2 \/ (beval s1 b1 = true /\ L s1 s2 = true ) \/
   (beval s2 b2 = true /\ R s1 s2 = true)) ->
  ((beval s1 b1 = true /\ beval s2 b2 = true /\ L s1 s2 = false /\ R s1 s2 = false) \/
    (beval s1 b1 = false /\ beval s2 b2 = false) \/  (beval s1 b1 = true /\ L s1 s2 = true ) \/
    (beval s2 b2 = true /\ R s1 s2 = true)).
Proof.
  intros H.
  destruct H.
  * destruct (beval s1 b1) eqn: Hb1.
    + destruct (L s1 s2) eqn: HL.
     -  auto.
     - destruct (R s1 s2) eqn: HR.
       ** rewrite <- H. auto.
       ** rewrite <- H. auto.
    + rewrite <- H. auto.
  * destruct H.
    + destruct H. rewrite H,H0. auto.
    + destruct H. rewrite H,H0. auto.
Qed.

(* Possible instation of L and R are :
   L = X /\ (not b1 \/ not Y)
   R = Y /\ (not b2 \/ not X)

   where X and Y are the condition for executiong left or right.
   In addition following side condition must be ensured:
   b1 /\ b2 -> X \/ Y
   b1 /\ not b2 -> X
   not b1 /\ b2 -> Y

*)

Lemma while_skedule_quadruple (inv : r_assertion) (L R : r_cond) b1 b2 c1 c2 ps:
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 = true /\
                         L s1 s2 = false /\ R s1 s2 = false)
            (fun s1' s2' => inv s1' s2')
            c1 c2 ps ->
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true  /\ L s1 s2 = true )
            (fun s1' s2' => inv s1' s2' )
            c1 CSkip ps ->
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s2 b2 = true  /\ R s1 s2 = true)
            (fun s1' s2' => inv s1' s2')
            CSkip c2 ps ->
  (forall s1 s2, inv s1 s2 ->
            beval s1 b1 = beval s2 b2 \/
            (beval s1 b1 = true /\ L s1 s2 = true ) \/
            (beval s2 b2 = true /\ R s1 s2 = true)) ->
  quadruple inv
            ( fun s1' s2' => inv s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
            (CWhile b1 c1 (fun _=> True)) (CWhile b2 c2 (fun _ => True)) ps.
Proof.
  intros Hinv1 Hinv2 Hinv3 Hinv.
  apply bi_quadruple_quadruple.
  intros i.
  induction i.
  intros s1 s2 s1' s2' n m Hi HP Heval1 Heval2.
  symmetry in Hi.
  apply plus_is_O in Hi.
  destruct Hi.
  subst.
  apply ceval_inf_loop in Heval1.
  contradiction Heval1.
  intros s1 s2 s1' s2' n m Hi HP Heval1 Heval2.
  specialize (Hinv _ _ HP).
  destruct n.
  apply ceval_inf_loop in Heval1.
  contradiction Heval1.
  destruct m.
  apply ceval_inf_loop in Heval2.
  contradiction Heval2.
  apply simpl_side_condition in Hinv.
  destruct Hinv.
  * rewrite  inline_cwhile in Heval1.
    rewrite inline_cwhile in Heval2.
    destruct n.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
    destruct m.
    apply ceval_inf_loop in Heval2.
    contradiction Heval2.
    rewrite inline_cif in Heval1.
    rewrite inline_cif in Heval2.
    remember (k_inliner (S n) (CSeq c1 (CWhile b1 c1 (fun _ : list sigma => True)))) as ident.
    inversion Heval1;clear Heval1;subst.
 - remember (k_inliner (S m) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    + rewrite inline_cseq in H7.
      rewrite inline_cseq in H9.
      remember (k_inliner (S n) (CWhile b1 c1 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S n) c1) as ident2.
      inversion H7;subst.
      clear H7.
      remember (k_inliner (S m) (CWhile b2 c2 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S m) c2) as ident2.
      inversion H9;subst.
      clear H9.
      assert (H12: i = S n + S (S m)) by lia.
      eapply IHi.
      apply H12.
      eapply Hinv1.
      split. apply HP.
      assumption.
      apply inline_n_ceval in H2. apply H2.
      apply inline_n_ceval in H3. apply H3.
      assumption.
      eapply inline_ceval_S.
      apply H11.
      lia.
    + rewrite H6 in H.
      rewrite H8 in H.
      decompose [and] H.
      discriminate H2.
  - remember (k_inliner (S n) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    + rewrite H6 in H.
      rewrite H8 in H.
      decompose [and] H.
      discriminate H0.
    + inversion H7;subst.
      inversion H9;subst.
      split. apply HP.
      split. assumption. assumption.
 * destruct H.
  - rewrite  inline_cwhile in Heval1.
    rewrite inline_cwhile in Heval2.
    destruct n.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
    destruct m.
    apply ceval_inf_loop in Heval2.
    contradiction Heval2.
    rewrite inline_cif in Heval1.
    rewrite inline_cif in Heval2.
    remember (k_inliner (S n) (CSeq c1 (CWhile b1 c1 (fun _ : list sigma => True)))) as ident.
    inversion Heval1;clear Heval1;subst.
    + remember (k_inliner (S m) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    ** rewrite H6 in H.
      rewrite H8 in H.
      decompose [and] H.
      discriminate H0.
    ** rewrite H6 in H.
      rewrite H8 in H.
      decompose [and] H.
      discriminate H0.
  + remember (k_inliner (S n) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2; subst.
    ** rewrite H6 in H.
      rewrite H8 in H.
      decompose [and] H.
      discriminate H1.
    ** inversion H7;subst.
      inversion H9;subst.
      split. apply HP.
      split. assumption. assumption.
  - destruct H.
    rewrite  inline_cwhile in Heval1.
    destruct n.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
    rewrite inline_cif in Heval1.
    remember (k_inliner (S n) (CSeq c1 (CWhile b1 c1 (fun _ : list sigma => True)))) as ident.
    inversion Heval1;clear Heval1;subst.
    + rewrite inline_cseq in H7.
      remember (k_inliner (S n) (CWhile b1 c1 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S n) c1) as ident2.
      inversion H7;subst.
      clear H7.
      assert (H12: i = S n + S m) by lia.
      eapply IHi.
      apply H12.
      eapply Hinv2.
      split. apply HP. assumption.
      apply inline_n_ceval in H2. apply H2.
      apply E_Skip.
      assumption.
      assumption.
    + destruct H.
      rewrite H6 in H.
      discriminate H.
  + rewrite  inline_cwhile in Heval2.
    destruct m.
    apply ceval_inf_loop in Heval2.
    contradiction Heval2.
    rewrite inline_cif in Heval2.
    remember (k_inliner (S m) (CSeq c2 (CWhile b2 c2 (fun _ : list sigma => True)))) as ident.
    inversion Heval2;clear Heval2;subst.
    ** rewrite inline_cseq in H7.
      remember (k_inliner (S m) (CWhile b2 c2 (fun _ : list sigma => True))) as ident1.
      remember (k_inliner (S m) c2) as ident2.
      inversion H7;subst.
      clear H7.
      assert (H12: i = S n + S m) by lia.
      eapply IHi.
      apply H12.
      eapply Hinv3.
      split. apply HP. assumption.
      apply E_Skip.
      apply inline_n_ceval in H2. apply H2.
      assumption.  assumption.
    ** destruct H.
      rewrite H6 in H.
      discriminate H.
Qed.
