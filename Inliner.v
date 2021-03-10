From Rela Require Import Com.
From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.

(** Function for procedure inlining in Com **)

Fixpoint inliner c inline :=
  match c with
  | CSeq p1 p2 => CSeq (inliner p1 inline) (inliner p2 inline)
  | CIf b p1 p2 => CIf b (inliner p1 inline) (inliner p2 inline)
  | CWhile b p inv => CWhile b (inliner p inline) inv
  | CCall f => inline f
  | _ => c
end.

(** Function for recursive procedure inlining in Com **)

Fixpoint k_inliner n c (ps : Psi.psi) :=
  match n with
  | 0 => CWhile BTrue CSkip (fun _ => True)
  | S n' => inliner c (fun f => k_inliner n' (ps f) ps)
end.

(** Function for procedure inlining in Psi.psi **)

Definition k_inliner_ps n ps := fun p => k_inliner n (ps p) ps.

(** Some fact about the inlining **)

Lemma inline_cskip n ps : k_inliner (S n) CSkip ps = CSkip.
Proof.
 reflexivity.
Qed.

Lemma inline_cass n ps x a1: k_inliner (S n) (CAss x a1) ps = (CAss x a1).
Proof.
 reflexivity.
Qed.

Lemma inline_cassert n ps b: k_inliner (S n) (CAssert b) ps = (CAssert b).
Proof.
 reflexivity.
Qed.

Lemma inline_cseq n ps p1 p2: k_inliner (S n) (CSeq p1 p2) ps =
                              CSeq (k_inliner (S n) p1 ps) (k_inliner (S n) p2 ps).
Proof.
 reflexivity.
Qed.

Lemma inline_cif n ps b p1 p2: k_inliner (S n) (CIf b p1 p2) ps =
                               CIf b (k_inliner (S n)  p1 ps) (k_inliner (S n) p2 ps).
Proof.
 reflexivity.
Qed.

Lemma inline_cwhile n ps p b inv: k_inliner (S n) (CWhile b p inv) ps =
                                  CWhile b (k_inliner (S n) p ps) inv.
Proof.
 reflexivity.
Qed.

Lemma inline_ccall n f ps :
   k_inliner (S n) (CCall f) ps = k_inliner n (ps f) ps.
Proof.
 reflexivity.
Qed.

(* ceval is inlining insensitive on command *)

Lemma ceval_inline p s ps s':
  ceval p s ps s' -> ceval (inliner p ps) s ps s'.
Proof.
intros.
induction H.
  + apply E_Skip.
  + apply E_Ass.
    now auto.
  + apply E_Assert.
    now auto.
  + simpl. apply E_IfTrue; [now auto | now auto].
  + simpl. apply E_IfFalse; [now auto | now auto].
  + simpl. eapply E_Seq.
    - apply IHceval1.
    - apply IHceval2.
  + apply E_WhileFalse; now auto.
  + simpl. eapply E_WhileTrue; [now auto | | ].
    - apply IHceval1.
    - apply IHceval2.
  + simpl. assumption.
Qed.

Lemma inline_ceval p s ps s':
  ceval (inliner p ps) s ps s' -> ceval p s ps s'.
Proof.
intros.
generalize dependent s.
generalize dependent s'.
generalize dependent ps.
induction p;intros.
  + inversion H;subst.
    apply E_Skip.
  + inversion H;subst.
    apply E_Ass. now auto.
  + inversion H;subst.
    apply E_Assert. now auto.
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
   + remember (inliner (CWhile b p inv) ps) as original_command eqn:Horig.
     induction H.
     * inversion Horig.
     * inversion Horig.
     * inversion Horig.
     * inversion Horig.
     * inversion Horig.
     * inversion Horig.
     * inversion Horig;subst.
       eapply E_WhileFalse.
       assumption.
     * inversion Horig;subst.
       eapply E_WhileTrue.
       assumption.
       apply IHp. apply H0.
       apply IHceval2.
       assumption.
     * inversion Horig;subst.
   + apply E_Call.
      simpl in H. assumption.
Qed.

(* Inlinig on Com "n+1" times is equivalent to inline on Psi.psi "n" times *)

Lemma n_inline_n_inline_ps n p s ps_init s' :
   (forall ps, ceval (k_inliner (S n) p ps_init) s ps s') ->
   ceval p s (k_inliner_ps n ps_init) s'.
Proof.
intros.
specialize (H (k_inliner_ps n ps_init)).
generalize dependent s.
generalize dependent s'.
induction p ;intros.
* rewrite inline_cskip in H.
  apply H.
* rewrite inline_cass in H.
  apply H.
* rewrite inline_cassert in H.
  apply H.
* rewrite inline_cseq in H.
  inversion H;subst.
  apply E_Seq with s'0.
  + apply IHp1.
    apply H2.
  + apply IHp2.
    apply H6.
* rewrite inline_cif in H.
  inversion H;subst.
  + apply E_IfTrue.
    - assumption.
    - apply IHp1.
      apply H7.
  + apply E_IfFalse.
    - assumption.
    - apply IHp2.
      apply H7.
* remember (k_inliner (S n) (CWhile b p inv) ps_init) as original_command eqn:Horig.
  induction H;rewrite inline_cwhile in Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig;subst.
     eapply E_WhileFalse.
     assumption.
  + inversion Horig;subst.
    eapply E_WhileTrue.
    - assumption.
    - apply IHp. apply H0.
    - apply IHceval2.
      assumption.
      rewrite <- inline_cwhile in Horig.
      apply Horig.
  + inversion Horig;subst.
* apply E_Call.
  rewrite inline_ccall in H.
  apply H.
Qed.

Lemma inline_p_ps n p ps s s' ps1 ps2:
ceval (k_inliner n p ps) s ps1 s' ->
ceval (k_inliner n p ps) s ps2 s'.
Proof.
intros.
generalize dependent s.
generalize dependent s'.
generalize dependent p.
induction n.
* intros.
  apply ceval_inf_loop in H.
  contradiction H.
* induction p;intros.
  + inversion H;subst.
    apply E_Skip.
  + inversion H;subst.
    apply E_Ass.
    auto.
  + inversion H;subst.
    apply E_Assert.
    auto.
  + rewrite inline_cseq.
    rewrite inline_cseq in H.
    inversion H;subst.
    apply E_Seq with s'0.
    - apply IHp1.
      apply H2.
    - apply IHp2.
      apply H6.
  + rewrite inline_cif.
    rewrite inline_cif in H.
    inversion H;subst.
    - apply E_IfTrue.
      assumption.
      apply IHp1.
      apply H7.
    - apply E_IfFalse.
      assumption.
      apply IHp2.
      apply H7.
  + remember (k_inliner (S n) (CWhile b p inv) ps) as original_command eqn:Horig.
    induction H;rewrite inline_cwhile in Horig.
    - inversion Horig.
    - inversion Horig.
    - inversion Horig.
    - inversion Horig.
    - inversion Horig.
    - inversion Horig.
    - inversion Horig;subst.
      eapply E_WhileFalse.
      assumption.
    - inversion Horig;subst.
      eapply E_WhileTrue.
      ** assumption.
      ** apply IHp. apply H0.
      ** apply IHceval2.
         assumption.
         assumption.
         rewrite <- inline_cwhile in Horig.
         apply Horig.
     - inversion Horig;subst.
  + apply IHn.
    apply H.
Qed.

Lemma n_ps_inline_n_inline n p s ps_init s' :
   ceval p s (k_inliner_ps n ps_init) s' ->
   (forall ps, ceval (k_inliner (S n) p ps_init) s ps s').
Proof.
intros.
generalize dependent s.
generalize dependent s'.
induction p;intros.
* eapply inline_p_ps.
  apply H.
* eapply inline_p_ps.
  apply H.
* eapply inline_p_ps.
  apply H.
* inversion H;subst.
  apply E_Seq with s'0.
  + apply IHp1.
    apply H2.
  + apply IHp2.
    apply H6.
* inversion H;subst.
  + apply E_IfTrue.
    - assumption.
    - apply IHp1.
      assumption.
  + apply E_IfFalse.
    - assumption.
    - apply IHp2.
      assumption.
* remember (CWhile b p inv) as original_command eqn:Horig.
  induction H.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig.
  + inversion Horig;subst.
     eapply E_WhileFalse.
     assumption.
  + inversion Horig;subst.
    eapply E_WhileTrue.
    - assumption.
    - apply IHp. apply H0.
    - apply IHceval2.
      assumption.
      reflexivity.
  + inversion Horig;subst.
* inversion H; subst.
  rewrite inline_ccall.
  eapply inline_p_ps.
  apply H1.
Qed.

(* ceval is "n" inlining insensitive on command *)

Lemma inline_n_ceval n p s ps_init s':
  (forall ps, ceval (k_inliner n p ps_init) s ps s') -> ceval p s ps_init s'.
Proof.
intros.
specialize (H ps_init).
generalize dependent s.
generalize dependent s'.
generalize dependent p.
generalize dependent ps_init.
induction n.
* intros.
  apply ceval_inf_loop in H.
  contradiction H.
* induction p;intros.
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
   + remember (k_inliner (S n) (CWhile b p inv) ps_init) as original_command eqn:Horig.
     induction H.
     - inversion Horig.
     - inversion Horig.
     - inversion Horig.
     - inversion Horig.
     - inversion Horig.
     - inversion Horig.
     - inversion Horig;subst.
       eapply E_WhileFalse.
       assumption.
     - inversion Horig;subst.
       eapply E_WhileTrue.
       ** assumption.
       ** apply IHp. apply H0.
       ** apply IHceval2.
          assumption.
          reflexivity.
     - inversion Horig;subst.
  + apply inline_ceval.
    apply IHn.
    rewrite inline_ccall in H.
    apply H.
Qed.

Lemma inline_ceval_S n p s ps_init  s' ps:
  ceval (k_inliner n p ps_init) s ps s' ->
  forall m, n <= m -> ceval (k_inliner m p ps_init) s ps s'.
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
     - remember (k_inliner (S n) (CWhile b p inv) ps_init) as original_command eqn:Horig.
     induction H.
      ** inversion Horig.
      ** inversion Horig.
      ** inversion Horig.
      ** inversion Horig.
      ** inversion Horig.
      ** inversion Horig.
      ** inversion Horig;subst.
         eapply E_WhileFalse.
         assumption.
      ** inversion Horig;subst.
         rewrite inline_cwhile.
         eapply E_WhileTrue.
         ++ assumption.
         ++ apply IHp. apply H1.
         ++ apply IHceval2.
            assumption.
            assumption.
            reflexivity.
      ** inversion Horig;subst.
  - rewrite inline_ccall.
    apply IHn.
    now apply Le.le_S_n.
    apply H.
Qed.

Lemma ceval_inline_n p s ps_init s':
  ceval p s ps_init s' -> exists n, forall ps, ceval (k_inliner n p ps_init) s ps s'.
Proof.
induction 1;intros.
* exists 1.
  apply E_Skip.
* exists 1.
  intros.
  apply E_Ass.
  assumption.
* exists 1.
  intros.
  apply E_Assert.
  assumption.
* destruct IHceval as [n IH].
  exists n.
  intros.
  specialize (IH ps0).
  destruct n.
  - apply ceval_inf_loop in IH.
    contradiction IH.
  - rewrite inline_cif.
    apply E_IfTrue.
    assumption.
    apply IH.
* destruct IHceval as [n IH].
  exists n.
  intros.
  specialize (IH ps0).
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
  intros.
  specialize (IH1 ps0).
  specialize (IH2 ps0).
  destruct n1 as [|n1].
  + apply ceval_inf_loop in IH1.
    contradiction IH1.
  + destruct n2 as [|n2].
    - apply ceval_inf_loop in IH2.
      contradiction IH2.
    - destruct (Proc.max_dec (S n1) (S n2)).
      ** rewrite e.
         rewrite inline_cseq.
         apply E_Seq with s'. 
         ++ apply inline_ceval_S with (S n1); [now auto | reflexivity].
         ++ apply inline_ceval_S with (S n2); [now auto | now apply PeanoNat.Nat.max_l_iff].
      ** rewrite e.
         rewrite inline_cseq.
         apply E_Seq with s'. 
         ++ apply inline_ceval_S with (S n1); [now auto | now apply PeanoNat.Nat.max_r_iff].
         ++ apply inline_ceval_S with (S n2); [now auto | reflexivity].
* exists 1. intros. rewrite inline_cwhile. apply E_WhileFalse; now auto.
* destruct IHceval1 as [n1 IH1].
  destruct IHceval2 as [n2 IH2].
  exists (max n1 n2).
  intros.
  specialize (IH1 ps0).
  specialize (IH2 ps0).
  destruct n1 as [|n1].
  + apply ceval_inf_loop in IH1.
    contradiction IH1.
  + destruct n2 as [|n2].
    - apply ceval_inf_loop in IH2.
      contradiction IH2.
    - destruct (Proc.max_dec (S n1) (S n2)).
      ** rewrite e.
         rewrite inline_cwhile.
         apply E_WhileTrue with s'; [now auto | | ].
         ++ apply inline_ceval_S with (S n1); [now auto | reflexivity].
         ++ rewrite <- inline_cwhile.
            apply inline_ceval_S with (S n2); [now auto | now apply PeanoNat.Nat.max_l_iff].
      ** rewrite e.
         rewrite inline_cwhile.
         apply E_WhileTrue with s';[now auto | | ]. 
         ++ apply inline_ceval_S with (S n1) ; [now auto | now apply PeanoNat.Nat.max_r_iff].
         ++ rewrite <- inline_cwhile.
            apply inline_ceval_S with (S n2); [now auto | reflexivity].
* destruct IHceval as [n IH].
  exists (S n).
  intros.
  specialize (IH ps0).
  rewrite inline_ccall.
  destruct n as [|n].
  + apply ceval_inf_loop in IH.
    contradiction IH.
  + apply IH.
Qed.

(* ceval is inlining insensitive on ps *)

Lemma n_inline_ps_ceval p s ps s' n:
  ceval p s (k_inliner_ps n ps) s' -> ceval p s ps s'.
Proof.
intros.
apply inline_n_ceval with (S n).
intros.
specialize (n_ps_inline_n_inline n p s ps s' H ps0).
intros.
apply H0.
Qed.

Lemma ceval_n_inline_ps p s ps s':
  ceval p s ps s' -> exists n, ceval p s (k_inliner_ps n ps) s'.
Proof.
intros.
apply ceval_inline_n in H.
destruct H as [n IH].
destruct n as [|n].
* specialize (IH ps).
  apply ceval_inf_loop in IH.
  contradiction IH.
* exists n.
  apply n_inline_n_inline_ps.
  apply IH.
Qed.

(*Inling "n+1" times on Psi.psi is equivalent to inline p and "n" times Psi.psi*)

Lemma n_inline_ps_inline  n  f s ps s' :
 ceval (CCall f) s (k_inliner_ps (S n) ps) s' ->
 ceval (inliner (CCall f) ps) s (k_inliner_ps n ps) s'.
Proof.
intros.
apply inline_ceval.
specialize (n_ps_inline_n_inline (S n) (CCall f) s ps s' H).
intros.
apply H0.
Qed.
