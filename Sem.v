From Rela Require Import Loc.
From Rela Require Import Aexp.
Import AexpNotations.
From Rela Require Import Bexp.
Import BexpNotations.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Com.
From Rela Require Import function_cpo constructs.

(** Evaluation command as a relation **)

Inductive ceval : com -> sigma -> Psi.psi -> sigma -> Prop :=
  | E_Skip : forall s ps,
      ceval CSkip s ps s
  | E_Assi : forall s ps x a n,
      aeval s a = n ->
      ceval (CAssi x a) s ps (x !-> n ; s)
  | E_Assr : forall s ps x a n,
      aeval s a = n ->
      ceval (CAssr x a) s ps ((s x) !-> n ; s)
  | E_Assert: forall s ps (b : assertion),
      ceval (CAssert b) s ps s
  | E_IfTrue : forall s s' ps b p1 p2,
      beval s b = true ->
      ceval p1 s ps s' ->
      ceval (CIf b p1 p2) s ps s'
  | E_IfFalse : forall s s' ps b p1 p2,
      beval s b = false ->
      ceval p2 s ps s' ->
      ceval (CIf b p1 p2) s ps s'
  | E_Seq : forall s s' s'' ps p1 p2,
      ceval p1 s ps s' ->
      ceval p2 s' ps s'' ->
      ceval (CSeq p1 p2) s ps s''
  | E_WhileFalse : forall b s ps p inv var id,
      beval s b = false ->
      ceval (CWhile b p inv var id) s  ps s
  | E_WhileTrue : forall b s s' s'' ps p inv var id,
      beval s b = true ->
      ceval p s ps s' ->
      ceval (CWhile b p inv var id) s' ps s'' ->
      ceval (CWhile b p inv var id) s  ps s''
  | E_Call : forall s s' f ps,
      ceval ( ps f) s ps s' ->
      ceval (CCall f) s  ps s'
.

(** Facts about ceval **)

Lemma ceval_inf_loop s ps s' inv var id:
ceval (CWhile BTrue CSkip inv var id) s ps s' -> False.
Proof.
  intros Heval.
  remember (CWhile BTrue CSkip inv var id) as original_command eqn:Horig.
  induction Heval;inversion Horig.
  * inversion Horig;subst. inversion H.
  * inversion Horig;subst.
    apply IHHeval2. reflexivity.
Qed.

Lemma ceval_det s ps c:
  forall s1' s2', ceval c s ps s1' -> ceval c s ps s2' -> s1' = s2'.
Proof.
  intros s1' s2' E1 E2.
  generalize dependent s2'.
  induction E1; intros st2' E2 ; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply IHE1; auto.
  - rewrite H in H6.
    discriminate H6.
  - rewrite H in H6.
    discriminate H6.
  - eapply IHE1; auto.
  - specialize (IHE1_1 s'0 H1).
    subst.
    apply (IHE1_2 _ H5).
  - reflexivity.
  - rewrite H in H8.
    discriminate H8.
  - rewrite H in H8.
    discriminate H8.
  - specialize (IHE1_1 s'0 H9).
    subst.
    apply (IHE1_2 _ H10).
  - apply (IHE1 _ H0).
Qed.

(** Evaluation command as a function **)

(* https://github.com/rocq-community/semantics *)

Definition bind (A B:Type)(v:option A)(f:A->option B) : option B :=
  match v with Some x => f x | None => None end.

Arguments bind : default implicits.

(*This proof can more modular, the sale for W_phi_continuous *)

Lemma bind_continuous :
  forall (A B:Type) F G,
    continuous (f_order A B) (f_order' B) F ->
    continuous (f_order A B) (f_order' B) G ->
    continuous (f_order A B) (f_order' B)
      (fun f x => bind (F f x) (G f)).
Proof.
  unfold f_order'.
  intros A B F G HFc HGc c Hc l H.
  specialize (HFc c Hc l H) as HF.
  specialize (HGc c Hc l H) as HG.
  clear H.
  apply lift_lub.
  intros x.
  split.
  - intros n.
    destruct HF as [HF _].
    specialize (HF n x); simpl in HF.
    inversion HF;[auto |].
    destruct x0;rewrite <- H;[simpl|auto].
    destruct HG as [HG _].
    specialize (HG n b);simpl in HG.
    inversion HG;auto.
  - intros y Hu.
    case_eq (F l x);[|auto].
    + intros x0 H; simpl.
      specialize (lub_some_witness _ _ _ _ _ _ H HF) as [nf Hf].
      case_eq (G l x0);[|auto].
      * intros ? H0; simpl.
        specialize (lub_some_witness _ _ _ _ _ _ H0 HG) as [ng Hg].
        specialize (Hu (nf + ng)); simpl in Hu.
        specialize
          (transitive_lift A _ (@option_cpo B) (transitive_option_cpo B))
          as Htc.
        specialize
          (reflexive_lift A _ (@option_cpo B) (reflexive_option_cpo B))
          as Hrc.
        generalize (chain_le _ _ Htc Hrc _ _ _ Hc (Nat.le_add_r nf ng)).
        specialize (continuous_imp_monotonic _ _ _ _ F Hrc HFc) as HFm.
        intros HFcc %(HFm _ _).
        specialize (HFcc x).
        rewrite Hf in HFcc.
        inversion HFcc; subst.
        rewrite <- H3 in Hu; simpl in Hu.
        generalize (chain_le _ _ Htc Hrc c _ _ Hc (Nat.le_add_l ng nf)).
        specialize (continuous_imp_monotonic _ _ _ _ G Hrc HGc) as HGm.
        intros HGcc %(HGm _ _).
        specialize (HGcc x0).
        rewrite Hg in HGcc.
        inversion HGcc;subst.
        rewrite <- H4 in Hu.
        assumption.
Qed.

Module W_phi.

  Definition F_phi (A:Type)(t:A->option bool)(f g :A->option A) :=
    fun r => 'IF (t r) 'THEN (bind (f r) g) 'ELSE (Some r).

  Theorem F_phi_continuous :
    forall (A : Type) t f,
      continuous (f_order A A)(f_order A A) (F_phi A t f).
  Proof.
    intros A t f; unfold F_phi.
      apply ifthenelse_continuous with (F:= comp_right f)
                                       (G:= fun (g:A->option A)(x:A) => Some x).
    apply comp_right_continuous.
    apply continuous_cst; auto.
  Qed.

  Definition phi := fun A t f => Tarski_fix (F_phi A t f).

  Arguments phi : default implicits.

  Lemma phi_terminates_n :
    forall (A:Type) (t:A->option bool)  f r r',
      phi t f r = Some r' ->
      exists n, iter _ (F_phi A t f) n (fun g => None) r = Some r'.
  Proof.
    intros A t f r r' Heq.
    assert (Hlub : lub (f_order' A) (phi t f)
                     (fun n => iter _ (F_phi A t f) n (fun x : A => None))).
    apply least_fixpoint_lub_iterates; auto.
    intros g x; apply option_cpo_none_bot.
    unfold f_order'; apply F_phi_continuous.
    unfold phi, F_phi, f_order'; apply Tarski_fix_prop.
    exact (F_phi_continuous A t f).
    apply (lub_some_witness _ _ _ r r' (phi t f) Heq Hlub).
  Qed.

  Lemma fix_phi :
    forall (A:Type)(t:A->option bool) f,
      F_phi A t f (phi t f) = phi t f.
  Proof.
    intros A t f.
    assert (Hint : least_fixpoint (f_order' A) (F_phi A t f) (phi t f)).
    unfold phi, f_order'; apply Tarski_fix_prop; apply F_phi_continuous.
    unfold least_fixpoint in Hint; fold (phi t f) in Hint.
    intuition.
  Qed.

  Lemma always_witness A B:
    forall (F : (A -> option B) -> B -> option B)
      (c : nat -> A -> option B)
      (l : A -> option B),
      lub (f_order' B) (F l) (fun n : nat => F (c n)) ->
      forall x, exists n, @option_cpo B (F l x) (F (c n) x).
  Proof.
    intros F c l HF x.
    specialize (lub_lift_reverse _ _ _ _ _ HF) as HF'.
    simpl in HF'.
    case_eq (F l x).
    - intros b Hb.
      specialize (HF' x).
      rewrite Hb in HF'.
      specialize (lub_some_witness1 _ _ _ HF') as [w Hw].
      exists w. rewrite Hw. auto.
    - intros. exists 0. auto.
  Qed.

  Lemma iter_phi :
    forall (A B : Type)
      F
      (t : B -> option bool)
      (c : nat -> A -> option B)
      w b n x,
      iter (B -> option B) (F_phi B t (F (c n))) w (fun _ : B => None) x = Some b ->
      W_phi.phi t (F (c n)) x = Some b.
  Proof.
    intros ?? F t c w ? ?.
    induction w.
    - intros ? Hw; inversion Hw.
    - simpl; intros x.
      rewrite <- W_phi.fix_phi.
      unfold W_phi.F_phi at 1 3.
      case (t x);[| discriminate ].
      intros b0;case b0;[simpl|auto].
      case_eq (F (c n) x);[simpl| intros ? Hb; inversion Hb].
      intros x' Hx' Hn.
      apply IHw.
      assumption.
  Qed.

  Theorem W_phi_continuous :
    forall (A B:Type) F t,
      continuous (f_order A B) (f_order' B) F ->
      continuous (f_order A B) (f_order' B)
        (fun f x => W_phi.phi t (F f) x).
  Proof.
    intros A B F t HFc c Hc l Hl.
    specialize (HFc c Hc l Hl) as HF.
    apply lift_lub.
    intros x.
    split.
    - intros n.
      case_eq (W_phi.phi t (F (c n)) x);[|auto].
      intros b [nb <-] %(W_phi.phi_terminates_n _ _ _ _ _).
      revert x.
      induction nb ;[auto |].
      simpl;intros x.
      rewrite <- W_phi.fix_phi.
      unfold W_phi.F_phi at 1 3.
      case (t x);[|auto]; intros b0.
      case b0;simpl;[|auto].
      destruct HF as [HF _].
      specialize (HF n x);simpl in HF.
      inversion HF;[auto |].
      rewrite <- H.
      case x0;[|auto].
      simpl.
      apply IHnb.
    - intros y Hy.
      specialize (always_witness _ _ _ _ _ HF) as Hx.
      case_eq (W_phi.phi t (F l) x);[|auto].
      intros b Hb.
      specialize (W_phi.phi_terminates_n _ _ _ _ _ Hb) as [w Hw].
      assert (truc : exists n,
                 iter (B -> option B) (W_phi.F_phi B t (F (c n))) w (fun _ : B => None) x
                 = Some b).
      { clear Hy Hb.
        generalize dependent x.
        induction w.
        - intros x Hw; inversion Hw.
        - intros x; simpl.
          unfold W_phi.F_phi at 1 3.
          case (t x);[|discriminate].
          intros b0;case b0;[simpl|exists 0;auto].
          simpl.
          case_eq (F l x);[simpl| discriminate].
          intros x' Hx' [n Hn] %(IHw _).
          specialize (Hx x) as [n' Hn'].
          rewrite Hx' in Hn'.
          inversion Hn'.
          exists (n' + n).
          specialize
            (transitive_lift A _ (@option_cpo B) (transitive_option_cpo B))
            as Htc.
          specialize
            (reflexive_lift A _ (@option_cpo B) (reflexive_option_cpo B))
            as Hrc.
          generalize (chain_le _ _ Htc Hrc _ _ _ Hc (Nat.le_add_r n' n)).
          specialize (continuous_imp_monotonic _ _ _ _ F Hrc HFc) as HFm.
          intros HFcc %(HFm _ _).
          specialize (HFcc x).
          rewrite <- H1 in HFcc.
          inversion HFcc.
          simpl.
          revert Hn. revert Htc. revert Hrc. revert Hc. revert HFc. clear.
          intros HFc Hc Hrc Htc.
          revert x'.
          induction w.
          + intros ? Hn;inversion Hn.
          + simpl. intros x.
            unfold W_phi.F_phi at 1 3.
            case (t x);[|eauto].
            intros b0;case b0;[simpl|auto].
            case_eq (F (c n) x);[simpl| discriminate ].
            intros x' Hx' Hn.
            generalize (chain_le _ _ Htc Hrc _ _ _ Hc (Nat.le_add_l n n')).
            specialize (continuous_imp_monotonic _ _ _ _ F Hrc HFc) as HFm.
            intros HFcc %(HFm _ _).
            specialize (HFcc x).
            rewrite Hx' in HFcc.
            inversion HFcc.
            simpl.
            apply IHw.
            assumption.
      }
      destruct truc.
      specialize (Hy x0).
      simpl in Hy.
      apply iter_phi in H.
      rewrite H in Hy.
      assumption.
  Qed.

End W_phi.

Module Psi'.
  Definition psi : Type := (Proc.t * sigma) -> option sigma.

  Definition empty_psi: psi := fun x => Some (snd x).
End Psi'.

Fixpoint ds  (ps : Psi'.psi) (i : com) : sigma -> option sigma :=
  match i with
  | CSkip => fun r => Some r
  | CAssi x a => fun l => bind (Some (aeval l a)) (fun v => Some (x !-> v; l))
  | CAssr x a => fun l => bind (Some (aeval l a)) (fun v => Some ((l x) !-> v; l))
  | CAssert a => fun r => Some r
  | CSeq i1 i2 => fun r => bind (ds ps i1 r) (ds ps i2)
  | CIf b i1 i2 => fun l => if beval l b then ds ps i1 l else ds ps i2 l
  | CWhile b p inv var id => fun l => W_phi.phi (fun l' => Some (beval l' b)) (ds ps p) l
  | CCall f => fun l => ps (f, l)
  end.

Module F_phi.

  Lemma ds_continuous :
    forall i,
      continuous
        (f_order (Proc.t * sigma) sigma)
        (f_order sigma sigma)
        (fun ps => ds ps i).
  Proof.
    induction i.
    - intros c  _ ps _;  simpl.
      apply lub_cst.
      apply reflexive_f_order.
    - intros c  _ ps _;  simpl.
      apply lub_cst.
      apply reflexive_f_order.
    - intros c  _ ps _;  simpl.
      apply lub_cst.
      apply reflexive_f_order.
    - intros c  _ ps _;  simpl.
      apply lub_cst.
      apply reflexive_f_order.
    - simpl; apply bind_continuous; assumption.
    - simpl.
      apply
        (ifthenelse_continuous
           (Proc.t * sigma) sigma (fun x => Some (beval x b)) _ _ IHi1 IHi2).
    - simpl; apply W_phi.W_phi_continuous; assumption.
    - simpl. intros c Hc l Hl.
      split.
      * intros n s.
        destruct Hl as [Hl _].
        specialize (Hl n (f,s)).
        assumption.
      * intros y Hy s.
        case_eq (l (f,s));[|auto].
        intros x H.
        specialize (lub_some_witness _ _ _ _ _ _ H Hl) as [n Hx].
        specialize (Hy n s);simpl in Hy.
        rewrite <- Hx.
        assumption.
  Qed.

  Definition F_phi ps (ps' : Psi'.psi) : Psi'.psi :=
    fun x => ds ps' (ps (fst x)) (snd x).

  Theorem F_phi_continuous :
    forall ps,
      continuous
        (f_order (Proc.t * sigma) sigma)
        (f_order (Proc.t * sigma) sigma) (F_phi ps).
  Proof.
    intros ps c Hc l [Hu Hl].
    unfold F_phi.
    split.
    - intros n [p s];  simpl.
      specialize (ds_continuous (ps p) c Hc l (conj Hu Hl)) as [Hu' _].
      apply Hu'.
    - intros ds' Hds' [ p s]; simpl.
      specialize (ds_continuous (ps p) c Hc l (conj Hu Hl)) as [_ Hl'].
      apply (Hl' (fun s => ds' (p,s))).
      intros n s'.
      apply (Hds' n (p,s')).
  Qed.

  Definition phi := fun ps => Tarski_fix (F_phi ps).

  Arguments phi : default implicits.

  Lemma phi_terminates_n :
    forall ps r r',
      phi ps r = Some r' ->
      exists n, iter _ (F_phi ps) n (fun _ => None) r = Some r'.
    intros ps r r' Heq.
    apply (lub_some_witness _ _
                (fun n => iter _ (F_phi ps) n (fun _ => None)) r r' (phi ps) Heq).
    apply least_fixpoint_lub_iterates.
    + unfold reflexive.
      unfold lift_order.
      intros; apply option_cpo_refl.
    + apply antisymmetric_lift.
      apply antisym_option_cpo.
    + apply lift_complete.
      apply complete_option_cpo.
    + intros x g; apply option_cpo_none_bot.
    + apply F_phi_continuous.
    + unfold phi, F_phi, f_order'; apply Tarski_fix_prop.
      exact (F_phi_continuous ps).
  Qed.

  Lemma fix_phi :
    forall ps, F_phi ps (phi ps) = phi ps.
  Proof.
    intros ps.
    assert (Hint : least_fixpoint (f_order (Proc.t * sigma) sigma) (F_phi ps) (phi ps)).
    unfold phi, f_order'; apply Tarski_fix_prop; apply F_phi_continuous.
    unfold least_fixpoint in Hint; fold (phi ps) in Hint.
    intuition.
  Qed.

End F_phi.

Definition denot c s ps := ds (F_phi.phi ps) c s.
