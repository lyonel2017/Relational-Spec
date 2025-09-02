From Rela Require Import Loc.
From Rela Require Import Aexp.
Import AexpNotations.
From Rela Require Import Bexp.
Import BexpNotations.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Inliner.
From Rela Require Import function_cpo constructs.

Theorem ds_sn :  forall i l l' ps, denot i l ps = Some l' -> ceval i l ps l'.
  induction i.
  - unfold denot, ds.
    injection 1 as ->.
    apply E_Skip.
  - unfold denot, ds, bind.
    injection 1 as <-.
    now apply E_Assi.
  - unfold denot, ds, bind.
    injection 1 as <-.
    now apply E_Assr.
  - unfold denot, ds, bind.
    injection 1 as <-.
    now apply E_Assert.
  - intros l l' ps; unfold denot; simpl; unfold bind.
    case_eq (ds (F_phi.phi ps) i1 l); intros s' Hs'.
    + intros; apply (E_Seq _ s'); [now apply IHi1| now apply IHi2].
    + discriminate Hs'.
  - intros l l' ps; unfold denot; simpl.
    case_eq (beval l b); intros Hb H.
    + apply E_IfTrue; [assumption | now apply IHi1].
    + apply E_IfFalse; [assumption | now apply IHi2].
  - intros l l' ps H.
    pose (f:= W_phi.F_phi _ (fun l => Some (beval l b)) (ds (F_phi.phi ps) i)).
    assert (Hn: exists n:nat,
               iter _ f n (fun _ : sigma => None) l = Some l').
    { apply W_phi.phi_terminates_n. assumption. }
    destruct Hn as [n Hn].
    clear H; generalize dependent l.
    induction n;simpl;intros l.
    + discriminate.
    + unfold f at 1, W_phi.F_phi , ifthenelse at 1.
      case_eq (beval l b);intros Hb.
      * unfold bind.
        case_eq (ds (F_phi.phi ps) i l);intros.
        -- now apply (E_WhileTrue _ _ s);[|apply IHi |apply IHn].
        -- discriminate.
      * injection 1 as <-.
        now apply E_WhileFalse.
  - intros l l' ps H.
    apply F_phi.phi_terminates_n in H.
    destruct H as [n Hn].
    assert(H: ds (iter Psi'.psi (F_phi.F_phi ps) n (fun _ : Proc.t * sigma => None)) (CCall f) l = Some l');
    [apply Hn | clear Hn].
    apply Inline2.ds_iter_ds_k_inliner in H.
    apply Inline2.ds_none_ceval_none in H.
    apply Inline1.inline_n_ceval with (S n).
    now apply Inline2.ceval_inline2_inline1.
Qed.

Theorem sn_ds : forall l i l' ps , ceval i l ps l' -> denot i l ps = Some l'.
  induction 1.
  - auto.
  - rewrite <- H. reflexivity.
  - rewrite <- H; reflexivity.
  - reflexivity.
  - unfold denot. simpl.
    rewrite H. assumption.
  - unfold denot. simpl.
    rewrite H. assumption.
  - unfold denot. simpl.
    unfold denot in IHceval1.
    rewrite IHceval1.  assumption.
  - unfold denot. simpl.
    rewrite <- W_phi.fix_phi.
    unfold W_phi.F_phi.
    rewrite H. reflexivity.
  - unfold denot. simpl.
    rewrite <- W_phi.fix_phi.
    unfold W_phi.F_phi.
    rewrite H. simpl.
    unfold denot in IHceval1.
    rewrite IHceval1. assumption.
  - unfold denot. simpl.
    rewrite <- F_phi.fix_phi.
    unfold F_phi.F_phi.
    assumption.
Qed.

Theorem ds_eq_sn : forall i l l' ps, denot i l ps = Some l' <-> ceval i l ps l'.
intros; split; [apply ds_sn | apply sn_ds]; auto.
Qed.
