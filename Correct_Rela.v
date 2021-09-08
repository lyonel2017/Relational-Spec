From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Rela.
From Rela Require Import Vcg.
From Rela Require Import Vcg_Rela.

From Coq Require Import Program.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.

(** Proof that one can use a standard verification condition generator
    to proof Relational Properties **)

Lemma rcorrect :
forall cl ps p h (hyh :length p = length h),
tc_p ps cl ->
forall (P: r_precondition) (Q: r_postcondition),
(forall ml (hy:length p = length ml),
P ml -> rtc' p ml h cl hy hyh) ->
(forall ml (hy:length p = length ml),
P ml -> rtc p ml h cl (fun ml' _ => Q ml' ml) hy hyh) ->
relational_prop P Q p ps.
Proof.
intros cl ps p h hyh Hproc.
unfold relational_prop.
generalize dependent h.
induction p.
*  intros.
   specialize (H0 []).
   inversion hyh.
   symmetry in H6.
   apply length_zero_iff_nil in H6.
   subst.
   simpl in H0.
   apply length_zero_iff_nil in H1.
   apply length_zero_iff_nil in H2.
   subst.
   apply H0.
   reflexivity.
   assumption.
*  intros.
   destruct s;[ discriminate H1 | ].
   destruct s';[ discriminate H2 | ].
   destruct h;[ discriminate hyh | ].
   inversion H4;subst.
   inversion hyh.
   specialize (IHp (h0) H6 (fun sl => P (s :: sl)) 
                           (fun sl' sl => Q (s1 :: sl') (s :: sl))).
   simpl in IHp.
   generalize H13.
   generalize H3.
   inversion H1.
   inversion H2.
   generalize H8.
   generalize H7.
   eapply IHp.
    ** intros.
       symmetry in H1.
       assert (hy2: length (a ::p) = length (s::ml)).
       {intros. simpl. rewrite hy. reflexivity. }
       specialize (H (s :: ml) hy2 H5).
       destruct (mk_rtc'_def a p cl s ml h h0 hy2 hyh) as (hyr1 & hyr2 & HYP).
       rewrite HYP in H.
       destruct H.
       replace hy with hyr1.
       replace H6 with hyr2.
       apply H9.
       apply eq_proofs_unicity. intros. lia.
       apply eq_proofs_unicity. intros. lia.
    ** intros.
       generalize H10.
       generalize H5.
       generalize s s1.
       rewrite hoare_rela.
       eapply recursion_hoare_triple.
       ++ eapply correct_proc.
          apply Hproc.
       ++ eapply correct.
       -- intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          specialize (H (m :: ml) hy2 H9).
          destruct (mk_rtc'_def a p cl m ml h h0 hy2 hyh) as (hyr1 & hyr2 & HYP).
          rewrite HYP in H.
          destruct H.
          apply H.
       -- intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          destruct (mk_rtc_def a p cl m ml h h0 hy2 hyh) as (hyr1 & hyr2 & HYP).
          specialize (H0 (m::ml) hy2 H9).
          specialize (HYP (fun l _ => Q l (m ::ml))).
          rewrite HYP in H0.
          replace hy with hyr1.
          replace H6 with hyr2.
          apply H0.
          apply eq_proofs_unicity.  intros. lia.
          apply eq_proofs_unicity.  intros. lia.
Qed.

Lemma urcorrect :
forall cl rcl ps p h (hyh :length p = length h),
tc_p ps cl ->
forall (P: r_precondition) (Q: r_postcondition),
(forall ml (hy:length p = length ml),
P ml -> rtc' p ml h cl hy hyh) ->
(forall ml (hy:length p = length ml),
P ml -> rtc p ml h cl (fun ml' _ => Q ml' ml) hy hyh) ->
relational_prop_ctx rcl ps P Q p.
Proof.
intros.
intros H2.
eapply rcorrect.
 * apply H.
 * apply H0.
 * apply H1.
Qed.