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

Theorem rcorrect :
forall cl ps p,
tc_p ps cl ->
forall (P Q: r_assertion),
(forall ml (hy:length p = length ml),
P ml -> rtc' p ml cl hy) ->
(forall ml (hy:length p = length ml),
P ml -> rtc p ml cl Q hy) ->
relational_prop P Q p ps.
Proof.
intros cl ps p Hproc.
unfold relational_prop.
induction p.
*  intros.
   specialize (H0 []).
   simpl in H0.
   apply length_zero_iff_nil in H1.
   apply length_zero_iff_nil in H2.
   subst.
   apply H0.
   reflexivity.
   assumption.
*  intros.
   destruct s;[ discriminate H1 | ].
   destruct s';[ discriminate H2| ].
   inversion H4;subst.
   specialize (IHp (fun sl => P (s :: sl)) (fun sl => Q (s1 :: sl))).
   simpl in IHp.
   generalize H13.
   generalize H3.
   inversion H1.
   inversion H2.
   generalize H7.
   generalize H6.
   eapply IHp.
    ** intros.
       symmetry in H1.
       assert (hy2: length (a ::p) = length (s::ml)).
       {intros. simpl. rewrite hy. reflexivity. }
       specialize (H (s :: ml) hy2 H5).
       destruct (mk_rtc'_def a p cl s ml hy2) as (hyr & HYP).
       rewrite HYP in H.
       destruct H.
       replace hy with hyr.
       apply H8.
       apply eq_proofs_unicity.
       intros.
       lia.
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
          specialize (H (m :: ml) hy2 H8).
          destruct (mk_rtc'_def a p cl m ml hy2) as (hyr & HYP).
          rewrite HYP in H.
          destruct H.
          apply H.
       -- intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          destruct (mk_rtc_def a p cl m ml hy2) as (hyr & HYP).
          specialize (H0 (m::ml) hy2 H8).
          rewrite (HYP Q) in H0.
          replace hy with hyr.
          apply H0.
          apply eq_proofs_unicity.
          intros.
          lia.
Qed.
