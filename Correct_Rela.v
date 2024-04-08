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

Lemma rcorrect_c :
forall rcl ps p h (hyh :length p = length h),
forall (P: r_precondition) (Q: r_postcondition),
(forall ps,
  (forall ml (hy:length p = length ml),
     P ml -> tr rcl ps -> rtc' p ml h (phi_call (extract rcl) ps) hy hyh) /\
  (forall ml (hy:length p = length ml),
     P ml -> tr rcl ps ->
     rtc p ml h (phi_call (extract rcl) ps ) (fun ml' _ => Q ml' ml) hy hyh)) ->
relational_prop_ctx rcl ps P Q p.
Proof.
intros rcl ps p h hyh P Q H.
specialize (H ps); destruct H.
generalize dependent H0.
generalize dependent H.
generalize dependent Q.
generalize dependent P.
generalize dependent h.
induction p;intros.
*  intros Hproc.
   unfold relational_prop.
   intros.
   specialize (H0 []).
   inversion hyh.
   symmetry in H6.
   apply length_zero_iff_nil in H6.
   subst.
   simpl in H0.
   apply length_zero_iff_nil in H1.
   apply length_zero_iff_nil in H2.
   subst.
   eapply H0.
   reflexivity.
   assumption.
   eapply tr_relational_prop.
   apply Hproc.
*  intros Hproc.
   unfold relational_prop.
   intros.
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
       assert (hy2: length (a ::p) = length (s::ml)).
       {intros. simpl. rewrite hy. reflexivity. }
       specialize (H (s :: ml) hy2 H5).
       destruct (mk_rtc'_def a p (phi_call (extract rcl) ps) s ml h h0 hy2 hyh)
          as (hyr1 & hyr2 & HYP).
       rewrite HYP in H.
       destruct H.
       apply tr_relational_prop.
       apply Hproc.
       replace hy with hyr1.
       replace H6 with hyr2.
       apply H11.
       apply eq_proofs_unicity. intros. lia.
       apply eq_proofs_unicity. intros. lia.
    ** intros.
       generalize H10.
       generalize H5.
       generalize s s1.
       rewrite hoare_rela.
       specialize (rela_hoare_extract rcl ps Hproc).
       apply tr_relational_prop in Hproc.
       intros.
       specialize (phi_call_hoare ps (fun p => extract rcl p) H11) .
       eapply correct_c.
       -- intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          specialize (H (m :: ml) hy2 H12 Hproc).
          destruct (mk_rtc'_def a p (phi_call (extract rcl)ps) m ml h h0 hy2 hyh)
            as (hyr1 & hyr2 & HYP).
          rewrite HYP in H.
          apply H.
       -- intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          destruct (mk_rtc_def a p (phi_call (extract rcl) ps) m ml h h0 hy2 hyh)
             as (hyr1 & hyr2 & HYP).
          specialize (H0 (m::ml) hy2 H12 Hproc).
          specialize (HYP (fun l _ => Q l (m ::ml))).
          rewrite HYP in H0.
          replace hy with hyr1.
          replace H6 with hyr2.
          apply H0.
          apply eq_proofs_unicity.  intros. lia.
          apply eq_proofs_unicity.  intros. lia.
     ** apply Hproc.
Qed.

(** Proof that one can use a verification condition
    generator to proof relational procedure contract **)

Lemma rcorrect_proc :
  forall rcl ps,
    rtc_p ps rcl ->
    relational_prop_proc_ctx rcl ps.
Proof.
  intros cl ps Htc.
  unfold relational_prop_proc_ctx.
  intros.
  assert (H1:length (map ps p) = length (map (fun _ => empty_history) p)).
  {  rewrite map_length. rewrite map_length. reflexivity. }
  unfold rtc_p in Htc.
  eapply rcorrect_c;split;intros; specialize (Htc p ml ps1 hy H1 H);destruct Htc.
  * assumption.
  * apply H2.
  * assumption.
  * apply H3.
Qed.

(** Proof that one can use a verification condition
    generator for modular Relatioanl Properties verification **)

Theorem rcorrect :
  forall rcl ps p h (hyh :length p = length h),
  forall (P: r_precondition) (Q: r_postcondition),
  rtc_p ps rcl ->
  (forall ps,
    (forall ml (hy:length p = length ml),
       P ml -> tr rcl ps -> rtc' p ml h (phi_call (extract rcl) ps) hy hyh) /\
    (forall ml (hy:length p = length ml),
       P ml -> tr rcl ps ->
       rtc p ml h (phi_call (extract rcl) ps ) (fun ml' _ => Q ml' ml) hy hyh)) ->
    relational_prop P Q p ps.
Proof.
intros.
apply recursion_relational with rcl.
* apply rcorrect_proc. assumption.
* apply rcorrect_c with (h:=h) (hyh:=hyh). all: try assumption.
Qed.
