From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Rela.
From Rela Require Import Vcg.
From Rela Require Import Vcg_Rela.

From Stdlib Require Import Lists.List.
Import ListNotations.

(** Proof that one can use a standard verification condition generator
    to proof Relational Properties **)

Lemma rcorrect_c :
forall rcl ps p h,
forall (P: r_precondition) (Q: r_postcondition),
  (forall ps,
      let cll := (phi_call (extract rcl)) ps in
      (forall ml,  P ml -> tr rcl ps ->  rtc' p ml h cll)  /\
      (forall ml, P ml -> tr rcl ps -> rtc p ml h cll (fun ml' _ => Q ml' ml)))
  ->
  relational_prop_ctx rcl ps P Q p.
Proof.
  intros rcl ps p h P Q H.
  specialize (H ps); destruct H.
  generalize dependent H0.
  generalize dependent H.
  generalize dependent Q.
  generalize dependent P.
  generalize dependent h.
  induction p;intros.
  -  intros Hproc.
     unfold relational_prop.
     intros.
     apply length_zero_iff_nil in H1.
     apply length_zero_iff_nil in H2.
     subst.
     destruct h.
     + apply (H0 []).
        * assumption.
        * apply tr_relational_prop.
          apply Hproc.
     + assert (Htr: tr rcl ps).
       { apply tr_relational_prop. apply Hproc. }
       specialize (H0 [] H3 Htr).
       contradiction H0.
  -  intros Hproc.
     unfold relational_prop.
     intros.
     destruct s;[ discriminate H1 | ].
     destruct s';[ discriminate H2 | ].
     inversion H4;subst.
     destruct h.
     + assert (Htr: tr rcl ps).
       { apply tr_relational_prop.  apply Hproc. }
       specialize (H0 (s :: s0) H3 Htr).
       contradiction H0.
     + specialize (IHp h0 (fun sl => P (s :: sl))
                     (fun sl' sl => Q (s1 :: sl') (s :: sl))).
       simpl in IHp.
       generalize H13.
       generalize H3.
       inversion H1.
       inversion H2.
       generalize H7.
       generalize H6.
       apply IHp.
       * intros.
         specialize (H (s :: ml) H5 H8).
         apply H.
       * intros.
         generalize H10.
         generalize H5.
         generalize s s1.
         rewrite hoare_rela.
         specialize (rela_hoare_extract rcl ps Hproc).
         apply tr_relational_prop in Hproc.
         intros.
         specialize (phi_call_hoare ps (fun p => extract rcl p) H9) .
         eapply correct_c.
         -- intros.
            specialize (H (m :: ml) H11 Hproc).
            apply H.
         -- intros.
            specialize (H0 (m::ml) H11 Hproc).
            apply H0.
       * apply Hproc.
Qed.

(** Proof that one can use a verification condition
    generator to proof relational procedure contract **)

Lemma rcorrect_proc :
  forall rcl ps,
    rtc_p ps rcl ->
    relational_prop_proc_ctx rcl ps.
Proof.
  intros rcl ps Htc.
  unfold relational_prop_proc_ctx.
  intros.
  unfold rtc_p in Htc.
  eapply rcorrect_c;split;intros; specialize (Htc p ml ps1);destruct Htc.
  * assumption.
  * assumption.
  * apply H1.
  * assumption.
  * assumption.
  * assumption.
Qed.

(** Proof that one can use a verification condition
    generator for modular Relatioanl Properties verification **)

Theorem rcorrect :
  forall rcl ps p h,
  forall (P: r_precondition) (Q: r_postcondition),
  rtc_p ps rcl ->
  (forall ps,
    (forall ml,
       P ml -> tr rcl ps -> rtc' p ml h (phi_call (extract rcl) ps)) /\
    (forall ml,
       P ml -> tr rcl ps ->
       rtc p ml h (phi_call (extract rcl) ps ) (fun ml' _ => Q ml' ml))) ->
    relational_prop P Q p ps.
Proof.
  intros.
  apply recursion_relational with rcl.
  * apply rcorrect_proc. assumption.
  * apply rcorrect_c with (h:=h). all: try assumption.
Qed.
