From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Quadruple.
From Rela Require Import Rela.
From Rela Require Import Vcg.
From Rela Require Import Vcg_Quadruple.
From Rela Require Import Vcg_Rela.
From Rela Require Import Correct_Rela.

From Stdlib Require Import Lists.List.
Import ListNotations.

(** Proof that one can use a standard verification condition generator
    to proof Quadruples **)

Lemma qcorrect_c :
  forall qcl ps1 ps2 p1 p2 h1 h2,
    forall (P: q_precondition) (Q: q_postcondition),
      (forall ps1 ps2,
          (forall m1 m2,
              P m1 m2 -> qtr qcl ps1 ps2 ->
              qtc' p1 p2  m1 m2 h1 h2
                (phi_call Phi.trial_phi ps1)
                (phi_call Phi.trial_phi ps2))
          /\
            (forall m1 m2,
                P m1 m2 -> qtr qcl ps1 ps2 ->
                qtc p1 p2 m1 m2 h1 h2
                  (phi_call Phi.trial_phi ps1) (phi_call Phi.trial_phi ps2)
                  (fun m1' m2' _ _ => Q m1' m2' m1 m2))) ->
    quadruple_ctx qcl ps1 ps2 P Q p1 p2.
Proof.
  intros qcl ps1 ps2 p1 p2 h1 h2 P Q H.
  specialize (H ps1 ps2); destruct H.
  intros Hproc.
  unfold quadruple.
  intros.
  revert H3.
  revert H1.
  revert s2 s2'.
  eapply (correct_c p2 (phi_call Phi.trial_phi ps2) ps2 h2).
  - intros m HPre.
    specialize (H s1 m HPre (qtr_relational_prop _ _ _ Hproc)).
    apply H.
  - intros s2 HPre.
    revert H2.
    revert HPre.
    revert s1 s1'.
    eapply (correct_c p1 (phi_call Phi.trial_phi ps1) ps1 h1).
    + intros m HPre.
      specialize (H m s2 HPre (qtr_relational_prop _ _ _ Hproc)).
      apply H.
    + intros s1 HPre.
      specialize (H0 s1 s2 HPre (qtr_relational_prop _ _ _ Hproc)).
      apply H0.
    + apply phi_call_hoare.
      intros p.
      apply (trivial_hoare _ p).
  - apply phi_call_hoare.
    intros p.
    apply (trivial_hoare _ p).
Qed.

(** Proof that one can use a verification condition
    generator to proof Quadruple on procedure **)

Lemma qcorrect_proc :
  forall qcl ps1 ps2,
    qtc_p ps1 ps2 qcl ->
    quadruple_proc_ctx qcl ps1 ps2.
Proof.
  intros qcl ps1 ps2 Htc.
  unfold quadruple_proc_ctx.
  unfold qtc_p in Htc.
  split.
  - intros p1 p2 ps1_init ps2_inti.
    eapply qcorrect_c.
    intros ps1' ps2'.
    specialize (Htc p1 p2 ps1' ps2').
    decompose [and] Htc; clear Htc.
    split.
    + intros m1 m2 HPre Htr.
      apply H.
      split;[apply HPre|].
      split;[apply Htr|].
      split;[apply HPre|].
      split;apply HPre.
    + intros m1 m2 HPre Htr.
      apply H.
      split;[apply HPre|].
      split;[apply Htr|].
      split;[apply HPre|].
      split;apply HPre.
  - split.
    + intros p1 p2 ps1_init ps2_inti.
      eapply qcorrect_c.
      intros ps1' ps2'.
      specialize (Htc p1 p2 ps1' ps2').
      decompose [and] Htc; clear Htc.
      split.
      * intros m1 m2 HPre Htr.
        apply H1.
        split;[apply HPre|].
        split;[apply Htr|].
        apply HPre.
      * intros m1 m2 HPre Htr.
        apply H1.
        split;[apply HPre|].
        split;[apply Htr|].
        apply HPre.
    + split.
      * intros p1 p2 s1_init ps2_inti.
        eapply qcorrect_c.
        intros ps1' ps2'.
        specialize (Htc p1 p2 ps1' ps2').
        decompose [and] Htc; clear Htc.
        split.
        -- intros m1 m2 HPre Htr.
           apply H0.
           split;[apply HPre|].
           split;[apply Htr|].
           apply HPre.
        -- intros m1 m2 HPre Htr.
           apply H0.
           split;[apply HPre|].
           split;[apply Htr|].
           apply HPre.
      * intros p1 p2 s1 s2.
        specialize (Htc p1 p2 Psi.empty_psi Psi.empty_psi).
        decompose [and] Htc; clear Htc.
        apply H3.
Qed.

(** Proof that one can use a verification condition
    generator for modular Relatioanl Properties verification
    (with handler of Quadruples)
 **)

Theorem qcorrect :
  forall qcl ps1 ps2 p1 p2 h1 h2,
  forall (P: q_precondition) (Q: q_postcondition),
  qtc_p ps1 ps2 qcl ->
      (forall ps1 ps2,
          (forall m1 m2,
              P m1 m2 -> qtr qcl ps1 ps2 ->
              qtc' p1 p2  m1 m2 h1 h2
                (phi_call Phi.trial_phi ps1)
                (phi_call Phi.trial_phi ps2))
          /\
            (forall m1 m2,
                P m1 m2 -> qtr qcl ps1 ps2 ->
                qtc p1 p2 m1 m2 h1 h2
                  (phi_call Phi.trial_phi ps1) (phi_call Phi.trial_phi ps2)
                  (fun m1' m2' _ _ => Q m1' m2' m1 m2))) ->
      quadruple P Q p1 p2 ps1 ps2.
Proof.
  intros.
  apply recursion_quadruple with qcl.
  * apply qcorrect_proc. assumption.
  * apply qcorrect_c with (h1:=h1) (h2:=h2). all: try assumption.
Qed.


(*

- We need to define how to verifiy quadruples using verification
  condition generation using proof on calls and loops.
- We need to define how proof relational properties using
  relational properties on calls, quadruples on calls and
  quadruple on whiles

 *)

(* Include the relational while rule system *)

(* Just use the normal termination for the transitivity application, for
 partial correction use axiom forall f, s, exit s', call f s s'
 and proof the rule from the phd *)

Theorem qrcorrect :
  forall rcl (qcl: Quadruple.Q_Phi.phi) ps p h,
  forall (P: r_precondition) (Q: r_postcondition),
    let rcl0 :=
      (fun l : list Proc.Proc.t =>
         if PeanoNat.Nat.eqb (length l) 2 then rela_clause qcl rcl l else rcl l)
        in
  rtc_p ps rcl ->
  qtc_p ps ps qcl ->
  (forall ps,
    (forall ml,
       P ml -> tr rcl0 ps -> rtc' p ml h (phi_call (extract rcl0) ps)) /\
    (forall ml,
       P ml -> tr rcl0 ps ->
       rtc p ml h (phi_call (extract rcl0) ps ) (fun ml' _ => Q ml' ml))) ->
    relational_prop P Q p ps.
Proof.
  intros.
  apply ext_recursion_relational with rcl qcl.
  * eapply qcorrect_proc. apply H0.
  * apply rcorrect_proc. assumption.
  * apply (rcorrect_c rcl0 ps p h); assumption.
Qed.
