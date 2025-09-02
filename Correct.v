From Rela Require Import Vcg.
From Rela Require Import Hoare_Triple.
From Rela Require Import Com.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Loc.
Import Why3_Set.
Import Assn_b.
From Coq Require Import Lists.List.
Import ListNotations.

(** Proof that one can use a verification condition generator to proof Hoare Triples **)

Lemma correct_c :
  forall p cl ps l,
  forall (P :precondition) (Q: postcondition),
    (forall m, P m -> tc' p m l cl) ->
    (forall m, P m -> tc p m l cl (fun m' _ => Q m' m)) ->
    hoare_triple_ctx cl ps P Q p.
Proof.
  unfold hoare_triple_ctx.
  intros p cl ps.
  induction p.
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2. inversion H3;subst. reflexivity.
  * unfold hoare_triple. intros. eapply H0. apply H2.
    apply H. apply H2. inversion H3;subst. reflexivity.
  * intros l P Q Htc' Htc Hproc. eapply seq_hoare_triple.
    apply (IHp1 l).
    - apply Htc'.
    - intros.
      apply (consequence_tc_suite _ _ _ _
      (fun m' h => tc' p2 m' h cl /\ tc p2 m' h cl (fun m'' _  => Q m'' m))).
      + intros s l0 H0 s''.
        generalize dependent H0.
        generalize dependent s''.
        generalize dependent s.
        apply (IHp2 l0 ).
        ** intros. apply H0.
        ** intros. apply H0.
        ** apply Hproc.
      + apply tc_split.
        ** apply Htc'. apply H.
        ** apply Htc. apply H.
    - apply Hproc.
  * intros l P Q Htc' Htc Hproc. apply if_hoare_triple.
    + apply (IHp1 l).
      - intros. apply Htc'. apply H. apply bexp_eval_true. apply H.
      - intros. simpl in Htc. destruct H. specialize (Htc m H). destruct Htc.
        apply H1. apply bexp_eval_true. assumption.
      - assumption.
    + apply (IHp2 l).
      - intros. apply Htc'. apply H. destruct H. apply bexp_eval_false in H0. apply H0.
      - intros. simpl in H. destruct H. specialize (Htc m H). destruct Htc.
        apply H2. apply bexp_eval_false. assumption.
      - assumption.
  * intros l P Q Htc' Htc.
    intros Hproc s s' Pre Heval.
    specialize (IHp l
                  (fun sc => inv (sc :: (s :: l)) /\ beval sc b = true)
                  (fun sc _ => inv (sc :: (s :: l)))).
      specialize (Htc' s Pre).
      simpl in Htc'.
      destruct Htc'.
      specialize (Htc s Pre H).
      assert (H1 : inv (s' :: (s :: l)) /\ beval s' b = false -> Q s' s).
      { intros. apply Htc. apply H1. apply H1. }
      apply H1.
      generalize Heval.
      generalize H.
      apply while_triple.
      destruct H0.
      apply IHp.
      ** intros.
         apply H0.
         destruct H3.
         apply bexp_eval_true in H4.
         assumption.
         apply H3.
      ** intros.
         apply H2.
         destruct H3.
         apply bexp_eval_true in H4.
         assumption.
         apply H3.
    ** assumption.
 * intros l P Q Htc' Htc Hproc.
   intros s s' Pre Heval.
   specialize (Htc' s Pre).
   specialize (Htc s Pre).
   apply Htc; [apply Htc' | ].
   generalize Heval.
   generalize dependent Htc'.
   apply Hproc.
Qed.

(** Proof that one can use a verification condition
    generator to proof procedure contract **)

Lemma correct_proc :
  forall cl ps,
    tc_p ps cl ->
    hoare_triple_proc_ctx cl ps.
Proof.
  intros cl ps Htc.
  unfold hoare_triple_proc_ctx.
  intros.
  apply correct_c with Vcg.empty_history.
  * apply Htc.
  * apply Htc.
Qed.

(** Proof that one can use a verification condition
    generator for modular Hoare triple verification **)

Theorem correct :
  forall (c: com) (cl: Phi.phi) (ps: Psi.psi) (l : history),
  forall (P :precondition) (Q: postcondition),
    tc_p ps cl ->
    (forall m, P m -> tc' c m l cl) ->
    (forall m, P m -> tc c m l cl (fun m' _ => Q m' m)) ->
    hoare_triple P Q c ps.
Proof.
intros.
apply recursion_hoare_triple with cl.
* apply correct_proc. assumption.
* apply correct_c with l. all: try assumption.
Qed.
