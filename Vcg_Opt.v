From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Vcg.
From Rela Require Import Hoare_Triple.
Import Bool.Bool.

From Coq Require Import Lists.List.
Import ListNotations.

Import Vcg.Why3_Set.
Import Vcg.Assn_b.

(** Definition of logical banching **)

Inductive branch (A B C : Prop) : Prop :=
  | Then : A -> B -> branch A B C
  | Else : ~ A -> C -> branch A B C.

Lemma branch_simpl : forall A B C,
branch A B C -> (A -> B) /\ (~A -> C).
Proof.
intros.
destruct H.
+ split.
  * auto.
  * intros. contradiction H1.
+ split.
  * intros. contradiction H1.
  * auto.
Qed.

(** Partial translation of boolean expression into Prop **)

Fixpoint simpl_bassn b st :=
match b with
| BTrue => True
| BFalse => False
| BEq a1 a2 => aeval st a1 = aeval st a2
| BLe a1 a2 => aeval st a1 <= aeval st a2
| BAnd b1 b2 => (simpl_bassn b1 st) /\ (simpl_bassn b2 st)
| BOr b1 b2 => (simpl_bassn b1 st) \/ (simpl_bassn b2 st)
| BNot (BEq a1 a2) => aeval st a1 <> aeval st a2
| BNot (BLe a1 a2) => aeval st a2 < aeval st a1
| BNot BTrue => False
| BNot BFalse => True
| _ => bassn b st
end.

Lemma bassn_simpl_bassn : forall b st , bassn b st -> simpl_bassn b st.
Proof.
unfold bassn.
intros.
induction b.
* auto.
* auto.
* simpl.
  apply Is_true_eq_true in H.
  simpl in H.
  apply OrdersEx.Nat_as_DT.eqb_eq in H.
  assumption.
* simpl.
  apply Is_true_eq_true in H.
  simpl in H.
  apply Compare_dec.leb_complete in H.
  assumption.
* destruct b;simpl.
  + auto.
  + auto.
  + apply Proc.eqb_neq.
    apply negb_true_iff.
    apply Is_true_eq_true.
    apply H.
  + apply Proc.leb_gt.
    apply negb_true_iff.
    apply Is_true_eq_true.
    apply H.
  + auto.
  + auto.
  + auto.
* simpl. apply Is_true_eq_true in H.
  simpl in H.
  apply andb_true_iff in H.
  split.
  + apply IHb1.
    apply Is_true_eq_left.
    apply H.
  + apply IHb2.
    apply Is_true_eq_left.
    apply H.
* simpl. apply Is_true_eq_true in H.
  simpl in H.
  apply orb_true_iff in H.
  destruct H.
  + apply or_introl.
    apply IHb1.
    apply Is_true_eq_left.
    assumption.
  + apply or_intror.
    apply IHb2.
    apply Is_true_eq_left.
    assumption.
Qed.

Lemma bassn_not_simpl_bassn_not : forall b st , ~ bassn b st -> ~ simpl_bassn b st.
Proof.
unfold bassn.
intros.
induction b.
* auto.
* auto.
* simpl.
  apply Proc.eqb_neq.
  apply negb_true_iff.
  apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply H.
* simpl.
  apply Proc.nle_gt.
  apply Proc.leb_gt.
  apply negb_true_iff.
  apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply H.
* destruct b;simpl.
  + auto.
  + auto.
  + apply Proc.eq_dne.
    apply negb_prop_intro in H.
    apply Is_true_eq_true in H.
    simpl in H.
    rewrite negb_involutive in H.
    apply Proc.eqb_eq.
    apply H.
  + apply Proc.nlt_ge.
    apply negb_prop_intro in H.
    apply Is_true_eq_true in H.
    simpl in H.
    rewrite negb_involutive in H.
    apply Proc.leb_le.
    apply H.
  + auto.
  + auto.
  + auto.
* simpl.
  intros H1.
  destruct H1.
  apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply negb_true_iff in H.
  simpl in H.
  apply andb_false_iff in H.
  destruct H.
  + apply negb_true_iff in H.
    apply Is_true_eq_left in H.
    apply negb_prop_elim in H.
    apply IHb1 in H.
    contradiction H.
  + apply negb_true_iff in H.
    apply Is_true_eq_left in H.
    apply negb_prop_elim in H.
    apply IHb2 in H.
    contradiction H.
* apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply negb_true_iff in H.
  simpl in H.
  apply orb_false_iff in H.
  destruct  H.
  simpl.
  intros H1.
  destruct H1.
  + apply negb_true_iff in H.
    apply Is_true_eq_left in H.
    apply negb_prop_elim in H.
    apply IHb1 in H.
    contradiction H.
  + apply negb_true_iff in H0.
    apply Is_true_eq_left in H0.
    apply negb_prop_elim in H0.
    apply IHb2 in H0.
    contradiction H0.
Qed.

(** Defintion of optimized verification condition generator:
    - We do not have an exponential growth of the size of the formulas due
      to condition branching.
    - Boolean expression are translated to Prop for convenience during proof
      of verification conditions.
**)

Fixpoint tc (c: com) (m m': Sigma.sigma)
            (cl: Phi.phi) (fin: Prop -> Prop): Prop :=
    match c with
    | CSkip => fin (m' = m)
    | CAss x a => fin (m' = set m x (aeval m a))
    | CAssr x a => fin (m' = set m (m x) (aeval m a))
    | CAssert b =>  fin (b m /\ m = m')
    | CSeq p1 p2 => forall m'',
        tc p1 m m'' cl (fun f1 => tc p2 m'' m' cl (fun f2 => fin (f1 /\ f2)))
    | CIf b p1 p2 =>
        tc p1 m m' cl (fun p1 =>
        tc p2 m m' cl (fun p2 =>
            fin (branch (simpl_bassn b m) p1 p2)))
    | CWhile b p inv => fin (inv m /\ inv m' /\ ~(simpl_bassn b m'))
    | CCall f => fin((get_pre (cl f)) m /\ (get_post (cl f)) m')
    end.

(** Facts about verification condition generator **)

Ltac ltc1 := simpl; intros m m' suite1 suite2 H H0;
             apply H; apply H0.

Lemma consequence_tc_suite :
forall p cl m m' (suite1 suite2 : Prop -> Prop),
(forall p, suite1 p -> suite2 p) ->
tc p m m' cl suite1 -> tc p m m' cl suite2.
Proof.
intros p cl.
induction p.
  * ltc1.
  * ltc1.
  * ltc1.
  * ltc1.
  * simpl. intros.
    eapply IHp1 with (fun p => tc p2 m'' m' cl (fun f2 : Prop => suite1 (p /\ f2))).
    - intros.
      eapply IHp2 with (fun f => suite1(p /\ f)).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * simpl. intros.
    eapply IHp1 with
     (fun p => tc p2 m m' cl (fun f2 : Prop => suite1 (branch (simpl_bassn b m) p f2))).
    - intros.
      eapply IHp2 with (fun f => suite1 (branch (simpl_bassn b m) p f)).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * ltc1.
  * ltc1.
Qed.

Lemma intros_tc :
forall p m m' cl (debut : Prop) (suite : Prop -> Prop),
tc p m m' cl (fun f => debut -> suite f) ->
(debut -> tc p m m' cl suite).
Proof.
induction p;simpl.
* intros. apply H. assumption.
* intros. apply H. assumption.
* intros. apply H. assumption.
* intros. apply H. assumption.
* intros.
  eapply consequence_tc_suite.
  + intros.
    generalize H0.
    apply IHp2.
    apply H1.
  + apply H.
* intros.
  eapply consequence_tc_suite.
  + intros.
    generalize H0.
    apply IHp2.
    apply H1.
  + apply H.
* intros. apply H. assumption.
* intros. apply H. assumption.
Qed.

Lemma prenexe_tc:
forall (A:Type) p m m' cl (suite : A -> Prop -> Prop),
(forall s, tc p m m' cl (suite s)) ->
tc p m m' cl (fun f => forall s,suite s f).
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  eapply consequence_tc_suite.
  + intros p He.
    apply IHp2.
    apply He.
  + apply IHp1.
    intros.
   apply H.
* intros.
  eapply consequence_tc_suite.
  + intros p He.
    apply IHp2.
    apply He.
  + apply IHp1.
    intros.
   apply H.
* intros. apply H.
* intros. apply H.
Qed.

Lemma opt_1_true:
forall p1 p2 b m m' cl (suite : Prop),
simpl_bassn b m ->
tc p1 m m' cl (fun f1 =>
tc p2 m m' cl (fun f2 =>  branch (simpl_bassn b m) f1 f2 -> suite)) ->
tc p1 m m' cl (fun f1 =>
tc p2 m m' cl (fun f2 => f1 -> suite)).
Proof.
intros.
apply (consequence_tc_suite _ _ _ _
             (fun f1 => tc p2 m m' cl (fun f2 =>
              branch (simpl_bassn b m) f1 f2 -> suite))).
* intros.
  apply (consequence_tc_suite _ _ _ _
        (fun f2 => branch (simpl_bassn b m) p f2 -> suite)).
  - intros. apply H2.
    apply Then.
    all: try assumption.
  - assumption.
* assumption.
Qed.

Lemma opt_1_false:
forall p1 p2 b m m' cl (suite : Prop),
~simpl_bassn b m ->
tc p1 m m' cl (fun f1 =>
tc p2 m m' cl (fun f2 =>  branch (simpl_bassn b m) f1 f2 -> suite)) ->
tc p1 m m' cl (fun f1 =>
tc p2 m m' cl (fun f2 => f2 -> suite)).
Proof.
intros.
apply (consequence_tc_suite _ _ _ _
             (fun f1 => tc p2 m m' cl (fun f2 =>
              branch (simpl_bassn b m) f1 f2 -> suite))).
* intros.
  apply (consequence_tc_suite _ _ _ _
        (fun f2 => branch (simpl_bassn b m) p f2 -> suite)).
  - intros. apply H2.
    apply Else.
    all: try assumption.
  - assumption.
* assumption.
Qed.

Lemma simpl_tc :
forall p m m' cl (suite : Prop),
tc p m m' cl (fun _ => suite) -> suite .
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  assert (H1: tc p1 m m cl (fun _ : Prop => suite)).
  { intros.
    eapply consequence_tc_suite with
    ((fun _ : Prop => tc p2 m m' cl (fun _ : Prop => suite))).
    + intros.
      eapply IHp2.
      apply H0.
    + apply H.
  }
  eapply IHp1.
  apply H1.
* intros.
  eapply IHp2.
  eapply IHp1.
  apply H.
* intros. apply H.
* intros. apply H.
Qed.

Lemma true_tc :
forall p m m' cl,
True -> tc p m m' cl (fun _ => True).
Proof.
induction p;simpl;intros.
all: try auto.
* eapply consequence_tc_suite.
  + intros.
    apply IHp2.
    apply H0.
  + apply IHp1. auto.
* eapply consequence_tc_suite.
  + intros.
    apply IHp2.
    apply H0.
  + apply IHp1. auto.
Qed.

Lemma rev_simpl_tc :
forall p m m' cl (suite : Prop),
suite -> tc p m m' cl (fun _ => suite) .
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  apply (consequence_tc_suite _ _ _ _ (fun _ => suite)).
  + intros.
    apply IHp2.
    apply H.
  + apply IHp1.
    apply H.
* intros.
  apply (consequence_tc_suite _ _ _ _ (fun _ => suite)).
  + intros.
    apply IHp2.
    apply H.
  + apply IHp1.
    apply H.
* intros. apply H.
* intros. apply H.
Qed.

Lemma and_tc :
forall p (f1: Prop) m m' cl (suite :Prop),
(f1 -> tc p m m' cl (fun f2 => f2 -> suite)) -> 
tc p m m' cl (fun f2 => f1 /\ f2 -> suite).
Proof.
induction p;simpl;intros.
* apply H. apply H0. apply H0.
* apply H. apply H0. apply H0.
* apply H. apply H0. apply H0.
* apply H. apply H0. apply H0.
* eapply consequence_tc_suite.
  + intros.
    apply (consequence_tc_suite _ _ _ _ (fun f2 : Prop => (f1 /\ p) /\ f2 -> suite)).
    - intros. apply H1. split. split. apply H2. apply H2. apply H2.
    - apply IHp2.
      apply H0.
  + apply IHp1.
    intros.
    generalize (H H0 m'').
    intros.
    eapply consequence_tc_suite.
    - intros p H2.
      apply intros_tc.
      apply (consequence_tc_suite _ _ _ _ (fun f : Prop => p /\ f -> suite)).
      ++ intros. apply H3. split. apply H4. apply H5.
      ++ apply H2.
    - apply H1.
* destruct (beval m b) eqn: He.
  + simpl.
    eapply consequence_tc_suite.
    - intros.
      eapply consequence_tc_suite.
      ** intros.
         destruct H2.
         apply branch_simpl in H3.
         destruct H3.
         assert (H5: p).
         { apply H3. 
           apply bassn_simpl_bassn.
           apply bexp_eval_true.
           assumption.
         }
         assert (H6: f1 /\ p). { split. apply H2. apply H5. }
         generalize H6.
         apply H1.
      ** apply rev_simpl_tc.
       apply H0.
    - apply IHp1.
      intros.
      generalize (H H0);intros.
      apply (consequence_tc_suite _ _ _ _ _  (fun f2 : Prop => f2 -> suite))
      in H1.
      ** apply H1.
      ** intros.
       apply (consequence_tc_suite _ _ _ _ _  (fun _ : Prop => p -> suite)) 
       in H2.
       ++ apply simpl_tc in H2.
          apply H2. apply H3.
       ++ intros.
          apply H4.
          apply Then;[ | apply H5]. 
          apply bassn_simpl_bassn.
          apply bexp_eval_true.
          assumption.
  + simpl.
    eapply consequence_tc_suite.
    - intros.
      eapply consequence_tc_suite.
      ** intros.
         destruct H2.
         apply branch_simpl in H3.
         destruct H3.
         assert (H5: p0).
         { apply H4. 
           apply bassn_not_simpl_bassn_not.
           apply bexp_eval_false.
           assumption.
         }
         assert (H6: f1 /\ p0). { split. apply H2. apply H5. }
         generalize H6.
         apply H1.
      ** apply IHp2.
         apply H0.
    - apply rev_simpl_tc.
      intros.
      generalize (H H0);intros.
      apply (consequence_tc_suite _ _ _ _ _  
      (fun _ : Prop => tc p2 m m' cl (fun p2 : Prop => p2 -> suite)))
      in H1.
      ** apply simpl_tc in H1.
         apply H1.
      ** intros.
       apply (consequence_tc_suite _ _ _ _ _  (fun p0 : Prop => p0 -> suite)) 
       in H2.
       ++ apply H2.
       ++ intros.
          apply H3.
          apply Else;[ | apply H4].
          apply bassn_not_simpl_bassn_not.
          apply bexp_eval_false.
          assumption.
* apply H. apply H0. apply H0.
* apply H. apply H0. apply H0.
Qed.

(* The optimized version implies the naive version *)

Lemma tc_same :
forall p cl m (suite1 : Sigma.sigma -> Prop),
(forall m', tc p m m' cl (fun p => p -> suite1 m')) -> Vcg.tc p m cl suite1.
Proof.
intros.
generalize dependent suite1.
generalize dependent m.
induction p;simpl.
* intros. apply H. symmetry. assumption.
* intros. apply H. assumption.
* intros. apply H. assumption.
* intros. apply H. auto.
* intros.
  eapply Vcg.consequence_tc_suite.
  + intros.
    apply IHp2.
    apply H0.
  + apply IHp1.
    intros.
    eapply consequence_tc_suite.
    - intros p He Hp m'0.
      generalize dependent Hp.
      generalize dependent m'0.
      apply He.
    - apply prenexe_tc.
      intros.
      eapply consequence_tc_suite.
      ** intros p He.
         apply intros_tc.
         eapply consequence_tc_suite with
         (fun f : Prop => p /\ f -> suite1 s).
         ++ auto.
         ++ apply He.
      ** apply H.
* intros.
  split;intros.
  + apply IHp1.
    intros.
    specialize (H m').
    apply bassn_simpl_bassn in H0.
    specialize (opt_1_true p1 p2 b m m' cl (suite1 m') H0 H).
    intros.
    eapply consequence_tc_suite.
    - intros p He.
      apply (simpl_tc p2 m m' cl (p -> suite1 m')).
      apply He.
    - apply H1.
  + apply IHp2.
    intros.
    specialize (H m').
    apply bassn_not_simpl_bassn_not in H0.
    specialize (opt_1_false p1 p2 b m m' cl (suite1 m') H0 H).
    intros.
    apply (simpl_tc p1 m m' cl (tc p2 m m' cl (fun p : Prop => p -> suite1 m'))).
    apply H1.
* intros.
  apply H.
  apply bexp_eval_false in H2.
  apply bassn_not_simpl_bassn_not in H2.
  auto.
* intros.
  apply H.
  auto.
Qed.

(** Definition of a verification condition generator for the auxiliary goals **)

Fixpoint tc' (c : com) (m: Sigma.sigma)
            (cl: Phi.phi) : Prop :=
match c with
 | CSkip => True
 | CAss x a => True
 | CAssr x a => True
 | CAssert b => b m
 | CSeq p1 p2 => tc' p1 m cl /\
                 forall m'',
                 tc p1 m m'' cl (fun f => f -> tc' p2 m'' cl)
 | CIf b p1 p2 =>
      (simpl_bassn b m -> tc' p1 m cl) /\ (~simpl_bassn b m -> tc' p2 m cl)
 | CWhile b p inv => inv m /\
   (forall m', simpl_bassn b m' -> tc' p m' cl) /\
   (forall m' m'', simpl_bassn b m' -> inv m' -> tc p m' m'' cl (fun f => f -> inv m''))
 | CCall f => (get_pre (cl f)) m
end.

(* The optimized version implies the naive version *)

Lemma tc'_same :
forall p cl m,
tc' p m cl -> Vcg.tc' p m cl.
Proof.
induction p; simpl.
* intros. auto.
* intros. auto.
* intros. auto.
* intros. apply H.
* intros.
  split.
  - apply IHp1.
    apply H.
  - apply tc_same.
    intros.
    eapply consequence_tc_suite with
    (fun f : Prop => f -> tc' p2 m' cl).
    + intros.
      apply IHp2.
      auto.
    + apply H.
* intros.
  split;intros.
  - apply IHp1.
    apply H.
    apply bassn_simpl_bassn in H0.
    assumption.
  - apply IHp2.
    apply H.
    apply bassn_not_simpl_bassn_not in H0.
    assumption.
* intros.
  split.
  - apply H.
  - split;intros.
    + apply IHp.
      apply H.
      apply bassn_simpl_bassn in H0.
      assumption.
    + apply tc_same.
      intros.
      apply H.
      ** apply bassn_simpl_bassn.
         assumption.
      ** assumption.
* intros. apply H.
Qed.

(** Definition of a verification condition generator for procedures **)

Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m m', (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m m' cl (fun p => p -> (get_post (cl f)) m').

(* The optimized version implies the naive version *)

Lemma tc_p_same :
forall ps cl,
tc_p ps cl -> Vcg.tc_p ps cl.
Proof.
intros.
unfold Vcg.tc_p.
split;intros.
* apply tc'_same.
  apply H.
  all: try assumption.
* apply tc_same.
  intros.
  apply H.
  apply H0.
Qed.

Module Test.

Definition test (p1: com) (cl: Phi.phi) (a : sigma -> Prop) (m : sigma) :=
           forall m'' : sigma, tc p1 m m'' cl (fun f : Prop => f -> a m'').

Fixpoint tc_test (c : com) (cl: Phi.phi) : list (Sigma.sigma -> Prop) :=
match c with
 | CSkip => []
 | CAss x a => []
 | CAssr x a => []
 | CAssert b => [fun m => b m]
 | CSeq p1 p2 => tc_test p1 cl ++
                 map (test p1 cl) (tc_test p2 cl)

 | CIf b p1 p2 => (map (fun a: (Sigma.sigma -> Prop) =>
                  fun m => simpl_bassn b m -> a m) (tc_test p1 cl))
                  ++
                  (map (fun a: (Sigma.sigma -> Prop) =>
                  fun m => ~simpl_bassn b m -> a m) (tc_test p2 cl))

| CWhile b p i => [fun m => i m]
                   ++
                   (map (fun a: (Sigma.sigma -> Prop) =>
                   fun _ => forall m', simpl_bassn b m' -> a m') (tc_test p cl))
                   ++
                   [fun _ => forall m' m'', 
                   simpl_bassn b m' ->  i m' -> tc p m' m'' cl (fun f => f -> i m'')]

 | CCall f => [fun m => (get_pre (cl f)) m]
end.

Lemma tc_test_same :
forall p cl m,
(forall n, (nth n (tc_test p cl) (fun _ => True)) m) -> tc' p m cl.
Proof.
induction p;intros.
+ simpl. auto.
+ simpl. auto.
+ simpl. auto.
+ simpl.
  apply (H 0).
+ simpl.
  split.
  * apply IHp1.
    simpl in H.
    intro n.
    generalize (H n);intros;clear H.
    destruct (Proc.lt_ge_cases n (length ((tc_test p1 cl)))).
    - rewrite app_nth1 in H0; [assumption|assumption].
    - rewrite nth_overflow; [ auto | assumption].
  * intros.
    eapply consequence_tc_suite.
    - intros.
      apply IHp2.
      intros n.
      generalize dependent H1.
      generalize dependent n.
      apply H0.
    - simpl in H.
      apply prenexe_tc.
      intro n.
      generalize (H ((length(tc_test p1 cl))+n));intros;clear H.
      rewrite app_nth2_plus in H0.
      destruct (Proc.lt_ge_cases n (length ((tc_test p2 cl)))).
      ++ erewrite nth_indep in H0;[|rewrite map_length;assumption].
         rewrite map_nth in H0.
         apply H0.
      ++ rewrite nth_overflow;[ | assumption].
         eapply consequence_tc_suite.
         ** intros. apply H1.
         ** apply true_tc. auto.
+ simpl.
  split.
  * intros.
    apply IHp1.
    simpl in H.
    intro n.
    generalize (H n);intros;clear H.
    destruct (Proc.lt_ge_cases n (length ((tc_test p1 cl)))).
    - rewrite app_nth1 in H1;[ | rewrite map_length;assumption].
      erewrite nth_indep in H1;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : sigma -> Prop) (m : sigma) => simpl_bassn b m -> a m)) in H1.
      apply H1.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
  * intros.
    apply IHp2.
    simpl in H.
    intro n.
    generalize (H ((length(tc_test p1 cl))+n));intros;clear H.
    erewrite <- map_length in H1.
    rewrite app_nth2_plus in H1.
    destruct (Proc.lt_ge_cases n (length ((tc_test p2 cl)))).
    - erewrite nth_indep in H1;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : sigma -> Prop) (m : sigma) => ~simpl_bassn b m -> a m)) in H1.
      apply H1.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
+ simpl.
  split;[ apply (H 0)| ].
  split.
  * intros.
    apply IHp.
    intro n.
    generalize (H (1 + n)).
    intros.
    simpl in H1.
    destruct (Proc.lt_ge_cases n (length ((tc_test p cl)))).
    - rewrite app_nth1 in H1;[ | rewrite map_length;assumption].
      erewrite nth_indep in H1;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : sigma -> Prop) (_ : sigma) =>
                forall m', simpl_bassn b m' -> a m')) in H1.
      apply H1.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
  * intros.
    generalize (H (1 + (length (tc_test p cl)) + 0)).
    intros.
    simpl in H2.
    erewrite <- map_length in H2.
    rewrite app_nth2_plus in H2.
    simpl in H2. apply H2;[ assumption | assumption ].
+ apply (H 0).
Qed.

Import ComNotations.
Import AexpNotations.
Import BexpNotations.

Definition assert3 : com := <[ assert (fun m => m EAX = 2) ;
                               skip;
                               assert (fun m => m EAX = 2) ]>.

Example test_tc :
forall m n,
m EAX = 2 -> (nth n (tc_test assert3 Phi.empty_phi) (fun _ => True)) m.
Proof.
simpl.
destruct n.
  * auto.
  * destruct n.
    + unfold test.
      simpl.
      intros.
      destruct H0.
      subst.
      assumption.
    + intros.
      destruct n; [auto|auto].
Qed.

End Test.
