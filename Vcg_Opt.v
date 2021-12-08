From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Vcg.
From Rela Require Import Hoare_Triple.
Import Bool.Bool.
Import Arith.

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
  + apply Nat.eqb_neq.
    apply negb_true_iff.
    apply Is_true_eq_true.
    apply H.
  + apply Nat.leb_gt.
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
  apply Nat.eqb_neq.
  apply negb_true_iff.
  apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply H.
* simpl.
  apply Nat.nle_gt.
  apply Nat.leb_gt.
  apply negb_true_iff.
  apply negb_prop_intro in H.
  apply Is_true_eq_true in H.
  apply H.
* destruct b;simpl.
  + auto.
  + auto.
  + apply Nat.eq_dne.
    apply negb_prop_intro in H.
    apply Is_true_eq_true in H.
    simpl in H.
    rewrite negb_involutive in H.
    apply Nat.eqb_eq.
    apply H.
  + apply Nat.nlt_ge.
    apply negb_prop_intro in H.
    apply Is_true_eq_true in H.
    simpl in H.
    rewrite negb_involutive in H.
    apply Nat.leb_le.
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

Definition suite : Type := Prop -> Vcg.history -> Prop.

Fixpoint tc (c: com) (m m': Sigma.sigma) (h: Vcg.history)
            (cl: Phi.phi) (fin: suite): Prop :=
    match c with
    | CSkip => fin (m' = m) (m :: h)
    | CAss x a => fin (m' = set m x (aeval m a)) (m :: h)
    | CAssr x a => fin (m' = set m (m x) (aeval m a)) (m :: h)
    | CAssert b =>  fin (b (m :: h) /\ m = m') (m :: h)
    | CSeq p1 p2 => forall m'',
        tc p1 m m'' h cl (fun f1 h => tc p2 m'' m' h cl 
                                   (fun f2 h => fin (f1 /\ f2) h ))
    | CIf b p1 p2 =>
        tc p1 m m' h cl (fun p1 _ =>
        tc p2 m m' h cl (fun p2 _ =>
            fin (branch (simpl_bassn b m) p1 p2) (m :: h)))
    | CWhile b p inv => fin (inv (m :: h) /\ inv (m' :: h) /\ ~(simpl_bassn b m')) (m :: h)
    | CCall f => fin ((get_pre (cl f)) m /\ (get_post (cl f)) m' m) (m :: h)
    end.

(** Facts about verification condition generator **)

Ltac ltc1 := simpl; intros m m' l suite1 suite2 H H0;
             apply H; apply H0.

Lemma consequence_tc_suite :
forall p cl m m' l (suite1 suite2 : suite),
(forall p l, suite1 p l -> suite2 p l) ->
tc p m m' l cl suite1 -> tc p m m' l cl suite2.
Proof.
intros p cl.
induction p.
  * ltc1.
  * ltc1.
  * ltc1.
  * ltc1.
  * simpl. intros.
    eapply IHp1 with (fun p h => tc p2 m'' m' h cl (fun f2 h => suite1 (p /\ f2) h)).
    - intros.
      eapply IHp2 with (fun f h => suite1(p /\ f) h).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * simpl. intros.
    eapply IHp1 with
    (fun p _ => tc p2 m m' l cl (fun f2 _ => suite1 (branch (simpl_bassn b m) p f2) (m ::l))).
    - intros.
      eapply IHp2 with (fun f _ => suite1 (branch (simpl_bassn b m) p f) (m :: l)).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * ltc1.
  * ltc1.
Qed.

Lemma intros_tc :
forall p m m' l cl (debut : Prop) (suite : suite),
tc p m m' l cl (fun f h => debut -> suite f h) ->
(debut -> tc p m m' l cl suite).
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
forall (A:Type) p m m' l cl (suite : A -> suite),
(forall s, tc p m m' l cl (suite s)) ->
tc p m m' l cl (fun f h => forall s,suite s f h).
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  eapply consequence_tc_suite.
  + intros p l0 He.
    apply IHp2.
    apply He.
  + apply IHp1.
    intros.
    apply H.
* intros.
  eapply consequence_tc_suite.
  + intros p l0 He.
    apply IHp2.
    apply He.
  + apply IHp1.
    intros.
   apply H.
* intros. apply H.
* intros. apply H.
Qed.

Lemma opt_1_true:
forall p1 p2 b m m' l cl (s : Prop),
simpl_bassn b m ->
tc p1 m m' l cl (fun f1 _ =>
tc p2 m m' l cl (fun f2 _ =>  branch (simpl_bassn b m) f1 f2 -> s)) ->
tc p1 m m' l cl (fun f1 _ =>
tc p2 m m' l cl (fun f2 _ => f1 -> s)).
Proof.
intros.
apply consequence_tc_suite with
             (fun f1 _ => tc p2 m m' l cl (fun f2 _ =>
              branch (simpl_bassn b m) f1 f2 -> s)).
* intros.
  apply consequence_tc_suite with
        (fun f2 _ => branch (simpl_bassn b m) p f2 -> s).
  - intros. apply H2.
    apply Then.
    all: try assumption.
  - assumption.
* assumption.
Qed.

Lemma opt_1_false:
forall p1 p2 b m m' l cl (s : Prop),
~simpl_bassn b m ->
tc p1 m m' l cl (fun f1 _ =>
tc p2 m m' l cl (fun f2 _ =>  branch (simpl_bassn b m) f1 f2 -> s)) ->
tc p1 m m' l cl (fun f1 _ =>
tc p2 m m' l cl (fun f2 _ => f2 -> s)).
Proof.
intros.
apply consequence_tc_suite with
             (fun f1 _ => tc p2 m m' l cl (fun f2 _ =>
              branch (simpl_bassn b m) f1 f2 -> s)).
* intros.
  apply consequence_tc_suite with
        (fun f2 _ => branch (simpl_bassn b m) p f2 -> s).
  - intros. apply H2.
    apply Else.
    all: try assumption.
  - assumption.
* assumption.
Qed.

Lemma simpl_tc :
forall p m m' l cl (s : Prop),
tc p m m' l cl (fun _ _ => s) -> s .
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  assert (H1: tc p1 m m l cl (fun _ _ => s)).
  { intros.
    eapply consequence_tc_suite with
    ((fun _ h => tc p2 m m' h cl (fun _ _ => s))).
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
forall p m m' l cl,
True -> tc p m m' l cl (fun _ _ => True).
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
forall p m m' l cl (s : Prop),
s -> tc p m m' l cl (fun _ _ => s) .
Proof.
induction p;simpl.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros. apply H.
* intros.
  apply consequence_tc_suite with (fun _ _ => s).
  + intros.
    apply IHp2.
    apply H.
  + apply IHp1.
    apply H.
* intros.
  apply consequence_tc_suite with (fun _ _ => s).
  + intros.
    apply IHp2.
    apply H.
  + apply IHp1.
    apply H.
* intros. apply H.
* intros. apply H.
Qed.

(* The optimized version implies the naive version *)

Lemma tc_same :
forall p cl m l (suite1 : Vcg.suite),
  (forall m', tc p m m' l cl (fun p h => p -> suite1 m' h)) -> 
    Vcg.tc p m l cl suite1.
Proof.
intros.
generalize dependent suite1.
generalize dependent l.
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
    - intros p l0 He Hp m'0.
      generalize dependent Hp.
      generalize dependent m'0.
      apply He.
    - apply prenexe_tc.
      intros.
      eapply consequence_tc_suite.
      ** intros p l0 He.
         apply intros_tc.
         eapply consequence_tc_suite with
         (fun f h  => p /\ f -> suite1 s h).
         ++ auto.
         ++ apply He.
      ** apply H.
* intros.
  split;intros.
  + apply IHp1.
    intros.
    specialize (H m').
    apply bassn_simpl_bassn in H0.
    specialize (opt_1_true p1 p2 b m m' l cl (suite1 m' (m :: l)) H0 H).
    intros.
    eapply consequence_tc_suite.
    - intros p l0 He.
      apply (simpl_tc p2 m m' l cl (p -> suite1 m' (m :: l))).
      apply He.
    - apply H1.
  + apply IHp2.
    intros.
    specialize (H m').
    apply bassn_not_simpl_bassn_not in H0.
    specialize (opt_1_false p1 p2 b m m' l cl (suite1 m' (m :: l)) H0 H).
    intros.
    apply 
      (simpl_tc p1 m m' l cl (tc p2 m m' l cl (fun p _ => p -> suite1 m' (m :: l)))).
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

Fixpoint tc' (c : com) (m: Sigma.sigma) (h: Vcg.history) (cl: Phi.phi) : Prop :=
match c with
 | CSkip => True
 | CAss x a => True
 | CAssr x a => True
 | CAssert b => b (m :: h)
 | CSeq p1 p2 => tc' p1 m h cl /\
                 forall m'',
                 tc p1 m m'' h cl (fun f h => f -> tc' p2 m'' h cl)
 | CIf b p1 p2 =>
      (simpl_bassn b m -> tc' p1 m h cl) /\ (~simpl_bassn b m -> tc' p2 m h cl)
 | CWhile b p inv => inv (m :: h) /\
                     (forall m', simpl_bassn b m' -> 
                                 inv (m' :: h) ->
                                 tc' p m' h cl) /\
                     (forall m' m'', simpl_bassn b m' -> 
                                     inv (m' :: h) -> 
                   tc p m' m'' h cl (fun f _ => f -> inv (m'' :: h)))
 | CCall f => (get_pre (cl f)) m
end.

(* The optimized version implies the naive version *)

Lemma tc'_same : forall p cl m l, tc' p m l cl -> Vcg.tc' p m l cl.
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
    eapply consequence_tc_suite with (fun f h  => f -> tc' p2 m' h cl).
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
    forall f m m', (get_pre (cl f)) m -> tc' (ps f) m [] cl /\
                tc (ps f) m m' [] cl (fun p _ => p -> (get_post (cl f)) m' m).

(* The optimized version implies the naive version *)

Theorem tc_p_same :
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

(** Definition of a verification condition generator for the auxiliary goals 
    returning a list of goals **)

Module Tc'_list.

Definition continuation (p1: com) (cl: Phi.phi) 
                       (a : Vcg.suite) (m : sigma) (h: Vcg.history) :=
           forall m'' : sigma, tc p1 m m'' h cl (fun f h => f -> a m'' h).

Fixpoint tc'_list (c : com) (cl: Phi.phi) : list Vcg.suite :=
match c with
 | CSkip => []
 | CAss x a => []
 | CAssr x a => []
 | CAssert b => [fun m h => b (m :: h)]
 | CSeq p1 p2 => tc'_list p1 cl ++
                 map (continuation p1 cl) (tc'_list p2 cl)
 | CIf b p1 p2 => (map (fun a: Vcg.suite =>
                  fun m h => simpl_bassn b m -> a m h) (tc'_list p1 cl))
                  ++
                  (map (fun a: Vcg.suite =>
                  fun m h => ~simpl_bassn b m -> a m h ) (tc'_list p2 cl))
| CWhile b p i => [fun m h => i (m :: h)]
                   ++
                   (map (fun a: Vcg.suite =>
                   fun _ h => forall m',
                   simpl_bassn b m' -> i (m' :: h) ->a m' h) (tc'_list p cl))
                   ++
                   [fun _ h => forall m' m'',  
                   simpl_bassn b m' -> i (m' :: h) -> tc p m' m'' h cl (fun f _ => f -> i (m''::h))]
 | CCall f => [fun m _ => (get_pre (cl f)) m]
end.

(* The optimized version implies the naive version *)

Lemma tc'_list_same :
forall p cl m l,
(forall n, (nth n (tc'_list p cl) (fun _ _ => True)) m l) -> tc' p m l cl.
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
    specialize (H n).
    destruct (Nat.lt_ge_cases n (length ((tc'_list p1 cl)))).
    - rewrite app_nth1 in H; [assumption|assumption].
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
      specialize (H ((length(tc'_list p1 cl))+n)).
      rewrite app_nth2_plus in H.
      destruct (Nat.lt_ge_cases n (length ((tc'_list p2 cl)))).
      ++ erewrite nth_indep in H;[|rewrite map_length;assumption].
         rewrite map_nth in H.
         apply H.
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
    specialize (H n).
    destruct (Nat.lt_ge_cases n (length ((tc'_list p1 cl)))).
    - rewrite app_nth1 in H;[ | rewrite map_length;assumption].
      erewrite nth_indep in H;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : Vcg.suite) m h => simpl_bassn b m -> a m h)) in H.
      apply H.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
  * intros.
    apply IHp2.
    simpl in H.
    intro n.
    specialize (H ((length(tc'_list p1 cl))+n)).
    erewrite <- map_length in H.
    rewrite app_nth2_plus in H.
    destruct (Nat.lt_ge_cases n (length ((tc'_list p2 cl)))).
    - erewrite nth_indep in H;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : Vcg.suite) m h => ~simpl_bassn b m -> a m h)) in H.
      apply H.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
+ simpl.
  split;[ apply (H 0)| ].
  split.
  * intros.
    apply IHp.
    intro n.
    specialize (H (1 + n)).
    simpl in H.
    destruct (Proc.lt_ge_cases n (length ((tc'_list p cl)))).
    - rewrite app_nth1 in H ;[ | rewrite map_length;assumption].
      erewrite nth_indep in H;[ | rewrite map_length;assumption].
      rewrite
      (map_nth (fun (a : Vcg.suite) _ h =>
                forall m', simpl_bassn b m' -> inv (m' :: h)-> a m' h)) in H.
      apply H.
      assumption.
      assumption.
    - rewrite nth_overflow;[auto | assumption].
  * intros.
    specialize (H (1 + (length (tc'_list p cl)) + 0)).
    simpl in H.
    erewrite <- map_length in H.
    rewrite app_nth2_plus in H.
    simpl in H. apply H;[ assumption | assumption ].
+ apply (H 0).
Qed.

End Tc'_list.
