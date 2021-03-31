From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Vcg.
From Rela Require Import Hoare_Triple.

Import Vcg.Why3_Set.
Import Vcg.Assn_b.

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

Fixpoint tc (c: com) (m m': Sigma.sigma)
            (cl: Phi.phi) (fin: Prop -> Prop): Prop :=
    match c with
    | CSkip => fin (m = m')
    | CAss x a => fin (m' = set m x (aeval m a))
    | CAssert b =>  fin (b m /\ m = m')
    | CSeq p1 p2 => forall m'', 
        tc p1 m m'' cl (fun f1 => tc p2 m'' m' cl (fun f2 => fin (f1 /\ f2)))
    | CIf b p1 p2 =>
        tc p1 m m' cl (fun p1 => 
        tc p2 m m' cl (fun p2 => 
            fin (branch (bassn b m) p1 p2)))
    | CWhile b p inv => fin (inv m /\ inv m' /\ beval m' b = false)
    | CCall f => fin((get_pre (cl f)) m /\ (get_post (cl f)) m')
    end.

Lemma consequence_tc_suite :
forall p cl m m' (suite1 suite2 : Prop -> Prop),
(forall p, suite1 p -> suite2 p) ->
tc p m m' cl suite1 -> tc p m m' cl suite2.
Proof.
intros p cl.
induction p.
  * simpl. intros.
    apply H.
    apply H0.
  * simpl. intros.
    apply H.
    apply H0.
  * simpl. intros.
    apply H.
    apply H0.
  * simpl. intros.
    eapply IHp1 with (fun p => tc p2 m'' m' cl (fun f2 : Prop => suite1 (p /\ f2))).
    - intros.
      eapply IHp2 with (fun f => suite1(p /\ f)).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * simpl. intros.
    eapply IHp1 with 
     (fun p => tc p2 m m' cl (fun f2 : Prop => suite1 (branch (bassn b m) p f2))).
    - intros.
      eapply IHp2 with (fun f => suite1 (branch (bassn b m) p f)).
       + intros. apply H. assumption.
       + apply H1.
    - apply H0.
  * simpl. intros. 
    apply H.
    apply H0.
  * simpl. intros. 
    apply H.
    apply H0.
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

Lemma prenexe_tc :
forall p m m' cl (suite : sigma -> Prop -> Prop),
(forall s, tc p m m' cl (suite s)) ->
tc p m m' cl (fun f => forall s,suite s f).
Proof.
induction p;simpl.
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
bassn b m ->
tc p1 m m' cl (fun f1 => 
tc p2 m m' cl (fun f2 =>  branch (bassn b m) f1 f2 -> suite)) ->
tc p1 m m' cl (fun f1 => 
tc p2 m m' cl (fun f2 => f1 -> suite)).
Proof.
intros.
apply (consequence_tc_suite _ _ _ _ 
             (fun f1 => tc p2 m m' cl (fun f2 => 
              branch (bassn b m) f1 f2 -> suite))).
* intros.
  apply (consequence_tc_suite _ _ _ _ 
        (fun f2 => branch (bassn b m) p f2 -> suite)).
  - intros. apply H2.
    apply Then.
    all: try assumption.
  - assumption.
* assumption.
Qed.

Lemma opt_1_false:
forall p1 p2 b m m' cl (suite : Prop),
~bassn b m ->
tc p1 m m' cl (fun f1 => 
tc p2 m m' cl (fun f2 =>  branch (bassn b m) f1 f2 -> suite)) ->
tc p1 m m' cl (fun f1 => 
tc p2 m m' cl (fun f2 => f2 -> suite)).
Proof.
intros.
apply (consequence_tc_suite _ _ _ _ 
             (fun f1 => tc p2 m m' cl (fun f2 => 
              branch (bassn b m) f1 f2 -> suite))).
* intros.
  apply (consequence_tc_suite _ _ _ _ 
        (fun f2 => branch (bassn b m) p f2 -> suite)).
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

Lemma tc_same :
forall p cl m (suite1 : Sigma.sigma -> Prop),
(forall m', tc p m m' cl (fun p => p -> suite1 m')) -> Vcg.tc p m cl suite1.
Proof.
intros.
generalize dependent suite1.
generalize dependent m.
induction p;simpl.
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
    specialize (opt_1_false p1 p2 b m m' cl (suite1 m') H0 H).
    intros.
    apply (simpl_tc p1 m m' cl (tc p2 m m' cl (fun p : Prop => p -> suite1 m'))).
    apply H1.
* intros.
  apply H.
  auto.
* intros.
  apply H.
  auto.
Qed.

Fixpoint tc' (c : com) (m: Sigma.sigma)
            (cl: Phi.phi) : Prop :=
match c with
 | CSkip => True
 | CAss x a => True
 | CAssert b => b m
 | CSeq p1 p2 => tc' p1 m cl /\
                 forall m'',
                 tc p1 m m'' cl (fun f => f -> tc' p2 m'' cl)
 | CIf b p1 p2 =>
      (bassn b m -> tc' p1 m cl) /\ (~bassn b m -> tc' p2 m cl)
 | CWhile b p inv => inv m /\
                    (forall m', bassn b m' -> tc' p m' cl) /\
                    (forall m' m'', inv m'  -> tc p m' m'' cl (fun f => f -> inv m''))
 | CCall f => (get_pre (cl f)) m
end.

Lemma tc'_same :
forall p cl m,
tc' p m cl -> Vcg.tc' p m cl.
Proof.
induction p; simpl.
* intros. auto.
* intros. auto.
* intros.  apply H.
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
    apply H. assumption.
  - apply IHp2.
    apply H. assumption.
* intros.
  split.
  - apply H.
  - split;intros.
    + apply IHp.
      apply H.
      assumption.
    + apply tc_same.
      intros.
      apply H.
      assumption.
* intros. apply H.
Qed.

Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m m', (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m m' cl (fun p => p -> (get_post (cl f)) m').

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