From Rela Require Import Proc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Inliner.
From Rela Require Total.
From Rela Require Import Sem_Prop.

From Coq Require Import Lia.
Import Arith.

(** Defintion of quadruple assertion **)

Definition q_assertion: Type := sigma ->sigma -> Prop.

Definition empty_q_assertion : q_assertion := (fun _ _ => False).

(** Definition of quadruple Precondition **)

Definition q_precondition : Type := sigma -> sigma -> Prop.

Definition empty_q_precondition : q_precondition := (fun _ _ => False).

(** Defintion of quadruple Postcondition **)

Definition q_postcondition : Type :=  sigma -> sigma -> sigma -> sigma -> Prop.

Definition empty_q_postcondition :  q_postcondition := (fun _ _ _ _ => True).

(** Definition of classical quadruple **)

Section Classical.

  Section relation.
    Context {A : Type}.
    Context (R: A -> A -> A -> A -> Prop).

    Inductive relation : A -> A -> option A -> option A -> Prop :=
      relation_bot : forall x1 x2:A, relation x1 x2 None None
    | relation_r :
      forall x1 x2 x3 x4: A, R x3 x4 x1 x2 -> relation x1 x2 (Some x3) (Some x4).
  End relation.

  Definition classical_quadruple (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) : Prop :=
    forall s1 s2, P s1 s2 -> relation Q s1 s2 (denot c1 s1 ps) (denot c2 s2 ps).

End Classical.

(** Definition of quadruple **)

Section Quadruple.

  Definition quadruple (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) : Prop :=
    forall s1 s2 s1' s2',
      P s1 s2 -> ceval c1 s1 ps s1' ->
      ceval c2 s2 ps s2' -> Q s1' s2' s1 s2.

  Lemma to_classical (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) :
    ((forall s2,Total.total (fun s1 => P s1 s2) (fun _ _ => True) c1 ps) /\
       (forall s1,Total.total (fun s2 => P s1 s2) (fun _ _ => True) c2 ps) /\
       quadruple P Q c1 c2 ps) ->
    classical_quadruple P Q c1 c2 ps.
  Proof.
    intros [Ht1 [Ht2 H]] s1 s2 HP.
    specialize (Ht1 s2 s1 HP) as [n1 [H1 _]].
    specialize (Ht2 s1 s2 HP) as [n2 [H2 _]].
    rewrite (sn_ds _ _ _ _  H1).
    rewrite (sn_ds _ _ _ _  H2).
    apply relation_r.
    apply H;assumption.
  Qed.

  Lemma from_classical (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) :
    classical_quadruple P Q c1 c2 ps ->
    quadruple P Q c1 c2 ps.
  Proof.
    intros H s1 s2 s1' s2' HP H1 H2.
    specialize (H s1 s2 HP).
    rewrite (sn_ds _ _ _ _  H1) in H.
    rewrite (sn_ds _ _ _ _  H2) in H.
    now inversion H;subst.
  Qed.

End Quadruple.

(** Definition of coterminating quadruple **)

Section Co_quadruple.

  Definition co_termination (P: q_precondition) (c1 c2: com)
    (ps : Psi.psi) : Prop :=
    forall s1 s2, P s1 s2 ->
              ((exists s', ceval c1 s1 ps s') <-> (exists s', ceval c2 s2 ps s')).

  Definition co_quadruple (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) : Prop :=
    co_termination P c1 c2 ps /\ quadruple P Q c1 c2 ps.

  Lemma co_to_classical (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) :
    co_quadruple P Q c1 c2 ps ->
    classical_quadruple P Q c1 c2 ps.
  Proof.
    intros H s1 s2 HP.
    destruct H as [Hco Hq].
    specialize (Hco s1 s2 HP).
    destruct Hco as [Hco1 Hco2].
    case_eq (denot c1 s1 ps).
    - intros s' HE1.
      specialize (ds_sn _ _ _ _ HE1) as Ht1.
      assert (Ht1e: (exists s' : sigma, ceval c1 s1 ps s')) by eauto.
      specialize (Hco1 Ht1e) as [s'' Ht2].
      rewrite (sn_ds _ _ _ _ Ht2).
      apply relation_r.
      now apply Hq.
    - intros HE1.
      case_eq (denot c2 s2 ps).
      + intros s' HE2.
        specialize (ds_sn _ _ _ _ HE2) as Ht2.
        assert (Ht2e: (exists s' : sigma, ceval c2 s2 ps s')) by eauto.
        specialize (Hco2 Ht2e) as [? Ht1].
        rewrite (sn_ds _ _ _ _ Ht1) in HE1.
        discriminate HE1.
      + intros ?.
        apply relation_bot.
  Qed.

  Lemma co_from_classical (P: q_precondition) (Q: q_postcondition)
    (c1 c2: com) (ps : Psi.psi) :
    classical_quadruple P Q c1 c2 ps ->
    co_quadruple P Q c1 c2 ps.
  Proof.
    intros Hr.
    split.
    - intros s1 s2 HP.
      specialize (Hr s1 s2 HP).
      split.
      + intros [s1' HE1].
        rewrite (sn_ds _ _ _ _ HE1) in Hr.
        inversion Hr.
        symmetry in H2.
        specialize (ds_sn _ _ _ _ H2) as Ht2.
        eauto.
      + intros [s2' HE2].
        rewrite (sn_ds _ _ _ _ HE2) in Hr.
        inversion Hr.
        symmetry in H.
        specialize (ds_sn _ _ _ _ H) as Ht1.
        eauto.
    - now apply from_classical.
  Qed.

End Co_quadruple.

(** Definition of a quadruple properties with inliner for loops **)

Definition i_quadruple (n: nat) (P: q_precondition) (Q: q_postcondition)
  (c1 c2 : com) (b1 b2: bexp) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 ->
                   ceval (unroll n b1 c1) s1 ps s1' -> ceval (unroll n b2 c2) s2 ps s2' ->
                   Q s1' s2' s1 s2.

Lemma qceval_n_inline_loop b1 b2 p1 p2 s1 s2 inv1 inv2 var1 var2 id1 id2 ps s1' s2':
  ceval (CWhile b1 p1 inv1 var1 id1) s1 ps s1' ->  ceval (CWhile b2 p2 inv2 var2 id2) s2 ps s2' ->
  exists n : nat, ceval (unroll n b1 p1) s1 ps s1' /\ ceval (unroll n b2  p2) s2 ps s2' .
Proof.
  intros Heval1  Heval2.
  apply ceval_unroll_n in Heval1.
  apply ceval_unroll_n in Heval2.
  destruct Heval1. destruct Heval2.
  destruct (Nat.max_dec x0 x).
  * exists x0.
    apply PeanoNat.Nat.max_l_iff in e.
    split.
    eapply unroll_ceval_S ;[apply H|assumption].
    apply H0.
  * exists x.
    apply PeanoNat.Nat.max_r_iff in e.
    split.
    apply H.
    eapply unroll_ceval_S;[apply H0|assumption].
Qed.

Lemma i_quadruple_quadruple P Q p1 p2 b1 b2 inv1 inv2 var1 var2 id1 id2 ps:
  quadruple P Q (CWhile b1 p1 inv1 var1 id1) (CWhile b2 p2 inv2 var2 id2) ps
  <-> forall n, i_quadruple n P Q p1 p2 b1 b2 ps.
Proof.
  unfold quadruple, i_quadruple;split;intros H.
  - intros n s1 s2 s1' s2' Pre Heval1 Heval2.
    eapply H.
    apply Pre.
    eapply unroll_n_ceval; apply Heval1.
    eapply unroll_n_ceval; apply Heval2.
  - intros s1 s2 s1' s2' Pre Heval1 Heval2.
    eapply qceval_n_inline_loop in Heval1; [|apply Heval2].
    destruct Heval1. destruct H0.
    eapply H ;eauto.
Qed.

(** Facts about quadruple Properties **)

Lemma while_quadruple (inv: q_assertion) b1 b2 c1 c2 id1 id2 ps:
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 =  true)
    (fun s1' s2' _ _ => inv s1' s2' /\ beval s1' b1 = beval s2' b2 ) c1 c2 ps ->
  quadruple ( fun s1 s2 => inv s1 s2 /\ beval s1 b1 = beval s2 b2 )
    ( fun s1' s2' _ _ => inv s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
    (CWhile b1 c1 (fun _=> True) (fun _ => 0) id1)
    (CWhile b2 c2 (fun _ => True) (fun _ => 0) id2) ps.
Proof.
  intros Hinv.
  apply i_quadruple_quadruple.
  intros n.
  induction n.
  - intros s1 s2 s1' s2' HP Heval1 Heval2.
    apply ceval_inf_loop in Heval1.
    contradiction Heval1.
  - intros s1 s2 s1' s2' HP Heval1 Heval2.
    destruct HP as [HP1 HP2].
    simpl in Heval1, Heval2.
    inversion Heval1;subst.
    + inversion Heval2;subst.
      * inversion H6;subst.
        inversion H8;subst.
        eapply IHn.
        eapply Hinv.
        split;[apply HP1 | rewrite H5,H7;auto ].
        all: try eauto.
      * rewrite H5,H7 in HP2; now auto.
    + inversion Heval2;subst.
      *  rewrite H5,H7 in HP2.
         inversion HP2.
      * inversion H6;subst.
        inversion H8;subst.
        rewrite H5,H7.
        auto.
Qed.

Definition bi_quadruple (i: nat) (P: q_precondition) (Q: q_postcondition)
  (c1 c2 : com) (b1 b2: bexp) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2' n m , i = n + m -> P s1 s2 ->
                        ceval (unroll n b1 c1) s1 ps s1' ->
                        ceval (unroll m b2 c2) s2 ps s2' ->
                        Q s1' s2' s1 s2.

Lemma qceval_n_b_inline_loop p1 p2 b1 b2 inv1 inv2 var1 var2 id1 id2 s1 s2 ps s1' s2':
  ceval (CWhile b1 p1 inv1 var1 id1) s1 ps s1' -> ceval (CWhile b2 p2 inv2 var2 id2) s2 ps s2' ->
  exists n m: nat, ceval (Inliner.unroll n b1 p1) s1 ps s1' /\ ceval (Inliner.unroll m b2 p2) s2 ps s2' .
Proof.
  intros Heval1  Heval2.
  apply ceval_unroll_n in Heval1.
  apply ceval_unroll_n in Heval2.
  destruct Heval1. destruct Heval2.
  exists x. exists x0.
  split.
  apply H.
  apply H0.
Qed.

Lemma bi_quadruple_quadruple P Q p1 p2 b1 b2 inv1 inv2 var1 var2 id1 id2 ps:
  quadruple P Q (CWhile b1 p1 inv1 var1 id1) (CWhile b2 p2 inv2 var2 id2) ps <->
    forall n, bi_quadruple n P Q p1 p2 b1 b2 ps.
Proof.
  unfold quadruple, bi_quadruple;split;intros H.
  * intros i s1 s2 s1' s2' n m Hi Pre Heval1 Heval2.
    eapply H.
    apply Pre.
    eapply unroll_n_ceval; apply Heval1.
    eapply unroll_n_ceval; apply Heval2.
  * intros s1 s2 s1' s2' Pre Heval1 Heval2.
    eapply qceval_n_b_inline_loop in  Heval1; [| apply Heval2].
    destruct Heval1. destruct H0. destruct H0.
    eapply (H (x0 + x)).
    reflexivity.
    apply Pre.
    assumption.
    assumption.
Qed.

(** Definition of condition for selecting the one side rules **)

Definition q_cond: Type := sigma -> sigma -> bool.

Definition empty_q_cond : q_cond := (fun _ _ => false).

(** Definition of while contract for quadruple **)

Definition wq_clause : Type := q_cond * q_cond * q_assertion.

Definition empty_wq_clause : wq_clause :=
  (empty_q_cond, empty_q_cond,empty_q_assertion).

Definition get_wq_inv (an: wq_clause) :=
  let (_,inv) := an in
  inv.

Definition get_wq_L (an: wq_clause) :=
  let (an, _) := an in
  let (L, _) := an in
  L.

Definition get_wq_R (an: wq_clause) :=
  let (an, _) := an in
  let (_, R) := an in
  R.

(** Definition of relational invariant environments **)

Module QW_Phi.

  Definition phi : Type :=
    com -> bexp -> nat -> com -> bexp -> nat -> wq_clause.

  Definition empty_phi: phi :=
    fun _ _ _ _ _ _=> empty_wq_clause.

End QW_Phi.

Lemma simpl_side_condition b1 b2 L R s1 s2 :
  (beval s1 b1 = beval s2 b2 \/ (beval s1 b1 = true /\ L s1 s2 = true ) \/
     (beval s2 b2 = true /\ R s1 s2 = true)) ->
  ((beval s1 b1 = true /\ beval s2 b2 = true /\ L s1 s2 = false /\ R s1 s2 = false) \/
     (beval s1 b1 = false /\ beval s2 b2 = false) \/  (beval s1 b1 = true /\ L s1 s2 = true ) \/
     (beval s2 b2 = true /\ R s1 s2 = true)).
Proof.
  intros H.
  destruct H.
  * destruct (beval s1 b1) eqn: Hb1.
  + destruct (L s1 s2) eqn: HL.
  -  auto.
  - destruct (R s1 s2) eqn: HR.
    ** rewrite <- H. auto.
    ** rewrite <- H. auto.
    + rewrite <- H. auto.
      * destruct H.
    + destruct H. rewrite H,H0. auto.
    + destruct H. rewrite H,H0. auto.
Qed.

(* Possible instation of L and R are :
   L = X /\ (not b1 \/ not Y)
   R = Y /\ (not b2 \/ not X)

   where X and Y are the condition for executiong left or right.
   In addition following side condition must be ensured:
   b1 /\ b2 -> X \/ Y
   b1 /\ not b2 -> X
   not b1 /\ b2 -> Y

 *)

Lemma while_skedule_quadruple
  (inv : q_assertion) (L R : q_cond) b1 b2 c1 c2 id1 id2 ps:
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 = true /\
                         L s1 s2 = false /\ R s1 s2 = false)
    (fun s1' s2' _ _ => inv s1' s2')
    c1 c2 ps ->
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true  /\ L s1 s2 = true )
    (fun s1' s2' _ _ => inv s1' s2' )
    c1 CSkip ps ->
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s2 b2 = true  /\ R s1 s2 = true)
    (fun s1' s2' _ _ => inv s1' s2')
    CSkip c2 ps ->
  (forall s1 s2, inv s1 s2 ->
            beval s1 b1 = beval s2 b2 \/
              (beval s1 b1 = true /\ L s1 s2 = true ) \/
              (beval s2 b2 = true /\ R s1 s2 = true)) ->
  quadruple inv
    ( fun s1' s2' _ _ => inv s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
    (CWhile b1 c1 (fun _=> True) (fun _ => 0) id1)
    (CWhile b2 c2 (fun _ => True) (fun _ => 0) id2) ps.
Proof.
  intros Hinv1 Hinv2 Hinv3 Hinv.
  apply bi_quadruple_quadruple.
  induction n.
  - intros s1 s2 s1' s2' n m Hi HP Heval1 Heval2.
    symmetry in Hi.
    apply Nat.eq_add_0 in Hi.
    destruct Hi; subst.
    apply ceval_inf_loop in Heval1; now auto.
  - intros s1 s2 s1' s2' n1 n2 Hi HP Heval1 Heval2.
    destruct n1.
    apply ceval_inf_loop in Heval1; now auto.
    destruct n2.
    apply ceval_inf_loop in Heval2; now auto.
    specialize (Hinv _ _ HP).
    apply simpl_side_condition in Hinv.
    destruct Hinv.
    + inversion Heval1; subst.
      inversion Heval2; subst.
      inversion H7; subst.
      inversion H9; subst.
      inversion Hi.
      eapply IHn ;[ apply H1 | | | ].
      eapply Hinv1; [ split;[apply HP| apply H] | apply H2 | apply H3].
      assumption.
      eapply unroll_ceval_S;[apply H12 | Lia.lia].
      rewrite H8 in H; now auto.
      rewrite H6 in H; now auto.
    + destruct H.
      * inversion Heval1; subst.
        rewrite H6 in H; now auto.
        inversion Heval2; subst.
        rewrite H8 in H; now auto.
        inversion H7; subst.
        inversion H9; subst.
        auto.
      * destruct H.
        -- inversion Heval1; subst.
           inversion H7; subst.
           inversion Hi.
           eapply IHn; [ apply H1 | | | ].
           eapply Hinv2; [split; [apply HP| assumption] | apply H2| apply E_Skip].
           assumption. assumption.
           rewrite H6 in H; now auto.
        -- inversion Heval2; subst.
           inversion H7; subst.
           rewrite Nat.add_comm in Hi.
           inversion Hi.
           rewrite Nat.add_comm in H1.
           eapply IHn; [ apply H1 | | | ].
           eapply Hinv3; [split; [apply HP| assumption] | apply E_Skip | apply H2 ].
           assumption.  assumption.
           rewrite H6 in H; now auto.
Qed.

(** Definition of a quadruple contract **)

Definition q_clause : Type := q_precondition * q_postcondition * q_cond * q_cond * q_cond.

Definition empty_clause : q_clause :=
  (empty_q_precondition, empty_q_postcondition, fun _ _ => true, fun _ _ => true, fun _ _ => true).

Definition get_q_pre (an: q_clause) : q_precondition :=
  let (an,_) := an in
  let (l,_) := an in
  let (l,_) := l in
  let (pre,_) := l in
  pre.

Definition get_q_post (an:q_clause) : q_postcondition :=
  let (an,_) := an in
  let (l,_) := an in
  let (l,_) := l in
  let (_,post) := l in
  post.

Definition get_L (an:q_clause) : q_cond:=
  let (an,_) := an in
  let (l,_) := an in
  let (_,L) := l in
  L.

Definition get_R (an:q_clause) : q_cond :=
  let (an,_) := an in
  let (_,R) := an in
  R.

Definition get_LR (an: q_clause) : q_cond :=
  let (_,LR) := an in
  LR.

(** Definition of quadruple contract environments :
    a map from two procedure name to quadruple clauses **)

Module Q_Phi.

  Definition phi : Type := Proc.t -> Proc.t -> q_clause.

  Definition empty_phi: phi := fun _ _ => empty_clause.

End Q_Phi.

(** Defintion of quadruple with inliner **)

Definition bi_quadruple_fun_2 (i: nat) (P: q_precondition) (Q: q_postcondition)
  (c1 c2 : com) (ps1 ps2 : Psi.psi) : Prop :=
  forall s1 s2 s1' s2' n m, i = n + m -> P s1 s2 ->
                       ceval c1 s1 (Inline1.k_inliner_ps n ps1) s1' ->
                       ceval c2 s2 (Inline1.k_inliner_ps m ps2) s2' ->
                       Q s1' s2' s1 s2.

Lemma qceval_n_b_inline_fun_2 p1 p2 s1 s2 ps1 ps2 s1' s2':
  ceval p1 s1 ps1 s1' ->  ceval p2 s2 ps2 s2' ->
  exists n m: nat, ceval p1 s1 (Inline1.k_inliner_ps n ps1) s1' /\
               ceval p2 s2 (Inline1.k_inliner_ps m ps2) s2'.
Proof.
  intros Heval1  Heval2.
  apply Inline1.ceval_n_inline_ps in Heval1.
  apply Inline1.ceval_n_inline_ps in Heval2.
  destruct Heval1. destruct Heval2.
  exists x. exists x0.
  split.
  apply H.
  apply H0.
Qed.

Definition quadruple_2 (P: q_precondition) (Q: q_postcondition)
  (c1 c2: com) (ps1 ps2 : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 -> ceval c1 s1 ps1 s1' -> ceval c2 s2 ps2 s2' -> Q s1' s2' s1 s2.

Lemma bi_quadruple_quadruple_fun P Q p1 p2 ps1 ps2:
  quadruple_2 P Q p1 p2 ps1 ps2 <-> forall n, bi_quadruple_fun_2 n P Q p1 p2 ps1 ps2.
Proof.
  unfold quadruple_2, bi_quadruple_fun_2;split;intros H.
  * intros i s1 s2 s1' s2' n m Hi Pre Heval1 Heval2.
    eapply H.
    apply Pre.
    eapply (Inline1.n_inline_ps_ceval _ _ _ _ _ Heval1).
    eapply (Inline1.n_inline_ps_ceval _ _ _ _ _ Heval2).
  * intros s1 s2 s1' s2' Pre Heval1 Heval2.
    specialize (qceval_n_b_inline_fun_2 _ _ _ _ _ _ _ _  Heval1 Heval2).
    intros Heval. destruct Heval as [n Heval]. destruct Heval as [m Heval].
    destruct Heval as (Hevaln & Hevalm).
    specialize (H (n + m) s1 s2 s1' s2' n m).
    apply H.
    reflexivity.
    assumption.
    assumption.
    assumption.
Qed.

Definition quadruple_ctx_2 (rcl:Q_Phi.phi) (ps1 ps2: Psi.psi)
  (P: q_precondition) (Q : q_postcondition) (c1 c2:  com) :=
  (forall p1 p2, quadruple_2 (get_q_pre (rcl p1 p2))
              (get_q_post (rcl p1 p2)) (CCall p1) (CCall p2) ps1 ps2) ->
  quadruple_2 P Q c1 c2 ps1 ps2.


Definition quadruple_proc_ctx_2 (rcl : Q_Phi.phi) (ps_init_1 ps_init_2 :Psi.psi):=
  (forall p1 p2 ps1 ps2,
       quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_q_pre (rcl p1 p2) s1 s2 /\
                                               get_LR(rcl p1 p2) s1 s2 = true /\
                                               get_L(rcl p1 p2) s1 s2 = false /\
                                               get_R(rcl p1 p2) s1 s2 = false)
        (get_q_post (rcl p1 p2)) (ps_init_1 p1) (ps_init_2 p2)) /\
    (forall p1 p2 ps1 ps2,
        quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_q_pre (rcl p1 p2) s1 s2 /\
                                                 get_L(rcl p1 p2) s1 s2 = true)
          (get_q_post (rcl p1 p2)) (ps_init_1 p1) (CCall p2)) /\
    (forall p1 p2 ps1 ps2,
        quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_q_pre (rcl p1 p2) s1 s2 /\
                                                 get_R(rcl p1 p2) s1 s2 = true)
          (get_q_post (rcl p1 p2)) (CCall p1) (ps_init_2 p2)) /\
    (forall p1 p2 s1 s2,  get_q_pre (rcl p1 p2) s1 s2 ->
                     ((get_LR(rcl p1 p2) s1 s2 = true /\ get_L(rcl p1 p2) s1 s2 = false /\ get_R(rcl p1 p2) s1 s2 = false) \/
                       get_L(rcl p1 p2) s1 s2 = true \/ get_R(rcl p1 p2) s1 s2 = true)).

Lemma ext_q_recursive_proc ps1 ps2 rcl:
  quadruple_proc_ctx_2 rcl ps1 ps2 ->
  (forall p1 p2, quadruple_2 (get_q_pre (rcl p1 p2))
              (get_q_post (rcl p1 p2)) (CCall p1) (CCall p2) ps1 ps2).
Proof.
  intros.
  apply bi_quadruple_quadruple_fun.
  intros i.
  generalize dependent p2.
  generalize dependent p1.
  induction i.
  intros p1 p2 s1 s2 s1' s2' n m Hi HPre Heval1 Heval2.
  symmetry in Hi.
  apply Nat.eq_add_0 in Hi.
  destruct Hi; subst.
  inversion Heval1;subst.
  apply ceval_inf_loop in H1; now auto.
  intros p1 p2 s1 s2 s1' s2' n m Hi HPre Heval1 Heval2.
  destruct n.
  inversion Heval1;subst.
  apply ceval_inf_loop in H1; now auto.
  destruct m.
  inversion Heval2;subst.
  apply ceval_inf_loop in H1; now auto.
  unfold quadruple_proc_ctx_2 in H.
  decompose [and] H; clear H.
  specialize (H4 p1 p2 s1 s2 HPre).
  destruct H4.
  - eapply H0.
    + intros p0 p3 s0 s1'0 s2'0 s2'1 H5 H6 H7.
      assert (H12: i = n + S m) by lia.
      eapply IHi;[apply H12|apply H5|apply H6|apply H7].
    + split. apply HPre. apply H.
    + apply Inline1.n_inline_ps_inline in Heval1.
      apply Heval1.
    + apply Inline1.ceval_n_inline_ps_S with (m:= S (S m)) in Heval2 ;[| lia].
      apply Inline1.n_inline_ps_inline in Heval2.
      apply Heval2.
  - destruct H.
    + eapply H2.
      * intros p0 p3 s0 s1'0 s2'0 s2'1 H5 H6 H7.
        assert (H12: i = n + S m) by lia.
        eapply IHi;[apply H12|apply H5|apply H6|apply H7].
      * split. apply HPre. apply H.
      * apply Inline1.n_inline_ps_inline in Heval1.
        apply Heval1.
      * apply Heval2.
    + eapply H1.
      * intros p0 p3 s0 s1'0 s2'0 s2'1 H5 H6 H7.
        assert (H12: i = S n + m) by lia.
        eapply IHi;[apply H12|apply H5|apply H6|apply H7].
      * split. apply HPre. apply H.
      * apply Heval1.
      * apply Inline1.n_inline_ps_inline in Heval2.
        apply Heval2.
Qed.

Definition quadruple_ctx (rcl:Q_Phi.phi) (ps: Psi.psi)
  (P: q_precondition) (Q : q_postcondition) (c1 c2:  com) :=
  quadruple_ctx_2 rcl ps ps P Q c1 c2.

Definition quadruple_proc_ctx (rcl : Q_Phi.phi) (ps_init :Psi.psi):=
  quadruple_proc_ctx_2 rcl ps_init ps_init.

Theorem recursion_quadruple :
  forall P Q p1 p2 ps rcl,
    quadruple_proc_ctx rcl ps  ->
    quadruple_ctx rcl ps P Q p1 p2 ->
    quadruple P Q p1 p2 ps.
Proof.
  intros.
  apply H0.
  apply ext_q_recursive_proc.
  apply H.
Qed.

Import AexpNotations.
Import BexpNotations.
Import ComNotations.
From Rela Require Import Aexp.
From Rela Require Import Bexp.

Module While_Proc.
  Parameter c1 : com.
  Parameter c2 : com.
  Parameter b1: bexp.
  Parameter b2: bexp.

  Definition w1: com :=
    <[ if {b1} then
         {c1};
         call(1)
       else
         skip
       end ]>.

  Definition w2: com :=
    <[ if {b2} then
         {c2};
         call(2)
       else
         skip
       end ]>.

  Definition ps (x': Proc.t) :=
    if Proc.eqb x' 1 then  w1 else
      if Proc.eqb x' 2 then  w2 else Psi.empty_psi x'.

  Parameter invar: q_assertion.

  Definition q_pre : q_precondition := invar.

  Definition q_post : q_postcondition := fun m1 m2 _ _ => invar m1 m2 /\
                                                         beval m1 b1 = false /\
                                                         beval m2 b2 = false.

  Parameter L: q_cond.
  Parameter R : q_cond.

  Definition Lc s1 s2 := andb (L s1 s2) (beval s1 b1).
  Definition Rc s1 s2 := andb (R s1 s2) (beval s2 b2).
  Definition LR s1 s2 := negb (xorb (beval s1 b1) (beval s2 b2)).

  Definition rcl (f1' f2': Proc.t) : q_clause :=
    if andb (Proc.eqb f1' 1) (Proc.eqb f2' 2)
    then (q_pre,q_post, Lc, Rc, LR)
    else Q_Phi.empty_phi f1' f2'.

  Lemma ext_q_recursive_proc_1_2:
  quadruple_proc_ctx_2 rcl ps ps ->
  quadruple_2 (get_q_pre (rcl 1 2))
              (get_q_post (rcl 1 2)) (CCall 1) (CCall 2) ps ps.
  Proof.
    intros.
    specialize (ext_q_recursive_proc ps ps rcl H 1 2).
    auto.
  Qed.

  Lemma inv_proc :
    (forall ps1 ps2,
        quadruple_2 (fun s1 s2 => invar s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 = true /\
                                 L s1 s2 = false /\ R s1 s2 = false)
          (fun s1' s2' _ _ => invar s1' s2')
          c1 c2 ps1 ps2) ->
    (forall ps1 ps2,
        quadruple_2 (fun s1 s2 => invar s1 s2 /\ beval s1 b1 = true  /\ L s1 s2 = true )
          (fun s1' s2' _ _ => invar s1' s2' )
          c1 CSkip ps1 ps2) ->
    (forall ps1 ps2,
        quadruple_2 (fun s1 s2 => invar s1 s2 /\ beval s2 b2 = true  /\ R s1 s2 = true)
          (fun s1' s2' _ _ => invar s1' s2')
          CSkip c2 ps1 ps2) ->
    (forall s1 s2, invar s1 s2 ->
              beval s1 b1 = beval s2 b2 \/
                (beval s1 b1 = true /\ L s1 s2 = true ) \/
                (beval s2 b2 = true /\ R s1 s2 = true)) ->
    quadruple (get_q_pre (rcl 1 2))
      (get_q_post (rcl 1 2)) (CCall 1) (CCall 2) ps.
  Proof.
    intros.
    apply ext_q_recursive_proc_1_2.
    unfold rcl, ps, q_pre, q_post.
    unfold quadruple_proc_ctx_2.
    split.
    + unfold quadruple_ctx_2.
      intros.
      destruct (p1 =? 1) eqn: He1.
      destruct (p2 =? 2) eqn: He2.
      simpl.
      intros s1 s2 s1' s2' HPre Heval1 Heval2.
      unfold LR, Lc, Rc in HPre.
      decompose [and] HPre;clear HPre.
      rewrite Bool.negb_xorb in H6.
      rewrite Bool.eqb_true_iff in H6.
      unfold w1 in Heval1.
      apply Loc.Loc.eqb_eq in He2;subst.
      simpl in Heval2.
      unfold w2 in Heval2.
      inversion Heval1;subst;clear Heval1.
      inversion H15;subst;clear H15.
      inversion Heval2;subst;clear Heval2.
      inversion H18;subst;clear H18.
      specialize (H3 1 2).
      simpl in H3.
      eapply H3.
      eapply H.
      repeat split; eauto.
      rewrite H14 in H5.
      destruct (Bool.andb_false_elim _ _ H5) as [| H20];[auto|inversion H20].
      rewrite H17 in H8.
      destruct (Bool.andb_false_elim _ _ H8) as [| H21];[auto|inversion H21].
      eauto. eauto. auto. auto.
      rewrite H14, H17 in H6.
      inversion H6.
      inversion Heval2;subst;clear Heval2.
      inversion H17;subst;clear H17.
      rewrite H14, H16 in H6.
      inversion H6.
      inversion H15;subst.
      inversion H17; subst.
      repeat split;auto.
      simpl.
      intros s1 s2 s1' s2' HPre Heval1 Heval2.
      unfold empty_q_postcondition; auto.
      simpl.
      intros s1 s2 s1' s2' HPre Heval1 Heval2.
      unfold empty_q_postcondition; auto.
    + split.
      - unfold quadruple_ctx_2.
        intros.
        destruct (p1 =? 1) eqn: He1.
        destruct (p2 =? 2) eqn: He2.
        simpl.
        intros s1 s2 s1' s2' HPre Heval1 Heval2.
        unfold LR, Lc, Rc in HPre.
        decompose [and] HPre;clear HPre.
        unfold w1 in Heval1.
        inversion Heval1;subst;clear Heval1.
        inversion H13;subst;clear H13.
        specialize (H3 1 2).
        simpl in H3.
        eapply H3.
        eapply H0.
        repeat split; eauto.
        rewrite H12 in H5.
        destruct (andb_prop _ _ H5) as [H15 _];auto.
        eauto. apply (E_Skip s2 ps2). auto. auto.
        apply Loc.Loc.eqb_eq in He2;subst.
        auto.
        destruct (andb_prop _ _ H5) as [_ H15].
        rewrite H15 in H12.
        inversion H12.
        simpl.
        intros s1 s2 s1' s2' HPre Heval1 Heval2.
        unfold empty_q_postcondition; auto.
        simpl.
        intros s1 s2 s1' s2' HPre Heval1 Heval2.
        unfold empty_q_postcondition; auto.
      - split.
        * unfold quadruple_ctx_2.
          intros.
          destruct (p1 =? 1) eqn: He1.
          destruct (p2 =? 2) eqn: He2.
          simpl.
          intros s1 s2 s1' s2' HPre Heval1 Heval2.
          unfold LR, Lc, Rc in HPre.
          decompose [and] HPre;clear HPre.
          apply Loc.Loc.eqb_eq in He2;subst.
          simpl in Heval2.
          unfold w2 in Heval2.
          inversion Heval2;subst;clear Heval2.
          inversion H13;subst;clear H13.
          specialize (H3 1 2).
          simpl in H3.
          eapply H3.
          eapply H1.
          repeat split; eauto.
          rewrite H12 in H5.
          destruct (andb_prop _ _ H5) as [H15 _];auto.
          apply (E_Skip s1 ps1). eauto.
          apply Loc.Loc.eqb_eq in He1;subst.
          auto.
          auto.
          destruct (andb_prop _ _ H5) as [_ H15].
          rewrite H15 in H12.
          inversion H12.
          simpl.
          intros s1 s2 s1' s2' HPre Heval1 Heval2.
          unfold empty_q_postcondition; auto.
          simpl.
          intros s1 s2 s1' s2' HPre Heval1 Heval2.
          unfold empty_q_postcondition; auto.
        * intros.
          destruct (p1 =? 1) eqn: He1.
          destruct (p2 =? 2) eqn: He2.
          --  simpl.
              simpl in H3.
              specialize (H2 _ _ H3).
              unfold LR, Lc, Rc.
              apply simpl_side_condition in H2.
              destruct H2.
              ++ left.
                 decompose [and] H2;clear H2.
                 rewrite H4, H6, H5, H8.
                 auto.
              ++ destruct H2.
                 ** left.
                    decompose [and] H2;clear H2.
                    rewrite H4, H5.
                    rewrite Bool.andb_false_r.
                    rewrite Bool.andb_false_r.
                    auto.
                 ** destruct H2.
                    decompose [and] H2;clear H2.
                    right.
                    left.
                    rewrite H4, H5.
                    auto.
                    decompose [and] H2;clear H2.
                    right.
                    right.
                    rewrite H4, H5.
                    auto.
          -- simpl. auto.
          -- simpl. auto.
  Qed.

End While_Proc.
