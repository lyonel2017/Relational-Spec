From Rela Require Import Proc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Inliner.

From Coq Require Import Lia.
Import Arith.

(** Defintion of quadruple assertion **)

Definition r_assertion: Type := sigma ->sigma -> Prop.

(** Definition of quadruple Precondition **)

Definition r_precondition : Type := sigma -> sigma -> Prop.

Definition empty_r_precondition : r_precondition := (fun _ _ => False).

(** Defintion of quadruple Postcondition **)

Definition r_postcondition : Type :=  sigma -> sigma -> sigma -> sigma -> Prop.

Definition empty_r_postcondition :  r_postcondition := (fun _ _ _ _ => True).

(** Definition of quadruple **)

Definition quadruple (P: r_precondition) (Q: r_postcondition)
  (c1 c2: com) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 -> ceval c1 s1 ps s1' -> ceval c2 s2 ps s2' -> Q s1' s2' s1 s2.

(** Definition of a quadruple properties with inliner for loops **)

Definition i_quadruple (n: nat) (P: r_precondition) (Q: r_postcondition)
  (c1 c2 : com) (b1 b2: bexp) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2', P s1 s2 ->
                   ceval (unroll n b1 c1) s1 ps s1' -> ceval (unroll n b2 c2) s2 ps s2' ->
                   Q s1' s2' s1 s2.

Lemma qceval_n_inline_loop b1 b2 p1 p2 s1 s2 inv1 inv2 var1 var2 ps s1' s2':
  ceval (CWhile b1 p1 inv1 var1) s1 ps s1' ->  ceval (CWhile b2 p2 inv2 var2) s2 ps s2' ->
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
    eapply unroll_ceval_S;[apply H|assumption].
    apply H0.
  * exists x.
    apply PeanoNat.Nat.max_r_iff in e.
    split.
    apply H.
    eapply unroll_ceval_S;[apply H0|assumption].
Qed.

Lemma i_quadruple_quadruple P Q p1 p2 b1 b2 inv1 inv2 var1 var2 ps:
  quadruple P Q (CWhile b1 p1 inv1 var1) (CWhile b2 p2 inv2 var2) ps
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

Lemma while_quadruple (inv: r_assertion) b1 b2 c1 c2 ps:
  quadruple (fun s1 s2 => inv s1 s2 /\ beval s1 b1 = true /\ beval s2 b2 =  true)
    (fun s1' s2' _ _ => inv s1' s2' /\ beval s1' b1 = beval s2' b2 ) c1 c2 ps ->
  quadruple ( fun s1 s2 => inv s1 s2 /\ beval s1 b1 = beval s2 b2 )
    ( fun s1' s2' _ _ => inv s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
    (CWhile b1 c1 (fun _=> True) (fun _ => 0))
    (CWhile b2 c2 (fun _ => True) (fun _ => 0)) ps.
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

Definition bi_quadruple (i: nat) (P: r_precondition) (Q: r_postcondition)
  (c1 c2 : com) (b1 b2: bexp) (ps : Psi.psi) : Prop :=
  forall s1 s2 s1' s2' n m , i = n + m -> P s1 s2 ->
                        ceval (unroll n b1 c1) s1 ps s1' ->
                        ceval (unroll m b2 c2) s2 ps s2' ->
                        Q s1' s2' s1 s2.

Lemma qceval_n_b_inline_loop p1 p2 b1 b2 inv1 inv2 var1 var2 s1 s2 ps  s1' s2':
  ceval (CWhile b1 p1 inv1 var1) s1 ps s1' -> ceval (CWhile b2 p2 inv2 var2) s2 ps s2' ->
  exists n m: nat, ceval (unroll n b1 p1) s1 ps s1' /\ ceval (unroll m b2 p2) s2 ps s2' .
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

Lemma bi_quadruple_quadruple P Q p1 p2 b1 b2 inv1 inv2 var1 var2 ps:
  quadruple P Q (CWhile b1 p1 inv1 var1) (CWhile b2 p2 inv2 var2) ps <->
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

Definition r_cond: Type := sigma -> sigma -> bool.

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

Lemma while_skedule_quadruple (inv : r_assertion) (L R : r_cond) b1 b2 c1 c2 ps:
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
    (CWhile b1 c1 (fun _=> True) (fun _ => 0))
    (CWhile b2 c2 (fun _ => True) (fun _ => 0)) ps.
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

Definition r_clause : Type := r_precondition * r_postcondition * r_cond * r_cond * r_cond.

Definition empty_clause : r_clause :=
  (empty_r_precondition, empty_r_postcondition, fun _ _ => true, fun _ _ => true, fun _ _ => true).

Definition get_r_pre (an: r_clause) : r_precondition :=
  let (an,_) := an in
  let (l,_) := an in
  let (l,_) := l in
  let (pre,_) := l in
  pre.

Definition get_r_post (an:r_clause) : r_postcondition :=
  let (an,_) := an in
  let (l,_) := an in
  let (l,_) := l in
  let (_,post) := l in
  post.

Definition get_L (an:r_clause) : r_cond:=
  let (an,_) := an in
  let (l,_) := an in
  let (_,L) := l in
  L.

Definition get_R (an:r_clause) : r_cond :=
  let (an,_) := an in
  let (_,R) := an in
  R.

Definition get_LR (an: r_clause) : r_cond :=
  let (_,LR) := an in
  LR.

(** Definition of quadruple contract environments :
    a map from two procedure name to quadruple clauses **)

Module R_Phi.

  Definition r_phi : Type := Proc.t -> Proc.t -> r_clause.

  Definition empty_r_phi: r_phi := fun _ _ => empty_clause.

End R_Phi.

(** Defintion of quadruple with inliner **)

Definition bi_quadruple_fun_2 (i: nat) (P: r_precondition) (Q: r_postcondition)
  (c1 c2 : com) (ps1 ps2 : Psi.psi) : Prop :=
  forall s1 s2 s1' s2' n m, i = n + m -> P s1 s2 ->
                       ceval c1 s1 (Inline1.k_inliner_ps n ps1) s1' ->
                       ceval c2 s2 (Inline1.k_inliner_ps m ps2) s2' ->
                       Q s1' s2' s1 s2.

Lemma qceval_n_b_inline_fun_2 p1 p2 s1 s2 ps1 ps2 s1' s2':
  ceval p1 s1 ps1 s1' ->  ceval p2 s2 ps2 s2' ->
  exists n m: nat, ceval p1 s1 (Inline1.k_inliner_ps n ps1) s1' /\ ceval p2 s2 (Inline1.k_inliner_ps m ps2) s2'.
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

Definition quadruple_2 (P: r_precondition) (Q: r_postcondition)
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

Definition quadruple_ctx_2 (rcl:R_Phi.r_phi) (ps1 ps2: Psi.psi)
  (P: r_precondition) (Q : r_postcondition) (c1 c2:  com) :=
  (forall p1 p2, quadruple_2 (get_r_pre (rcl p1 p2))
              (get_r_post (rcl p1 p2)) (CCall p1) (CCall p2) ps1 ps2) ->
  quadruple_2 P Q c1 c2 ps1 ps2.


Definition quadruple_proc_ctx_2 (rcl : R_Phi.r_phi) (ps_init_1 ps_init_2 :Psi.psi):=
  (forall p1 p2 ps1 ps2,
      quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_r_pre (rcl p1 p2) s1 s2 /\
                                               get_LR(rcl p1 p2) s1 s2 = true /\
                                               get_L(rcl p1 p2) s1 s2 = false /\
                                               get_R(rcl p1 p2) s1 s2 = false)
        (get_r_post (rcl p1 p2)) (ps_init_1 p1) (ps_init_2 p2)) /\
    (forall p1 p2 ps1 ps2,
        quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_r_pre (rcl p1 p2) s1 s2 /\
                                                 get_L(rcl p1 p2) s1 s2 = true)
          (get_r_post (rcl p1 p2)) (ps_init_1 p1) (CCall p2)) /\
    (forall p1 p2 ps1 ps2,
        quadruple_ctx_2 rcl ps1 ps2 (fun s1 s2 => get_r_pre (rcl p1 p2) s1 s2 /\
                                                 get_R(rcl p1 p2) s1 s2 = true)
          (get_r_post (rcl p1 p2)) (CCall p1) (ps_init_2 p2)) /\
    (forall p1 p2 s1 s2,  get_r_pre (rcl p1 p2) s1 s2 ->
                     ((get_LR(rcl p1 p2) s1 s2 = true /\ get_L(rcl p1 p2) s1 s2 = false /\ get_R(rcl p1 p2) s1 s2 = false) \/
                       get_L(rcl p1 p2) s1 s2 = true \/ get_R(rcl p1 p2) s1 s2 = true)).

Lemma ext_r_recursive_proc ps1 ps2 rcl:
  quadruple_proc_ctx_2 rcl ps1 ps2 ->
  (forall p1 p2, quadruple_2 (get_r_pre (rcl p1 p2))
              (get_r_post (rcl p1 p2)) (CCall p1) (CCall p2) ps1 ps2).
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

Definition quadruple_ctx (rcl:R_Phi.r_phi) (ps: Psi.psi)
  (P: r_precondition) (Q : r_postcondition) (c1 c2:  com) :=
  quadruple_ctx_2 rcl ps ps P Q c1 c2.

Definition quadruple_proc_ctx (rcl : R_Phi.r_phi) (ps_init :Psi.psi):=
  quadruple_proc_ctx_2 rcl ps_init ps_init.

Theorem recursion_quadruple :
  forall P Q p1 p2 ps rcl,
    quadruple_proc_ctx rcl ps  ->
    quadruple_ctx rcl ps P Q p1 p2 ->
    quadruple P Q p1 p2 ps.
Proof.
  intros.
  apply H0.
  apply ext_r_recursive_proc.
  apply H.
Qed.

Module Test.
  Definition f1 : Proc.t:= 1.
  Definition f2 : Proc.t:= 2.
  Parameter c1 : com.
  Parameter c2 : com.
  Parameter b1: bexp.
  Parameter b2: bexp.

  From Rela Require Import Aexp.
  From Rela Require Import Bexp.

  Import AexpNotations.
  Import BexpNotations.
  Import ComNotations.

  Definition w1: com :=
    <[ if {b1} then
         {c1};
         call(f1)
       else
         skip
       end ]>.

  Definition w2: com :=
    <[ if {b2} then
         {c2};
         call(f2)
       else
         skip
       end ]>.

  Definition ps (x': Proc.t) :=
    if Proc.eqb x' f1 then  w1 else
      if Proc.eqb x' f2 then  w2 else Psi.empty_psi x'.

  Parameter invar: r_assertion.

  Definition r_pre : r_precondition := invar.

  Definition r_post : r_postcondition := fun m1 m2 _ _ => invar m1 m2.

  Parameter L: r_cond.
  Parameter R : r_cond.

  Definition Lc s1 s2 := andb (L s1 s2) (beval s1 b1).
  Definition Rc s1 s2 := andb (R s1 s2) (beval s2 b2).
  Definition LR s1 s2 := negb (xorb (beval s1 b1) (beval s2 b2)).

  Definition rcl (f1' f2': Proc.t) : r_clause :=
    if andb (Proc.eqb f1 f1') (Proc.eqb f2 f2')
    then (r_pre,r_post, Lc, Rc, LR)
    else R_Phi.empty_r_phi f1' f2'.

  Lemma test :
    (forall p1 p2, quadruple_2 (get_r_pre (rcl p1 p2))
                (get_r_post (rcl p1 p2)) (CCall p1) (CCall p2) ps ps) ->
    quadruple_proc_ctx rcl ps ->
    quadruple invar
      ( fun s1' s2' _ _ => invar s1' s2' /\ beval s1' b1 = false /\ beval s2' b2 = false )
      (CWhile b1 c1 (fun _=> True) (fun _ => 0))
      (CWhile b2 c2 (fun _ => True) (fun _ => 0)) ps.
  Proof.
    intros H0 H.
    unfold rcl in H.
    apply (while_skedule_quadruple _ L R).
    - unfold quadruple_proc_ctx in H.
      unfold quadruple_proc_ctx_2 in H.
      destruct H.
      clear H1.
      specialize (H f1 f2 ps ps).
      unfold quadruple_ctx_2 in H.
      specialize (H H0).
      simpl in H.
      unfold r_pre, r_post, Lc, Rc, LR in H.
      intros s1 s2 s1' s2' Hpre Heval1 Heval2.
      specialize (H s1 s2).
      apply H.
      split;[apply Hpre|].
      split.
      apply Bool.orb_false_iff.
      split;[apply Hpre|].
      apply Bool.negb_false_iff.
      apply Hpre.
      apply Bool.orb_false_iff.
      split;[apply Hpre|].
      apply Bool.negb_false_iff.
      apply Hpre.
      unfold ps.
      simpl.
      fold ps.
      unfold w1.
      apply E_IfTrue.
      apply Hpre.
      Search (orb _ (negb _)).
      (*Proof the extended rela rule that can use the rule above *)

      (*Just use the normal termination for the transitivity application, for
 partial correction use axiom forall f, s, exit s', call f s s'
 and proof the rule from the phd*)
