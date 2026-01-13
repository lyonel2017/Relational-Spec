From Rela Require Import Vcg.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Quadruple.
From Rela Require Import Vcg.
From Rela Require Import Vcg_Rela.

From Stdlib Require Import Lists.List.
Import ListNotations.

(** Defintion of the verification condition generator for quadruples,
    using the verification condition generator for relational properties **)

Definition q_suite : Type := Sigma.sigma -> Sigma.sigma -> history ->  history -> Prop.

Definition qtc
  (c1 c2: com)
  (m1 m2: Sigma.sigma)
  (h1 h2: history)
  (cl1 cl2: Phi.phi)
  (suite: q_suite) : Prop :=
  tc c1 m1 h1 cl1 (fun m1' h1' =>
                     tc c2 m2 h2 cl2 (fun m2' h2' => suite m1' m2' h1' h2')).

(** Defintion of the generator of auxiliare goals for relational quadruples **)

Definition qtc'
  (c1 c2: com)
  (m1 m2: Sigma.sigma)
  (h1 h2: history)
  (cl1 cl2: Phi.phi): Prop :=
  tc' c1 m1 h1 cl1 /\ tc' c2 m2 h2 cl2.

(** Defintion of the verification condition generator for quadruple on loop **)

Definition qwtc
  (c1 c2 : com)
  (h1 h2: history)
  (cl: Phi.phi)
  (inv : q_assertion)
  (L R : q_cond) b1 b2: Prop :=
  (forall m1 m2,
      inv m1 m2 -> Assn_b.bassn b1 m1 -> Assn_b.bassn b2 m2 ->
      L m1 m2 = false -> R m1 m2 = false ->
      (qtc' c1 c2 m1 m2 h1 h2 cl cl /\
         qtc c1 c2 m1 m2 h1 h2 cl cl (fun m1' m2' _ _ =>  inv m1' m2')))
  /\
    (forall m1 m2,
        inv m1 m2 -> Assn_b.bassn b1 m1 -> L m1 m2 = true  ->
        (qtc' c1 CSkip m1 m2 h1 h2 cl cl /\
           qtc c1 CSkip m1 m2 h1 h2 cl cl (fun m1' m2' _ _ =>  inv m1' m2')))
  /\
    (forall m1 m2,
        inv m1 m2-> Assn_b.bassn b2 m2 -> R m1 m2 = true ->
        (qtc' CSkip c2 m1 m2 h1 h2 cl cl /\
           qtc CSkip c2 m1 m2 h1 h2 cl cl (fun m1' m2' _ _ =>  inv m1' m2')))
  /\
    (forall m1 m2, inv m1 m2 ->
              beval m1 b1 = beval m2 b2 \/
                (beval m1 b1 = true /\ L m1 m2 = true ) \/
                (beval m2 b2 = true /\ R m1 m2 = true)).

(** Translation of a quadruple on loop into Prop **)

Definition while_call b p inv var ps s s' id :=
  ceval (CWhile b p inv var id) s ps s'.

Definition twq (qwl: QW_Phi.phi) ps1 ps2 :=
  forall c1 c2 b1 b2 inv1 inv2 var1 var2 s1 s1' s2 s2' n1 n2,
    while_call b1 c1 inv1 var1 ps1 s1 s1' n1 ->
    while_call b2 c2 inv2 var2 ps2 s2 s2' n2 ->
    get_wq_inv (qwl c1 b1 n1 c2 b2 n2 ) s1 s2 ->
    get_wq_inv (qwl c1 b1 n1 c2 b2 n2 ) s1' s2' /\
      beval s1' b1 = false /\ beval s2' b2 = false.

Lemma tr_quadruple_while (qwl: QW_Phi.phi) ps1 ps2 :
  (forall inv1 inv2 var1 var2 c1 c2 b1 b2 id1 id2,
      let wq_clause := qwl c1 b1 id1 c2 b2 id2 in
      let q_inv := get_wq_inv wq_clause in
      quadruple q_inv
        (fun m1 m2  _ _ => q_inv m1 m2 /\
                          beval m1 b1 = false /\ beval m2 b2 = false)
        (CWhile b1 c1 inv1 var1 id1)
        (CWhile b2 c2 inv2 var2 id2) ps1 ps2)
  -> twq qwl ps1 ps2.
Proof.
intros H c1 c2 b1 b2 inv1 inv2 var1 var2 s1 s1' s2 s2' id1 id2 hw1 hw2 hinv.
eapply H;eauto.
Qed.

(** Adding while_call to invariant of while **)

Definition mk_while_call b p inv var ps id h :=
  match h with
  | s :: (s' :: _) => while_call b p inv var ps s s' id
  | _ => False
  end.

Fixpoint inv_call c ps : com :=
    match c with
    | CSkip => c
    | CAssi x a => c
    | CAssr x a => c
    | CAssert b => c
    | CSeq p1 p2 => CSeq (inv_call p1 ps) (inv_call p2 ps)
    | CIf b p1 p2 => CIf b (inv_call p1 ps) (inv_call p2 ps)
    | CWhile b p inv var id =>
        CWhile b (inv_call p ps)
          (fun h => inv h /\ mk_while_call b p inv var ps id h)
          var id
    | CCall f => c
    end.

Lemma inv_call_ceval c ps:
forall s s', ceval (inv_call c ps) s ps s' <->  ceval c s ps s'.
Proof.
  induction c; intros.
  all: split; intros; auto.
  1-2: inversion H;subst;
       eapply E_Seq;[ apply IHc1| apply IHc2]; eauto.
  1-2: inversion H;subst;
      [ apply E_IfTrue;[auto|apply IHc1;auto] |
        apply E_IfFalse;[auto|apply IHc2;auto]].
  - remember (CWhile b c inv var id) as original_command eqn:Horig.
    remember (inv_call original_command ps) as original_command2 eqn:Horig2.
    induction H; subst; inversion Horig2;subst.
      + eapply E_WhileFalse; assumption.
      + eapply E_WhileTrue;[assumption | apply IHc;eauto|auto].
  - remember (CWhile b c inv var id) as original_command eqn:Horig.
    remember (inv_call original_command ps) as original_command2 eqn:Horig2.
    induction H; subst; inversion Horig;subst.
      + eapply E_WhileFalse; assumption.
      + eapply E_WhileTrue;[assumption | apply IHc;eauto|auto].
Qed.

Lemma inv_call_hoare :
  forall (inv: assertion) (var: variant) b c ps l id si,
    hoare_triple (fun s => inv (s :: (si :: l)))
      (fun s' _ => inv (s' :: (si :: l)) /\ beval s'  b = false)
      (CWhile b c inv var id) ps ->
    hoare_triple (fun s => inv (s :: (si :: l)))
      (fun s' _ => inv (s' :: (si :: l)) /\ beval s'  b = false)
      (inv_call (CWhile b c inv var id) ps) ps.
Proof.
  intros.
  intros s s' HPre Heval.
  eapply H;[apply HPre | apply inv_call_ceval;auto].
Qed.

(** Definition of a verification condition generator for quadruple on procedures **)

Definition qtr (qcl: Q_Phi.phi) (ps1 ps2: Psi.psi) :=
  forall p1 p2 s1 s2 s1' s2',
    proc_call p1 s1 s1' ps1 /\ proc_call p2 s2 s2' ps2 ->
    (get_q_pre (qcl p1 p2)) s1 s2 -> (get_q_post (qcl p1 p2)) s1' s2' s1 s2.

(** Facts about tr **)

Lemma qtr_relational_prop (qcl:Q_Phi.phi) (ps1 ps2: Psi.psi):
  (forall p1 p2,
      quadruple
        (get_q_pre (qcl p1 p2))
        (get_q_post (qcl p1 p2))
        (CCall p1) (CCall p2) ps1 ps2)
  -> qtr qcl ps1 ps2.
Proof.
  intros H p1 p2 s1 s2 s1' s2' [Hcall1 Hcall2] Hp.
  apply H;auto.
Qed.

(** Definition of a verification condition generator for quadruple on procedures **)

Definition qtc_p (ps1 ps2: Psi.psi) (qcl: Q_Phi.phi): Prop :=
  forall f1 f2 ps1' ps2',
    let c1 := ps1 f1 in
    let c2 := ps2 f2 in
    let cl1 := (phi_call Phi.trial_phi ps1') in
    let cl2 := (phi_call Phi.trial_phi ps2') in
    (forall m1 m2,
        get_q_pre (qcl f1 f2) m1 m2 /\
          qtr qcl ps1' ps2' /\
          get_LR(qcl f1 f2) m1 m2 = true /\
          get_L(qcl f1 f2) m1 m2 = false /\
          get_R(qcl f1 f2) m1 m2 = false ->
        (qtc' c1 c2 m1 m2 empty_history empty_history cl1 cl2 /\
           qtc c1 c2  m1 m2 empty_history empty_history cl1 cl2
             (fun m1' m2' _ _ => (get_q_post (qcl f1 f2)) m1' m2' m1 m2)))
    /\
    (forall m1 m2,
        get_q_pre (qcl f1 f2) m1 m2 /\
          qtr qcl ps1' ps2' /\
          get_L(qcl f1 f2) m1 m2 = true ->
        (qtc' c1 (CCall f2) m1 m2 empty_history empty_history cl1 cl2 /\
           qtc c1 (CCall f2)  m1 m2 empty_history empty_history cl1 cl2
             (fun m1' m2' _ _ => (get_q_post (qcl f1 f2)) m1' m2' m1 m2))) /\
    (forall m1 m2,
        get_q_pre (qcl f1 f2) m1 m2 /\
          qtr qcl ps1' ps2' /\
          get_R(qcl f1 f2) m1 m2 = true ->
        (qtc' (CCall f1) c2 m1 m2 empty_history empty_history cl1 cl2 /\
           qtc (CCall f1) c2 m1 m2 empty_history empty_history cl1 cl2
             (fun m1' m2' _ _ => (get_q_post (qcl f1 f2)) m1' m2' m1 m2)))
      /\
        (forall m1 m2,  get_q_pre (qcl f1 f2) m1 m2 ->
                   ((get_LR(qcl f1 f2) m1 m2 = true /\
                       get_L(qcl f1 f2) m1 m2 = false /\
                       get_R(qcl f1 f2) m1 m2 = false)
                    \/
                      get_L(qcl f1 f2) m1 m2 = true
                    \/
                      get_R(qcl f1 f2) m1 m2 = true)).
