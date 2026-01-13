From Rela Require Import Proc.
From Rela Require Import Inliner.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Quadruple.

From Stdlib Require Import Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Import Arith.

(** Definition of relational Precondition **)

Definition r_precondition : Type := list sigma -> Prop.

Definition empty_r_precondition : r_precondition := (fun _ => False).

(** Defintion of relational Postcondition **)

Definition r_postcondition : Type :=  list sigma -> list sigma -> Prop.

Definition empty_r_postcondition :  r_postcondition := (fun _ _ => True).

(** Definition of the relational evaluation of program **)

Inductive rceval : list com -> list sigma ->  Psi.psi -> list sigma -> Prop :=
 | E_Empty : forall ps, rceval [] [] ps []
 | E_Seq : forall c qc s q s' q' ps,
      ceval c s ps s' ->
      rceval qc q ps q' ->
      rceval (c::qc) (s::q) ps (s'::q').

(** Definition of relational properties **)

Definition relational_prop (P: r_precondition) (Q: r_postcondition)
                           (c : list com) (ps : Psi.psi) : Prop :=
 forall s s',  length s = length c -> length s' = length c ->
               P s -> rceval c s ps s' -> Q s' s.

(** A Hoare Triple is a Relational Property for a list of program of size one **)

Module Single_Rela_Prop.

Lemma list_length_one:
forall (A: Type) (h:A) (q : list A), length (h :: q) = 1 -> q = [].
Proof.
  intros.
  simpl in H.
  apply eq_add_S in H.
  apply length_zero_iff_nil in H.
  assumption.
Qed.

Lemma hoare_is_rela :
  forall P Q c ps,
    hoare_triple (fun s => P [s]) (fun s' s => Q [s'] [s]) c ps ->
    relational_prop P Q [c] ps.
Proof.
  unfold hoare_triple.
  unfold relational_prop.
  intros P Q c ps H s s' Hs Hs' HPre He.
  inversion He;subst.
  apply list_length_one in Hs.
  apply list_length_one in Hs'.
  subst.
  apply H;assumption.
Qed.

Lemma one_rela_is_hoare :
  forall (P: precondition) (Q: postcondition) c ps,
    relational_prop (fun s: list sigma => P (hd default_sigma s))
      (fun s' s => Q (hd default_sigma s') (hd default_sigma s)) [c] ps ->
    hoare_triple P Q c ps.
Proof.
  unfold hoare_triple.
  unfold relational_prop.
  intros.
  specialize (H [s] [s']).
  simpl in H.
  apply H.
  reflexivity.
  reflexivity.
  assumption.
  apply E_Seq.
  assumption.
  apply E_Empty.
Qed.

End Single_Rela_Prop.

(** Definition of a relational contract **)

Definition r_clause : Type := r_precondition * r_postcondition.

Definition empty_r_clause : r_clause := (empty_r_precondition, empty_r_postcondition).

Definition get_r_pre (an:r_clause) :=
          let (pre,post) := an in
          pre.

Definition get_r_post (an:r_clause) :=
          let (pre,post) := an in
          post.

(** Definition of relational contract environments :
    a map from list of procedure name to relational clauses **)

Module R_Phi.

  Definition phi : Type := list Proc.t -> r_clause.

  Definition empty_phi: phi :=  fun _ => empty_r_clause.

End R_Phi.

(** Defintion of a relational properties with inliner **)

Definition i_relational_prop (n: nat) (P: r_precondition) (Q: r_postcondition)
                             (c : list com) (ps : Psi.psi) : Prop :=
  forall s s', length s = length c -> length s' = length c ->
          P s -> rceval c s (Inline1.k_inliner_ps n ps) s'  -> Q s' s.

Lemma n_inline_ps_rceval :
  forall (p : list com) (s : list Sigma.sigma) (ps : Psi.psi)
    (s' : list Sigma.sigma) (n : nat),
    length s = length p -> length s' = length p ->
    rceval p s (Inline1.k_inliner_ps n ps) s' -> rceval p s ps s'.
Proof.
  induction p;intros s' ps s n Hs' Hs He.
  - apply length_zero_iff_nil in Hs;subst.
    apply length_zero_iff_nil in Hs';subst.
    apply E_Empty.
  - destruct s ;[discriminate Hs |].
     destruct s';[discriminate Hs' |].
     inversion He;subst.
     apply E_Seq.
     + apply (Inline1.n_inline_ps_ceval _ _ _ _ n).
       assumption.
     + apply (IHp  _ _ _ n).
       * inversion Hs' ; reflexivity.
       * inversion Hs; reflexivity.
       * assumption.
Qed.

Lemma rceval_n_inline_ps_S n p s ps  s':
  length s = length p -> length s' = length p ->
  rceval p s (Inline1.k_inliner_ps n ps) s' ->
  forall m, n <= m -> rceval p s (Inline1.k_inliner_ps m ps) s'.
Proof.
  generalize dependent s.
  generalize dependent s'.
  induction p; intros s' s Hs Hs' He m Hnm.
  - apply length_zero_iff_nil in Hs;subst.
    apply length_zero_iff_nil in Hs';subst.
    apply E_Empty.
  - destruct s;[discriminate Hs|].
    destruct s';[discriminate Hs'|].
    inversion He;subst; simpl.
    apply E_Seq.
    + apply (Inline1.ceval_n_inline_ps_S n); assumption.
    + apply IHp.
       * inversion Hs; reflexivity.
       * inversion Hs'; reflexivity.
       * assumption.
       * assumption.
Qed.

Lemma rceval_n_inline_ps :
  forall (p : list com)
    (s : list Sigma.sigma)
    (ps : Psi.psi)
    (s' : list Sigma.sigma),
    length s = length p -> length s' = length p ->
    rceval p s ps s' -> exists n : nat, rceval p s (Inline1.k_inliner_ps n ps) s'.
Proof.
  induction p; intros s ps s' Hs Hs' He.
  - apply length_zero_iff_nil in Hs;subst.
    apply length_zero_iff_nil in Hs';subst.
    exists 0.
    apply E_Empty.
  - destruct s;[discriminate Hs|].
    destruct s';[discriminate Hs'|].
    inversion He;subst;simpl.
    specialize (Inline1.ceval_n_inline_ps a s ps s1 H4) as [m H].
    inversion He;subst.
    inversion Hs.
    inversion Hs'.
    specialize (IHp s0 ps s' H1 H2 H10) as [n Hr].
    destruct (Nat.max_dec n m).
    + exists n.
       apply E_Seq;[ | apply Hr].
       apply (Inline1.ceval_n_inline_ps_S m).
       assumption.
       apply PeanoNat.Nat.max_l_iff.
       assumption.
    + exists m.
       apply E_Seq;[ apply H | ].
       apply (rceval_n_inline_ps_S n).
       all: try assumption.
       apply PeanoNat.Nat.max_r_iff.
       assumption.
Qed.

Lemma i_relational_prop_relational_prop :
  forall P Q p ps,
  relational_prop P Q p ps <-> forall n, i_relational_prop n P Q p ps.
Proof.
unfold relational_prop, i_relational_prop;split;intros H.
- intros n s s' Hs Hs' Pre Heval.
  apply H.
  all: try assumption.
  apply n_inline_ps_rceval in Heval.
  all: try assumption.
- intros s s' Hs Hs' HPre Heval.
  apply rceval_n_inline_ps in Heval;[ | assumption | assumption].
  destruct Heval as [n Heval].
  apply (H n).
  all: try assumption.
Qed.

(** Relational property for a com list with procedure context **)

Definition fold_call := List.map (fun p => CCall p).

Lemma fold_call_length (f : list Proc.t) : length (fold_call f) = length f.
Proof.
apply map_length.
Qed.

Definition relational_prop_ctx
  (rcl:R_Phi.phi) (ps: Psi.psi)
  (P: r_precondition) (Q : r_postcondition) (c: list com) :=
    (forall p, 0 < length p ->
            relational_prop (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_call p) ps) ->
      relational_prop P Q c ps.

(** Relational property for a procedure list with procedure context **)

Definition fold_proc (ps: Psi.psi) := List.map (fun f => ps f).

Lemma fold_proc_length (ps:  Psi.psi) (f : list Proc.t) :
  length (fold_proc ps f) = length f.
Proof.
apply map_length.
Qed.

Definition relational_prop_proc_ctx (rcl: R_Phi.phi) (ps_init: Psi.psi):=
  forall p ps,
    relational_prop_ctx rcl ps (get_r_pre (rcl p))
      (get_r_post (rcl p)) (fold_proc ps_init p).

Lemma rceval_inf_loop p s ps s':
  0 < length p ->
  rceval (fold_call p) s (Inline1.k_inliner_ps 0 ps) s' -> False.
Proof.
  intros H Heval.
  destruct p.
  * inversion H.
  * inversion Heval;subst.
    inversion H2;subst.
    apply ceval_inf_loop in H1.
    contradiction H1.
Qed.

Lemma r_n_inline_ps_inline:
  forall (n : nat)
    (f : list Proc.t) (s : list Sigma.sigma)
    (ps : Psi.psi) (s' : list Sigma.sigma),
  length s = length f -> length s' = length f ->
  rceval (fold_call f) s (Inline1.k_inliner_ps (S n) ps) s' ->
  rceval (fold_proc ps f ) s (Inline1.k_inliner_ps n ps) s'.
Proof.
induction f; intros s ps s' Hs Hs' He.
- apply length_zero_iff_nil in Hs;subst.
  apply length_zero_iff_nil in Hs';subst.
  apply E_Empty.
- destruct s;[discriminate Hs|].
  destruct s';[discriminate Hs'|].
  inversion He;subst.
  apply E_Seq.
  + apply Inline1.n_inline_ps_inline.
    assumption.
  + apply IHf.
    * inversion Hs; reflexivity.
    * inversion Hs'; reflexivity.
    * assumption.
Qed.

Lemma r_recursive_proc ps rcl:
    relational_prop_proc_ctx rcl ps ->
   (forall p, 0 < length p ->
      relational_prop (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_call p) ps).
Proof.
  intros.
  apply i_relational_prop_relational_prop.
  intros n.
  generalize dependent p.
  induction n.
  - intros p Hp s s' Hs Hs' HPre Heval.
    destruct p.
    + inversion Hp.
    + apply rceval_inf_loop in Heval.
      * contradiction Heval.
      * assumption.
  - intros p Hp s s' Hs Hs' HPre Heval.
    rewrite fold_call_length in Hs.
    rewrite fold_call_length in Hs'.
    apply r_n_inline_ps_inline in Heval;(try assumption).
    apply (H p (Inline1.k_inliner_ps n ps));(try assumption).
    + rewrite fold_proc_length; assumption.
    + rewrite fold_proc_length; assumption.
Qed.

(** Modular Relational properties Verification **)

Lemma recursion_relational :
  forall P Q p ps rcl,
    relational_prop_proc_ctx rcl ps ->
    relational_prop_ctx rcl ps P Q p ->
    relational_prop P Q p ps.
Proof.
  intros.
  apply H0.
  apply r_recursive_proc.
  assumption.
Qed.

(** Extended Modular Relational properties Verification **)

Definition rela_pre qcl rcl (l : list Proc.t) : r_precondition :=
  match l with
  | [l1; l2] =>
      (fun m =>
        match m with
        | [m1;m2] => (get_q_pre (qcl l1 l2)) m1 m2 /\
                     (get_r_pre (rcl l)) m
        | _ => False
        end)
  | _ => empty_r_precondition
  end.

Definition rela_post qcl rcl (l : list Proc.t) : r_postcondition :=
  match l with
  | [l1; l2] =>
      (fun m m' =>
        match m, m' with
        | [m1;m2],[m3;m4] => (get_q_post (qcl l1 l2)) m1 m2 m3 m4 /\
                             (get_r_post (rcl l)) m m'
        | _ ,_ => False
        end)
  | _ => empty_r_postcondition
  end.

Definition rela_clause qcl rcl l: r_clause :=
  (rela_pre qcl rcl l, rela_post qcl rcl l).

Lemma ext_recursion_relational :
  forall P Q p ps rcl qcl,
    quadruple_proc_ctx qcl ps ps ->
    relational_prop_proc_ctx rcl ps ->
    relational_prop_ctx
      (fun l => if List.length l =? 2 then
               rela_clause qcl rcl l
             else rcl l)
      ps P Q p ->
    relational_prop P Q p ps.
Proof.
  intros.
  apply H1.
  intros.
  destruct (length p0) eqn: Hp0.
  - inversion H2.
  - destruct n.
    + apply r_recursive_proc.
      assumption.
      rewrite Hp0.
      auto.
    + destruct n.
      * simpl.
        destruct p0. inversion Hp0.
        destruct p0. inversion Hp0.
        destruct p0;[|inversion Hp0].
        intros s s' Hs Hs' HPre Heval.
        destruct s. inversion Hs.
        destruct s0. inversion Hs.
        destruct s1;[|inversion Hs].
        destruct s'. inversion Hs'.
        destruct s'. inversion Hs'.
        destruct s';[|inversion Hs'].
        simpl. simpl in HPre.
        split.
        -- simpl in Heval.
           inversion Heval;subst.
           inversion H11;subst.
           inversion H13;subst.
           eapply ext_q_recursive_proc.
           apply H. apply HPre.
           auto. auto.
        -- eapply r_recursive_proc.
           eauto.
           rewrite Hp0.
           assumption.
           reflexivity.
           reflexivity.
           apply HPre.
           assumption.
      * apply r_recursive_proc.
        assumption.
        rewrite Hp0.
        auto.
Qed.
