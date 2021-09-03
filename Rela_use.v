From Rela Require Import Proc.
From Rela Require Import Com.
From Rela Require Import Inliner.
From Rela Require Import Hoare_Triple.
From Rela Require Import Rela.
From Coq Require Import Lists.List.
From Rela Require Import Vcg.

Import ListNotations.

(** Definition of relation Precondition **)

Definition r_precondition : Type := r_assertion.

Definition empty_r_precondition : r_precondition := (fun _ => True).

(** Defintion of relation Postcondtion **)

Definition r_postcondition : Type := r_assertion.

Definition empty_r_postcondition :  r_postcondition := (fun _ => True).

(** Definition of a relational contract **)

Definition r_clause : Type := r_precondition * r_postcondition.

Definition empty_clause : r_clause := (empty_r_precondition, empty_r_postcondition).

Definition get_r_pre (an:r_clause) :=
          let (pre,post) := an in
          pre.

Definition get_r_post (an:r_clause) :=
          let (pre,post) := an in
          post.

Module R_Phi.

  Definition r_phi : Type := list Proc.t -> r_clause.

  Definition empty_r_phi: r_phi := fun _ => empty_clause.

End R_Phi.

(* Defintion of a Relational Properties with inliner*)

Definition i_relational_prop (n: nat) (P Q: r_assertion) (c : list com) (ps : Psi.psi) : Prop :=
  forall s s', length s = length c -> length s' = length c ->
                P s -> rceval c s (k_inliner_ps n ps) s'  -> Q s'.

Lemma n_inline_ps_rceval :
forall (p : list com) (s : list Sigma.sigma) (ps : Proc.t -> com) 
        (s' : list Sigma.sigma) (n : nat),
length s = length p -> length s' = length p ->
rceval p s (k_inliner_ps n ps) s' -> rceval p s ps s'.
Proof.
induction p;intros.
* inversion H.
  apply length_zero_iff_nil in H3.
  inversion H0.
  apply length_zero_iff_nil in H4.
  subst.
  apply E_Empty.
*  destruct s.
   + discriminate H.
   + destruct s'.
   - discriminate H0.
   - inversion H1;subst.
     apply E_Seq.
      ** eapply n_inline_ps_ceval.
         apply H7.
     ** eapply IHp.
        ++ inversion H;reflexivity.
        ++ inversion H0;reflexivity.
        ++ apply H10.
Qed.

Lemma rceval_n_inline_ps_S n p s ps  s':
  length s = length p -> length s' = length p ->
  rceval p s (k_inliner_ps n ps) s' ->
  forall m, n <= m -> rceval p s (k_inliner_ps m ps) s'.
Proof.
generalize dependent s.
generalize dependent s'.
induction p;intros.
* inversion H.
  apply length_zero_iff_nil in H4.
  inversion H0.
  apply length_zero_iff_nil in H5.
  subst.
  apply E_Empty.
* destruct s.
   + discriminate H.
   + destruct s'.
   - discriminate H0.
   - inversion H1;subst.
     apply E_Seq.
     ** eapply ceval_n_inline_ps_S.
        apply H8.
        apply H2.
     ** eapply IHp.
        ++ inversion H;reflexivity.
        ++ inversion H0;reflexivity.
        ++ apply H11.
        ++ apply H2.
Qed.

Lemma rceval_n_inline_ps :
forall (p : list com) (s : list Sigma.sigma) (ps : Psi.psi) (s' : list Sigma.sigma),
length s = length p -> length s' = length p ->
rceval p s ps s' -> exists n : nat, rceval p s (k_inliner_ps n ps) s'.
Proof.
induction p;intros.
* inversion H.
  apply length_zero_iff_nil in H3.
  inversion H0.
  apply length_zero_iff_nil in H4.
  subst.
  exists 0.
  apply E_Empty.
*  destruct s.
   + discriminate H.
   + destruct s'.
   - discriminate H0.
   - inversion H1;subst.
      generalize (ceval_n_inline_ps a s ps s1 H7).
      intros.
      inversion H.
      inversion H0.
      specialize (IHp s0 ps s' H4 H5 H10).
      destruct H2.
      destruct IHp.
      destruct (Proc.max_dec x0 x).
      ** exists x0.
         apply E_Seq;[ | apply H3].
         apply (ceval_n_inline_ps_S x).
         apply H2.
         apply PeanoNat.Nat.max_l_iff.
         apply e.
      ** exists x.
         apply E_Seq;[ apply H2 | ].
         apply (rceval_n_inline_ps_S x0).
         all: try assumption.
         apply PeanoNat.Nat.max_r_iff.
         apply e.
Qed.

Lemma i_relational_prop_relational_prop :
  forall P Q p ps,
  relational_prop P Q p ps <-> forall n, i_relational_prop n P Q p ps.
Proof.
unfold relational_prop, i_relational_prop;split;intros H.
* intros n s s' H1 H2 Pre Heval.
  eapply H.
  apply H1.
  apply H2.
  apply Pre.
  apply n_inline_ps_rceval in Heval.
  all: try assumption.
* intros s s' H1 H2 HPre Heval.
  apply rceval_n_inline_ps in Heval;[ | assumption | assumption].
  destruct Heval.
  eapply H.
  + apply H1.
  + apply H2.
  + apply HPre.
  + apply H0.
Qed.

(* Relational property for a com list with procedure context *)

Definition fold_call := List.map (fun p => CCall p).

Definition relational_prop_ctx (rcl:R_Phi.r_phi) (ps: Psi.psi)
                            (P Q : r_assertion) (c: list com) :=
    (forall p, 0 < length p ->
            relational_prop (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_call p) ps) ->
      relational_prop P Q c ps.

(* Relational property for a procedure list with the procedure context *)

Definition fold_proc (ps: Psi.psi) := List.map (fun p => ps p).

Definition relational_prop_proc_ctx (rcl : R_Phi.r_phi) (ps_init :Psi.psi):=
  forall p ps, 
     relational_prop_ctx rcl ps (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_proc ps_init p).

Lemma rceval_inf_loop p s ps s':
length s = length p -> length s' = length p -> 0 < length p ->
rceval (fold_call p) s (k_inliner_ps 0 ps) s' -> False.
Proof.
intros H1 H2 H Heval.
destruct p.
* inversion H.
* inversion Heval;subst.
  inversion H4;subst.
  apply ceval_inf_loop in H3.
  apply H3.
Qed.

Lemma fold_call_length (f : list Proc.t) : length (fold_call f) = length f.
Proof.
apply map_length.
Qed.

Lemma fold_proc_length (ps: Psi.psi) (f : list Proc.t) : length (fold_proc ps f) = length f.
Proof.
apply map_length.
Qed.

Lemma r_n_inline_ps_inline:
  forall (n : nat) (f : list Proc.t) (s : list Sigma.sigma)
         (ps : Proc.t -> com) (s' : list Sigma.sigma),
  length s = length f -> length s' = length f ->
  rceval (fold_call f) s (k_inliner_ps (S n) ps) s' -> 
  rceval (fold_proc ps f ) s (k_inliner_ps n ps) s'.
Proof.
induction f;intros.
* inversion H.
  apply length_zero_iff_nil in H3.
  inversion H0.
  apply length_zero_iff_nil in H4.
  subst.
  apply E_Empty.
* destruct s.
   + discriminate H.
   + destruct s'.
   - discriminate H0.
   - inversion H1;subst.
     apply E_Seq.
     ** apply n_inline_ps_inline in H7.
        apply H7.
     ** apply IHf.
        ++ inversion H;reflexivity.
        ++ inversion H0;reflexivity.
        ++ apply H10.
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
* intros p Hp s s' H1 H2 HPre Heval.
  destruct p.
  + inversion Hp.
  + apply rceval_inf_loop in Heval.
    - contradiction Heval.
    - rewrite H1.
      rewrite fold_call_length.
      reflexivity.
    - rewrite H2.
      rewrite fold_call_length.
      reflexivity.
    - assumption.
* intros p Hp s s' H1 H2 HPre Heval.
  apply r_n_inline_ps_inline in Heval.
  eapply H.
  + apply IHn.
  + rewrite H1.
    rewrite fold_call_length.
    rewrite fold_proc_length.
    reflexivity.
  + rewrite H2.
    rewrite fold_call_length.
    rewrite fold_proc_length.
    reflexivity.
  + apply HPre.
  + apply Heval.
  + rewrite H1.
    rewrite fold_call_length.
    reflexivity.
  + rewrite H2.
    rewrite fold_call_length.
    reflexivity.
Qed.

(* Verification of Relational properties with procedure *)

Lemma recursion_hoare_triple :
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

Lemma urcorrect :
forall cl rcl ps p,
tc_p ps cl ->
forall (P Q: r_assertion),
(forall ml (hy:length p = length ml),
P ml -> rtc' p ml cl hy) ->
(forall ml (hy:length p = length ml),
P ml -> rtc p ml cl Q hy) ->
relational_prop_ctx rcl ps P Q p.
Proof.
intros.
intros H2.
eapply rcorrect.
 * apply H.
 * apply H0.
 * apply H1.
Qed.


(*Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m, (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m cl (get_post (cl f)).*)

(* Relation contract translation *)

(* TODO :
  We need: 
  
  Parameter is_call : proc -> sigma -> sigma -> Prop
  Axiom connection ceval (call f) s ps s' -> is_call f s s'
  
  Check if a translation implies the initial relationnal properties
  
  Check if we need to distinguished the call: probably no
  *)

(* use simpl termination to get the proc_call to be generated and get 
   generalization : add a vcg specificaly for termination in file vcg
   and the notion of termination and total correcness 
   in the file Hoare triple *)

(* The notion of co-termination can be added in futur work *)

(* The vcg add proc_call after each procedure call *)

(* The rule for using relational properties is a form of cut.
  Maybe in the proof of compleness it can be shown that it is not
  required. But it allow clear/smaller proofs *)
  
Definition proc_call f s s' := forall ps, ceval (CCall f) s ps s'.

Program Fixpoint proc_to_pred p s s' (hy:length cl = length ml): Prop:=
match p, s, s' with
| [] , [], [] => True
| h :: q, s:: qs, s' :: qs' => proc_call p s s' /\ proc_to_pred q qs qs' _
| _, _, _ => !
end.

Definition tr (rcl:R_Phi.r_phi) := 
   forall p s s', proc_to_pred p -> (get_r_pre (rcl p)) s -> (get_r_post (rcl p)) s'.