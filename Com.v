From Rela Require Import Loc.
From Rela Require Import Aexp.
Import AexpNotations.
From Rela Require Import Bexp.
Import BexpNotations.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
Import ListNotations.

(** Definition of assertion **)

Definition assertion : Type := list sigma -> Prop.

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAss (x : Loc.t) (a : aexp)
| CAssr (x : Loc.t) (a : aexp)
| CAssert (b: assertion )
| CSeq (p1 : com) (p2 : com)
| CIf (b : bexp) (p1 p2 : com)
| CWhile (b : bexp) (p : com) (inv : assertion)
| CCall (f: Proc.t).

(** Definition of procedure environment :
    a map from procedure name to the associated commands **)

Module Psi.

  Definition psi : Type := Proc.t -> com.

  Definition empty_psi: psi := fun _ => CSkip.
End Psi.

(** Evaluation command as a relation **)

Inductive ceval : com -> sigma -> Psi.psi -> sigma -> Prop :=
  | E_Skip : forall s ps,
      ceval CSkip s ps s
  | E_Ass : forall s ps x a n,
      aeval s a = n ->
      ceval (CAss x a) s ps (x !-> n ; s)
  | E_Assr : forall s ps x a n,
      aeval s a = n ->
      ceval (CAssr x a) s ps ((s x) !-> n ; s)
  | E_Assert: forall s ps (b : assertion),
      ceval (CAssert b) s ps s
  | E_IfTrue : forall s s' ps b p1 p2,
      beval s b = true ->
      ceval p1 s ps s' ->
      ceval (CIf b p1 p2) s ps s'
  | E_IfFalse : forall s s' ps b p1 p2,
      beval s b = false ->
      ceval p2 s ps s' ->
      ceval (CIf b p1 p2) s ps s'
  | E_Seq : forall s s' s'' ps p1 p2,
      ceval p1 s ps s' ->
      ceval p2 s' ps s'' ->
      ceval (CSeq p1 p2) s ps s''
  | E_WhileFalse : forall b s ps p inv,
      beval s b = false ->
      ceval (CWhile b p inv) s  ps s
  | E_WhileTrue : forall b s s' s'' ps p inv,
      beval s b = true ->
      ceval p s ps s' ->
      ceval (CWhile b p inv) s' ps s'' ->
      ceval (CWhile b p inv) s  ps s''
  | E_Call : forall s s' f ps,
      ceval ( ps f) s ps s' ->
      ceval (CCall f) s  ps s'
.

(** Facts about ceval **)

Lemma ceval_inf_loop s ps s' :
ceval (CWhile BTrue CSkip (fun _ => True)) s ps s' -> False.
Proof.
  intros Heval.
  remember (CWhile BTrue CSkip (fun _ : list Sigma.sigma => True)) as original_command eqn:Horig.
  induction Heval;inversion Horig.
  * inversion Horig;subst. inversion H.
  * inversion Horig;subst.
    apply IHHeval2. reflexivity.
Qed.

Lemma ceval_det s ps c:
  forall s1' s2', ceval c s ps s1' -> ceval c s ps s2' -> s1' = s2'.
Proof.
  intros.
  generalize dependent s2'.
  induction H; intros st2 E2; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  apply (IHceval _  H8).
  - rewrite H in H7.
    discriminate H7.
  - rewrite H in H7.
    discriminate H7.
  - apply (IHceval _ H8).
  - specialize (IHceval1 s'0 H3).
    subst.
    apply (IHceval2 _ H7).
  - reflexivity.
  - rewrite H in H3.
    discriminate H3.
  - rewrite H in H8.
    discriminate H8.
  - specialize (IHceval1 s'0 H9).
    subst.
    apply (IHceval2 _ H10).
  - apply (IHceval _ H1).
Qed.

(** Evaluation function for command **)

Fixpoint ceval_step (s : sigma) (c : com) (i : nat) (ps : Psi.psi)
                    : option sigma :=
  match i with
  | 0 => None
  | S i' =>
    match c with
      | CSkip => Some s
      | CAss x a => Some (x !-> aeval s a ; s)
      | CAssr x a => Some ((s x) !-> aeval s a ; s)
      | CAssert b => Some s
      | CSeq c1 c2 =>
          match (ceval_step s c1 i' ps) with
          | Some s' => ceval_step s' c2 i' ps
          | None => None
          end
      | CIf b c1 c2 =>
          if (beval s b)
            then ceval_step s c1 i' ps
            else ceval_step s c2 i' ps
      | CWhile b1 c1 inv =>
          if (beval s b1)
          then match (ceval_step s c1 i' ps) with
               | Some s' => ceval_step s' c i' ps
               | None => None
               end
          else Some s
      | CCall f => ceval_step s (ps f) i' ps
    end
  end.

(** Facts about ceval_step **)

Lemma ceval_step_ceval: forall c s s' ps,
      (exists i, ceval_step s c i ps = Some s') -> ceval c s ps s'.
Proof.
  intros.
  destruct H.
  generalize dependent s.
  generalize dependent s'.
  generalize  dependent c.
  induction x; intros.
  + simpl in H.
    discriminate H.
  + destruct c.
  * inversion H. apply E_Skip.
  * inversion H. apply E_Ass. reflexivity.
  * inversion H. apply E_Assr. reflexivity.
  * inversion H. apply E_Assert.
  *  inversion H.
    destruct (ceval_step s c1 x ps) eqn: H2.
    - eapply E_Seq.
      apply IHx. apply H2.
      apply IHx. apply H1.
    - discriminate H1.
* inversion H.
  destruct (beval s b) eqn: Hb.
    - apply (E_IfTrue _ _ _ _ _ _ Hb).
      apply IHx. apply H1.
    - apply (E_IfFalse _ _ _ _ _ _ Hb).
      apply IHx. apply H1.
* inversion H.
  destruct (beval s b) eqn: Hb.
  - destruct (ceval_step s c x ps) eqn: Hcevalstep.
    ++ apply (E_WhileTrue _ s s0 _ _ _ _ Hb).
       apply IHx. apply Hcevalstep.
       apply IHx. apply H1.
    ++ discriminate H1.
  - inversion H1. rewrite <- H2.
    apply (E_WhileFalse _ _ _ _ _ Hb).
* inversion H. apply E_Call. apply IHx.  apply H1.
Qed.

Lemma ceval_step_more: forall i1 i2 s s' c ps,
  i1 <= i2 ->
  ceval_step s c i1 ps = Some s' ->
  ceval_step s c i2 ps = Some s'.
Proof.
induction i1 as [|i1']; intros i2 s s' c ps Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    +  simpl in Hceval. inversion Hceval.
      reflexivity.
    + simpl in Hceval. inversion Hceval.
      reflexivity.
    + simpl in Hceval. inversion Hceval.
      reflexivity.
    + simpl in Hceval. inversion Hceval.
      reflexivity.
    + simpl in Hceval. simpl.
      destruct (ceval_step s c1 i1') eqn:Hcevalstep.
      * rewrite (IHi1' _ _ _ _ _ Hle' Hcevalstep).
        apply (IHi1' _ _ _ _ _ Hle' Hceval).
      * discriminate Hceval.
    + simpl. simpl in Hceval.
      destruct (beval s b).
      * apply (IHi1' _ _ _ _ _ Hle' Hceval).
      * apply (IHi1' _ _ _ _ _ Hle' Hceval).
    + simpl in Hceval. simpl.
      destruct (beval s b).
      * destruct (ceval_step s c i1') eqn: Hcevalstep.
        -- rewrite (IHi1' _ _ _ _ _ Hle' Hcevalstep).
           apply (IHi1' _ _ _ _ _ Hle' Hceval).
        -- discriminate Hceval.
      * assumption.
    + simpl. simpl in Hceval.
      apply (IHi1' _ _ _ _ _ Hle' Hceval).
Qed.

Lemma ceval_ceval_step: forall c s s' ps,
      ceval c s ps s'  ->
      exists i, ceval_step s c i ps = Some s'.
Proof.
  intros c s s' pc Hce.
  induction Hce.
  * exists 1. reflexivity.
  * exists 1. simpl. rewrite H. reflexivity.
  * exists 1. simpl. rewrite H. reflexivity.
  * exists 1. simpl. reflexivity.
  * destruct IHHce. exists (S x).
    simpl. rewrite H. assumption.
  * destruct IHHce. exists (S x).
    simpl. rewrite H. assumption.
  * destruct IHHce1.  destruct IHHce2.
    exists (S (x + x0)). simpl.
    destruct (ceval_step s p1 (x + x0) ps) eqn: Hceval_step.
  - apply (ceval_step_more x0);[lia |].
    apply (ceval_step_more _ (x + x0)) in H;[|lia].
    rewrite H in Hceval_step.
    inversion Hceval_step.
    rewrite <- H2.
    assumption.
  - apply (ceval_step_more _ (x + x0)) in H;[|lia].
    rewrite H in Hceval_step.
    discriminate Hceval_step.
  * exists 1. simpl. rewrite H. reflexivity.
  * destruct IHHce1.
    destruct IHHce2.
    exists (S (x + x0)). simpl.
    destruct (beval s b).
    + destruct (ceval_step s p (x + x0) ps) eqn : Hcval_step.
      - apply (ceval_step_more x0);[lia|].
        apply (ceval_step_more _ (x + x0)) in H0;[| lia].
        rewrite H0 in Hcval_step.
        inversion Hcval_step. rewrite <- H3.
        assumption.
      - apply (ceval_step_more _ (x + x0)) in H0;[| lia].
        rewrite H0 in Hcval_step.
        discriminate Hcval_step.
   + discriminate H.
  * destruct IHHce.
    exists (S x). simpl.
    assumption.
Qed.

(** Both evaluation are equivalent **)

Theorem ceval_and_ceval_step_coincide: forall c s s' ps,
            ceval c s ps s' <-> exists i, ceval_step s c i ps = Some s'.
Proof.
  intros c s s' ps.
  split. apply ceval_ceval_step. apply ceval_step_ceval.
Qed.

(** Notations for program **)

Declare Scope com_scope.
Open Scope com_scope.
Declare Custom Entry com.

Module ComNotations.
Notation "<[ e ]>" := (e) (e custom com at level 0) : com_scope.
Notation "{ x }" := x (in custom com at level 0, x constr) : com_scope.
Notation "'skip'" := (CSkip) (in custom com at level 1) : com_scope.
Notation "x := y" := (CAss x y)
            (in custom com at level 89,
             x custom aexp,
             y custom aexp,
             no associativity) : com_scope.
Notation "'°' x := y" := (CAssr x y)
            (in custom com at level 89,
             x custom aexp,
             y custom aexp,
             no associativity) : com_scope.
Notation "'assert' b" := (CAssert b)
            (in custom com at level 89,
            b constr at level 0) : com_scope.
Notation "x ; y" := (CSeq x y)
           (in custom com at level 70, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=  (CIf x y z)
           (in custom com at level 89,
           x custom bexp at level 0,
           y custom com at level 0,
           z custom com at level 0) : com_scope.
Notation "'while' x 'inv' i 'do' y 'end'" := (CWhile x y i)
            (in custom com at level 89,
            x custom bexp at level 0,
            y custom com at level 0,
            i constr at level 0) : com_scope.
Notation "'call' f" := (CCall f)
            (in custom com at level 89,
            f constr at level 0) : com_scope.
End ComNotations.
