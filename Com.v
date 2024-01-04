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

(** Definition of variant **)

Definition variant : Type := sigma -> nat .

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAss (x : Loc.t) (a: aexp)
| CAssr (x : Loc.t) (a : aexp)
| CAssert (b: assertion )
| CSeq (p1 : com) (p2 : com)
| CIf (b : bexp) (p1 p2 : com)
| CWhile (b : bexp) (p : com) (inv : assertion) (var : variant)
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
  | E_WhileFalse : forall b s ps p inv var,
      beval s b = false ->
      ceval (CWhile b p inv var) s  ps s
  | E_WhileTrue : forall b s s' s'' ps p inv var,
      beval s b = true ->
      ceval p s ps s' ->
      ceval (CWhile b p inv var) s' ps s'' ->
      ceval (CWhile b p inv var) s  ps s''
  | E_Call : forall s s' f ps,
      ceval ( ps f) s ps s' ->
      ceval (CCall f) s  ps s'
.

(** Facts about ceval **)

Lemma ceval_inf_loop s ps s' inv var :
ceval (CWhile BTrue CSkip inv var) s ps s' -> False.
Proof.
  intros Heval.
  remember (CWhile BTrue CSkip inv var) as original_command eqn:Horig.
  induction Heval;inversion Horig.
  * inversion Horig;subst. inversion H.
  * inversion Horig;subst.
    apply IHHeval2. reflexivity.
Qed.

Lemma ceval_det s ps c:
  forall s1' s2', ceval c s ps s1' -> ceval c s ps s2' -> s1' = s2'.
Proof.
  intros s1' s2' E1 E2.
  generalize dependent s2'.
  induction E1; intros st2' E2 ; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply IHE1; auto.
  - rewrite H in H6.
    discriminate H6.
  - rewrite H in H6.
    discriminate H6.
  - eapply IHE1; auto.
  - specialize (IHE1_1 s'0 H1).
    subst.
    apply (IHE1_2 _ H5).
  - reflexivity.
  - rewrite H in H7.
    discriminate H7.
  - rewrite H in H7.
    discriminate H7.
  - specialize (IHE1_1 s'0 H8).
    subst.
    apply (IHE1_2 _ H9).
  - apply (IHE1 _ H0).
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
