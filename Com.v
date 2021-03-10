From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Coq Require Import Lia.

(** Definition of assertion **)

Definition assertion : Type := sigma -> Prop.

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAss (x : Loc.t) (a : aexp)
| CAssert (b: assertion )
| CSeq (p1 : com) (p2 : com)
| CIf (b : bexp) (p1 p2 : com)
| CWhile (b : bexp) (p : com) (inv : assertion)
| CCall (f: Proc.t).

(** A map from procedure name to the associated commands *)

Module Psi.

  Definition psi : Type := Proc.t -> com.

  Definition empty_psi: psi := fun _ => CSkip.
End Psi.

(** Evaluation command as a relation **)

Inductive ceval : com -> sigma -> Psi.psi -> sigma -> Prop :=
  | E_Skip : forall s ps,
    ceval CSkip s ps s
  | E_Ass : forall s ps x a1 n,
    aeval s a1 = n ->
    ceval (CAss x a1) s ps (x !-> n ; s)
  | E_Assert: forall s ps (b : assertion),
    b s ->
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
  remember (CWhile BTrue CSkip (fun _ : Sigma.sigma => True)) as original_command eqn:Horig.
  induction Heval.
  * inversion Horig.
  * inversion Horig.
  * inversion Horig.
  * inversion Horig.
  * inversion Horig.
  * inversion Horig.
  * inversion Horig;subst. inversion H.
  * inversion Horig;subst.
    apply IHHeval2. reflexivity.
  * inversion Horig.
Qed.

(** Examples of commands **)

Definition plus2 : com := CAss EAX (APlus (AId EAX) (ANum 2)).

Example ecom3 :
forall (s : sigma),
  ceval plus2 s Psi.empty_psi (EAX !-> (s EAX) + 2 ; s).
Proof.
intros.
unfold plus2.
apply E_Ass. simpl. reflexivity.
Qed.

Definition assert2 : com := CAssert (fun s => s EAX = 2).

Example ecom4 :
forall (s : sigma),
  ceval assert2 (EAX !-> 2 ; s) Psi.empty_psi (EAX !-> 2 ; s).
Proof.
intros.
unfold assert2.
apply E_Assert. apply get_sigma_same.
Qed.
