From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Coq Require Import Lia.

(** Definition of assertion **)

Definition assertion : Type := sigma -> Prop.

(** Definition of Precondtion **)

Definition precondition : Type := assertion.

Definition empty_precondition : precondition := (fun _ => True).

(** Defintion of Postcondtion **)

Definition postcondition : Type := assertion.

Definition empty_postcondition :  postcondition := (fun _ => True).

(** Definition of a contract **)

Definition clause : Type := precondition * postcondition.

Definition empty_clause : clause := (empty_precondition, empty_postcondition).

Definition get_pre (an:clause) := 
          let (pre,post) := an in
          pre.

Definition get_post (an:clause) := 
          let (pre,post) := an in
          post.

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAss (x : Loc.t) (a : aexp)
| CAssert (b: assertion )
| CSeq (p1 : com) (p2 : com)
| CIf (b : bexp) (p1 p2 : com)
| CWhile (b : bexp) (p : com) (inv : assertion)
| CCall (f: Proc.t).

(** A map from procedure name to commands and its clause, called Psi*)

Module Psi.

  Definition psi : Type := Proc.t -> com * clause.

  Definition update_psi (x:Proc.t) (v: com ) (c: clause) (l:psi): psi :=
  fun (x': Proc.t) => if Proc.eqb x' x then (v,c) else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100, v at next level, right associativity).

  Definition empty_psi: psi := fun _ => (CSkip,empty_clause).
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
  | E_Com : forall s s' f ps,
      ceval (fst( ps f)) s ps s' ->
      ceval (CCall f) s  ps s'
.

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