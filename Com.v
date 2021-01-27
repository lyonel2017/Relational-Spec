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
(*| CWhile (b : bexp) (p : prog) (inv : assertion) (ass : (list nat))*)
(* | CCall (f : Proc.t)*)
.

(** A map from procedure name to commands, called Psi*)

Module Psi.

  (** The programs that can be called is a maps from procedure to program **)

  Definition psi : Type := Proc.t -> com.

  (** Notation for a "singleton state" with just one variable bound to a value. *)

  Definition update_psi (x:Proc.t) (v: com ) (l:psi): psi :=
  fun (x': Proc.t) => if Proc.eqb x' x then v else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100, v at next level, right associativity).
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
    
(*  | E_WhileFalse : forall b s ps p inv ass,
      beval s b = false ->
      ceval_c (CWhile b p inv ass) s  ps s
  | E_WhileTrue : forall b s s' s'' ps p inv ass,
      beval s b = true ->
      ceval_p p s ps s' ->
      ceval_c (CWhile b p inv ass) s' ps s'' ->
      ceval_c (CWhile b p inv ass) s  ps s''*)
.

(** Examples of commands **)

Definition plus2 : com := (CAss EAX (APlus (AId EAX) (ANum 2))).

Example ecom3 :
forall (s : sigma),
  ceval plus2 s (fun _ => CSkip) (EAX !-> (s EAX) + 2 ; s).
Proof.
intros.
unfold plus2.
apply E_Ass. simpl. reflexivity.
Qed.