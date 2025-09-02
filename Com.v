From Rela Require Import Loc.
From Rela Require Import Aexp.
Import AexpNotations.
From Rela Require Import Bexp.
Import BexpNotations.
From Rela Require Import Proc.
From Rela Require Import Sigma.

From Coq Require Import Lists.List.

Import ListNotations.

(** Definition of assertion **)

Definition assertion : Type := list sigma -> Prop.

(** Definition of variant **)

Definition variant : Type := sigma -> nat .

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAssi (x : Loc.t) (a: aexp)
| CAssr (x : Loc.t) (a : aexp)
| CAssert (b: assertion )
| CSeq (p1 : com) (p2 : com)
| CIf (b : bexp) (p1 p2 : com)
| CWhile (b : bexp) (p : com) (inv : assertion) (var : variant) (id : nat)
| CCall (f: Proc.t).

(** Definition of procedure environment :
    a map from procedure name to the associated commands **)

Module Psi.

  Definition psi : Type := Proc.t -> com.

  Definition empty_psi: psi := fun _ => CSkip.
End Psi.

(** Notations for program **)

Declare Scope com_scope.
Open Scope com_scope.
Declare Custom Entry com.

Module ComNotations.
Notation "<[ e ]>" := (e) (e custom com at level 0) : com_scope.
Notation "{ x }" := x (in custom com at level 0, x constr) : com_scope.
Notation "'skip'" := (CSkip) (in custom com at level 1) : com_scope.
Notation "x := y" := (CAssi x y)
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
Notation "'while' x 'inv' i 'vari' v 'id' k 'do' y 'end'" := (CWhile x y i v k)
            (in custom com at level 89,
             x custom bexp at level 0,
             y custom com at level 0,
             i constr at level 0,
             v constr at level 0,
             k constr at level 0) : com_scope.
Notation "'call' f" := (CCall f)
            (in custom com at level 89,
            f constr at level 0) : com_scope.
End ComNotations.
