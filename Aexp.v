From Rela Require Import Sigma.
From Rela Require Import Loc.

(** Definition of arithmetic expression **)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : Loc.t)
  | AP (x: Loc.t)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Evaluation of arithmetic expression **)

Fixpoint aeval (st : sigma) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st (x)
  | AP x => x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

(** Notations for arithmetic expression **)

Declare Scope aexp_scope.
Open Scope aexp_scope.
Declare Custom Entry aexp.

Module AexpNotations.

Coercion AP : Loc.t >-> aexp.
Coercion ANum : nat >-> aexp.

Notation "[? e ?]" := (e) (e custom aexp at level 0) : aexp_scope.
Notation "x" := x (in custom aexp at level 0, x constr at level 0) : aexp_scope.
Notation "( x )" := x (in custom aexp, 
                       x custom aexp at level 2) : aexp_scope.
Notation "'°' x" := (AId x) (in custom aexp at level 30,
                         x custom aexp ) : aexp_scope.
Notation "x + y" := (APlus x y) (in custom aexp at level 50, 
                                 x custom aexp,
                                 y custom aexp, 
                                 left associativity) : aexp_scope.
Notation "x - y" := (AMinus x y) (in custom aexp at level 50, 
                                  x custom aexp,
                                  y custom aexp, 
                                  left associativity) : aexp_scope.
Notation "x * y" := (AMult x y) (in custom aexp at level 40, 
                                 x custom aexp,
                                 y custom aexp, 
                                 left associativity) : aexp_scope.
End AexpNotations.

Import AexpNotations.

(** Example of arithmetic expression **)

Definition example_aexp : aexp := [? EAX + 2 + (°EAX * 2) ?].

Example aexp1 :
forall st : sigma,
    aeval (EAX !-> 5 ; st) example_aexp = 13.
Proof.
reflexivity.
Qed.