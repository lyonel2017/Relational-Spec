From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.
Import AexpNotations.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(** Definition of boolean expression **)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp).
	
(** Evaluation of boolean expression **)

Fixpoint beval (s : sigma) (b : bexp) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2  => (aeval s a1) =? (aeval s a2)
  | BLe a1 a2  => (aeval s a1) <=? (aeval s a2)
  | BNot b1    => negb (beval s b1)
  | BAnd b1 b2 => andb (beval s b1)(beval s b2)
  | BOr b1 b2  => orb (beval s b1) (beval s b2)
  end.

(** Notations for boolean expression **)

Declare Scope bexp_scope.
Open Scope bexp_scope.
Declare Custom Entry bexp.

Module BexpNotations.

Notation "[! e !]" := (e) (e custom bexp at level 0) : bexp_scope.
Notation "{ x }" := x (in custom bexp at level 0, x constr) : bexp_scope.
Notation "( x )" := x (in custom bexp, 
                       x custom bexp at level 2) : bexp_scope.
Notation "'true'" := true (at level 5).
Notation "'true'" := (BTrue) (in custom bexp at level 4) : bexp_scope.
Notation "'false'" := false (at level 5).
Notation "'false'" := (BFalse) (in custom bexp at level 4) : bexp_scope.
Notation "x '&&' y" := (BAnd x y) (in custom bexp at level 65, 
                                  x custom bexp, 
                                  y custom bexp,
                                  left associativity) : bexp_scope.
Notation "x '||' y" := (BOr x y) (in custom bexp at level 65,
                                x custom bexp, 
                                y custom bexp,
                                left associativity) : bexp_scope.
Notation "'~' b"  := (BNot b) (in custom bexp at level 80, 
                               b custom bexp, 
                               right associativity) : bexp_scope.
Notation "x '<=' y" := (BLe x y) (in custom bexp at level 70,
                      x custom aexp, 
                      y custom aexp,
                      no associativity) : bexp_scope.
Notation "x = y"  := (BEq x y) (in custom bexp at level 70, 
                      x custom aexp,
                      y custom aexp, 
                      no associativity) : bexp_scope.
End BexpNotations.

Import BexpNotations.

(** Example of boolean expression **)

Definition example_bexp : bexp := [! true && ~ °EAX <= 4 !].

Print Visibility.

Example bexp1 :
forall st : sigma,
    beval (EAX !-> 5 ; st) example_bexp = true.
Proof. 
reflexivity.
Qed.