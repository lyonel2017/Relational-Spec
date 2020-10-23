From Rela Require Import Sigma.
From Rela Require Import Var.
From Rela Require Import Aexp.
From Coq Require Import Bool.Bool.

From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(* Definition of arithmetic expression*)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp).

(* Notations *)

Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y" := (BOr x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(* Evaluation *)

Fixpoint beval (s : sigma) (b : bexp) : option bool :=
  match b with
  | <{true}>      => Some true
  | <{false}>     => Some false
  | <{a1 = a2}>   => 
    match (aeval s a1), (aeval s a2) with
      | None, _=> None
      | _, None => None
      | Some a1, Some a2 => Some (a1 =? a2)
    end
  | <{a1 <= a2}>  => 
    match (aeval s a1), (aeval s a2) with
      | None, _ => None
      | _ , None => None
      | Some a1, Some a2 => Some (a1 <=? a2)
    end
  | <{~ b1}>      =>
    match beval s b1 with
     | None => None
     | Some b1 => Some (negb b1)
    end
  | <{b1 && b2}>  =>
    match (beval s b1), (beval s b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (andb b1 b2) 
   end
  | <{b1 || b2}>  =>
    match (beval s b1), (beval s b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (orb b1 b2) 
    end
  end.

(* Example *)

Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4)}>
  = Some true.
Proof. 
reflexivity.
Qed.
