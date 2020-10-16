From Rela Require Import Var.
From Rela Require Import Label.
From Rela Require Import Sigma.
From Rela Require Import Lambda.
From Rela Require Import EAexp.

(* Definition of arithmetic expression*)

Inductive ebexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : eaexp)
  | BLe (a1 a2 : eaexp)
  | BNot (b : ebexp)
  | BAnd (b1 b2 : ebexp)
  | BOr (b1 b2 : ebexp).

(* Evaluation *)

Fixpoint ebeval (la : lambda) (b : ebexp) : option Prop :=
  match b with
  | BTrue      => Some True
  | BFalse     => Some False
  | BEq a1 a2   => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _=> None
      | _, None => None
      | Some a1, Some a2 => Some (a1 = a2)
    end
  | BLe a1 a2  => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _ => None
      | _ , None => None
      | Some a1, Some a2 => Some (a1 <= a2)
    end
  | BNot b1 =>
    match ebeval la b1 with
     | None => None
     | Some b1 => Some (~b1)
    end
  | BAnd b1 b2  =>
    match (ebeval la b1), (ebeval la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (b1 /\ b2) 
   end
  | BOr b1 b2  =>
    match (ebeval la b1), (ebeval la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (b1 \/ b2) 
    end
  end.

(* Example *)

Definition example_bexp : ebexp := BAnd BTrue (BNot (BLe (At X l1) (ANum 4))).

From Coq Require Import Omega.

Example bexp1 :
    match ebeval (l1 |-> (X !-> 5))  (BAnd BTrue (BLe (ANum 4) (At X l1))) with
    | None => False
    | Some p => p
    end.
Proof.
simpl.
split.
* auto.
* omega.
Qed.