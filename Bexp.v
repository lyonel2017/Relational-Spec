From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.

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

Fixpoint beval (s : sigma) (b : bexp) : option bool :=
  match b with
  | BTrue      => Some true
  | BFalse     => Some false
  | BEq a1 a2   => 
    match (aeval s a1), (aeval s a2) with
      | None, _=> None
      | _, None => None
      | Some a1, Some a2 => Some (a1 =? a2)
    end
  | BLe a1 a2  => 
    match (aeval s a1), (aeval s a2) with
      | None, _ => None
      | _ , None => None
      | Some a1, Some a2 => Some (a1 <=? a2)
    end
  | BNot b1      =>
    match beval s b1 with
     | None => None
     | Some b1 => Some (negb b1)
    end
  | BAnd b1 b2  =>
    match (beval s b1), (beval s b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (andb b1 b2) 
   end
  | BOr b1 b2  =>
    match (beval s b1), (beval s b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (orb b1 b2) 
    end
  end.

(** Helper function for boolean expression **)
(* Collector function for locations *)

Fixpoint cvb (b : bexp) : Loc_Set.LocSet.t :=
  match b with
  | BTrue      => Loc_Set.LocSet.empty
  | BFalse     => Loc_Set.LocSet.empty
  | BEq a1 a2   => Loc_Set.LocSet.union (cva a1) (cva a2)  
  | BLe a1 a2  => Loc_Set.LocSet.union (cva a1) (cva a2)
  | BNot  b1      => cvb b1
  | BAnd b1 b2  => Loc_Set.LocSet.union (cvb b1) (cvb b2)
  | BOr b1 b2  => Loc_Set.LocSet.union (cvb b1) (cvb b2)
  end.

(** Example of boolean expression **)

Definition example_bexp : bexp := BAnd BTrue (BNot (BLe (AId EAX) (ANum 4))).

Example bexp1 :
    beval (EAX !-> 5) example_bexp = Some true.
Proof. 
reflexivity.
Qed.


