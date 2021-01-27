From Rela Require Import Loc.

From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(** A memory state (called sigma) maps locations to natural numbers **)

Definition sigma : Type := Loc.t -> nat.

(** Notation for updating  memory states **)

Definition update_sigma (x:Loc.Loc.t) (v: nat) (l:sigma) : sigma :=  
fun (x': Loc.t) => if Loc.eqb x' x then v else l x'. 

Notation "x '!->' v ';' l" := (update_sigma x v l)(at level 100, v at next level, right associativity).

