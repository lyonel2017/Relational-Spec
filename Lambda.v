From Rela Require Import Label.
From Rela Require Import Sigma.

From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(** A map from label to memory states, called lambda **)

Definition lambda : Type := Label.t -> sigma.

(** Notation for updating lambda **)

Definition update_lambda (x:Label.Label.t) (v: sigma) (l:lambda): lambda :=  
fun (x': Label.t) => if Label.eqb x' x then v else l x'. 

Notation "x '|->' v ; l" := (update_lambda x v l)(at level 100).

(*Notation "x '|->' v ; l" := (fun (x': Label.t) => if Label.eqb x' x then v else l x') (at level 100).*)
