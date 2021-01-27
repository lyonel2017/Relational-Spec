From Rela Require Import Label.
From Rela Require Import Sigma.

From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Bool.Bool.

(** A map from label to memory states, called lambda **)

Definition lambda : Type := Label.t -> sigma.

(** Notation for updating lambda **)

Definition update_lambda (x:Label.Label.t) (v: sigma) (l:lambda): lambda :=  
fun (x': Label.t) => if Label.eqb x' x then v else l x'. 

Notation "x '|->' v ; l" := (update_lambda x v l)(at level 100, v at next level, right associativity).

Lemma get_lambda_same : forall x v l, (x |-> v ; l) x = v.
Proof.
intros.
unfold update_lambda.
rewrite Nat.eqb_refl.
reflexivity.
Qed.

Lemma get_lambda_diff : forall x1 x2 v l, x2 =? x1 = false -> (x1 |-> v ; l) x2 = l x2.
Proof.
intros.
unfold update_lambda.
rewrite H.
reflexivity.
Qed.