From Rela Require Import Loc.

(** A memory state (called sigma) maps locations to natural numbers **)

Definition sigma : Type := Loc.t -> nat.

(** Notation for updating  memory states **)

Definition update_sigma (x:Loc.Loc.t) (v: nat) (l:sigma) : sigma :=  
fun (x': Loc.t) => if Loc.Loc.eq_dec x x' then v else l x'. 

Notation "x '!->' v ';' l" := (update_sigma x v l)(at level 100, v at next level, right associativity).

Lemma get_sigma_same : forall x v l, (x !-> v ; l) x = v.
Proof.
intros.
unfold update_sigma.
destruct (Loc.eq_dec x x).
 * reflexivity.
 * contradiction n. reflexivity.
Qed.

Lemma get_lambda_diff : forall x1 x2 v l, x2 <> x1 -> (x1 !-> v ; l) x2 = l x2.
Proof.
intros.
unfold update_sigma.
destruct (Loc.eq_dec x1 x2).
+ contradiction H. rewrite e. reflexivity.
+ reflexivity.
Qed.