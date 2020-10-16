From Rela Require Import Var.
Require Import FMapAVL.
Require Import FMaps.
From Coq Require Import OrderedTypeEx.

Module Var_Map.

  Module Map := FMapAVL.Make Nat_as_OT.

  Module Facts := Facts Map.

  Include Facts.

End Var_Map.

Definition sigma : Type := Var_Map.Map.t nat.

Definition empty_sigma: sigma:= Var_Map.Map.empty nat.

Definition update_sigma (s:sigma) (v:var) (n: nat) : sigma := Var_Map.Map.add v n s.

Definition find_sigma (v : var) (s: sigma) := Var_Map.Map.find v s.

(** Notation for a "singleton state" with just one variable bound to a value. *)
Notation "x '!->' v" := (update_sigma empty_sigma x v) (at level 100).
