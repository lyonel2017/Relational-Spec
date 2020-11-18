From Rela Require Import Loc.

(** A memory state (called sigma) maps variables to natural numbers **)

Definition sigma : Type := Loc_Map.LocMap.t nat.

(** Function for handling memory states **)

Definition empty_sigma: sigma:= Loc_Map.LocMap.empty nat.

Definition update_sigma (s:sigma) (l:Loc.t) (n: nat) : sigma := Loc_Map.LocMap.add l n s.

Definition find_sigma (l : Loc.t) (s: sigma) := Loc_Map.LocMap.find l s.

(** Notation for memory states **)

Notation "x '!->' v" := (update_sigma empty_sigma x v) (at level 100).
