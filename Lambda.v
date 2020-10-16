From Rela Require Import Label.
From Rela Require Import Sigma.
Require Import FMapAVL.
Require Import FMaps.
From Coq Require Import OrderedTypeEx.

Module Label_Map.

  Module Map := FMapAVL.Make Nat_as_OT.

  Module Facts := Facts Map.

  Include Facts.

End Label_Map.

Definition lambda : Type := Label_Map.Map.t sigma.

Definition empty_lambda : lambda := Label_Map.Map.empty sigma.

Definition update_lambda (la: lambda) (l: label) (s: sigma) : lambda := Label_Map.Map.add l s la.

Definition find_lambda (l: label) (la: lambda) := Label_Map.Map.find l la.

(** Notation for a "singleton state" with just one variable bound to a value. *)
Notation "x '|->' v" := (update_lambda empty_lambda x v) (at level 100).
