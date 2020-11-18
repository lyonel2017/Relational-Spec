From Rela Require Import Label.
From Rela Require Import Sigma.

(** A map from label to memory states, called lambda**)

Definition lambda : Type := Label_Map.LabelMap.t sigma.

(** Function for handling lambda **)

Definition empty_lambda : lambda := Label_Map.LabelMap.empty sigma.

Definition update_lambda (la: lambda) (l: Label.t) (s: sigma) : lambda := Label_Map.LabelMap.add l s la.

Definition find_lambda (l: Label.t) (la: lambda) := Label_Map.LabelMap.find l la.

(** Notation for lambda **)

Notation "x '|->' v" := (update_lambda empty_lambda x v) (at level 100).
