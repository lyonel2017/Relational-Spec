From Coq Require Import Arith.
From Coq Require Import FMaps.
From Coq Require Import MSets.

(** Procedure names are natural numbers **)

Module Proc := Nat.

(** Defining a few procedure names **)

Definition P1 : Proc.t:= 1.
Definition  P2 : Proc.t := 2.
Definition p3 : Proc.t := 3.
Definition  P4 : Proc.t := 4.

(** Definition of procedure maps **)

Module Proc_Map.

  Module ProcMap := FMapWeakList.Make Proc.
  Module ProcMapFacts := FMapFacts.Facts ProcMap.
  Module ProcMapProps := FMapFacts.Properties ProcMap.

End Proc_Map.

(** Defintion of procedure sets **)

Module Proc_Set.

  Module ProcSet := MSetAVL.Make Proc.
  Module ProcSetFacts := MSetFacts.Facts ProcSet.
  Module ProcSetProps := MSetProperties.Properties ProcSet.

End Proc_Set.