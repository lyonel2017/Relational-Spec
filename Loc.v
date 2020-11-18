From Coq Require Import Arith.
From Coq Require Import FMaps.
From Coq Require Import MSets.

(* Rename into location *)


(** Variable (also called locations) are natural numbers **)

Module Loc := Nat.

(** Defining a few Location names **)

Definition EAX : Loc.t:= 1.
Definition EBX : Loc.t:= 2.
Definition ECX : Loc.t:= 3.
Definition EDX : Loc.t:= 4.

(** Definition of Locations maps **)

Module Loc_Map.

  Module LocMap := FMapWeakList.Make Loc.
  Module LocMapFacts := FMapFacts.Facts LocMap.
  Module LocMapProps := FMapFacts.Properties LocMap.

End Loc_Map.

(** Defintion of variable sets **)

Module Loc_Set.

  Module LocSet := MSetAVL.Make Loc.
  Module LocSetFacts := MSetFacts.Facts LocSet.
  Module LocSetProps := MSetProperties.Properties LocSet.

End Loc_Set.