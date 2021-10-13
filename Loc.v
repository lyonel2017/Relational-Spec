From Coq Require Import Arith.
From Coq Require Import FMaps.
From Coq Require Import MSets.

(** Variable (also called locations) are natural numbers **)

Module Loc := Nat.

(** Defining a few Location names **)

Definition EAX : Loc.t:= 1.
Definition EBX : Loc.t:= 2.
Definition ECX : Loc.t:= 3.
Definition EDX : Loc.t:= 4.
Definition EEX : Loc.t:= 5.
Definition EFX : Loc.t:= 6.
Definition EGX : Loc.t:= 7.
Definition EHX : Loc.t:= 8.

Definition X1 : Loc.t:= 1.
Definition X2 : Loc.t:= 2.
Definition X3 : Loc.t:= 3.
Definition X4 : Loc.t:= 3.