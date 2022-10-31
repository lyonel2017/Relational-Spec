Require Import Arith.

(** We choose procedure names to be natural numbers.
    However, the best would be to define Proc as a
    Module Type DecidableType and make all proof modular.
**)

(** Procedure names are Natural **)

Module Proc := Nat.

(** Defining a few Procedire names **)

Parameter f : Proc.t.
Parameter f1 : Proc.t.
Definition f2 : Proc.t:= 2.
Definition f3 : Proc.t:= 3.
Definition f4 : Proc.t:= 4.
Definition op : Proc.t:= 5.
