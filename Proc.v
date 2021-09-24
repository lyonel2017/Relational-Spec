(** Procedure names are Natural**)
Require Import Arith.

(** We choose procedure names to be natural numbers. 
    However, the best would be to define Module Proc
    to be of Type Eq and make all proof modular.
**)

Module Proc := Nat.