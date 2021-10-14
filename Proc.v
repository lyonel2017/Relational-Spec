Require Import Arith.

(** We choose procedure names to be natural numbers.
    However, the best would be to define Proc as a
    Module Type DecidableType and make all proof modular.
**)

(** Procedure names are Natural **)

Module Proc := Nat.
