From Rela Require Import Sigma.
From Rela Require Import Loc.

(** Definition of arithmetic expression **)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : Loc.t)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Evaluation of arithmetic expression **)

Fixpoint aeval (st : sigma) (a : aexp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => find_sigma x st  (*Define a notation*)
  | APlus a1 a2 => 
    match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 + a2)
    end
  | AMinus a1 a2 => 
     match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 - a2)
    end
  | AMult a1 a2 => 
     match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 * a2)
    end
  end.

(** Helper function for arithmetic expression**)
(* Collector function for locations *)

Fixpoint cva (a : aexp) : Loc_Set.LocSet.t :=
  match a with
  | ANum n => Loc_Set.LocSet.empty
  | AId x => Loc_Set.LocSet.singleton x
  | APlus a1 a2 =>  Loc_Set.LocSet.union (cva a1) (cva a2)
  | AMinus a1 a2 => Loc_Set.LocSet.union (cva a1) (cva a2)
  | AMult a1 a2 => Loc_Set.LocSet.union (cva a1) (cva a2)
  end.

(** Example of arithmetic expression **)

Definition example_aexp : aexp := APlus (ANum 3) (AMult (AId EAX) (ANum 2)).

Example aexp1 :
    aeval (EAX !-> 5) example_aexp = Some 13.
Proof.
reflexivity.
Qed.



