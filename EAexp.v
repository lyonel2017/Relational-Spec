From Rela Require Import Loc.
From Rela Require Import Label.
From Rela Require Import Sigma.
From Rela Require Import Lambda.

(** Definition of extended arithmetic expression **)

Inductive eaexp : Type :=
  | EANum (n : nat)
  | EAt (x : Loc.t) (l : Label.t)
  | EAPlus (a1 a2 : eaexp)
  | EAMinus (a1 a2 : eaexp)
  | EAMult (a1 a2 : eaexp).

(** Evaluation of extended arithmetic expression **)

Fixpoint eaeval (la : lambda) (a : eaexp) : option nat :=
  match a with
  | EANum n => Some n
  | EAt x l => 
     match (find_lambda l la) with
     | None => None
     | Some s => find_sigma x s
     end
  | EAPlus a1 a2 => 
    match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 + a2)
    end
  | EAMinus a1 a2 => 
     match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 - a2)
    end
  | EAMult a1 a2 => 
     match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 * a2)
    end
  end.

(** Helper function for extended arithmetic expression **)
(* Collector function for locations *)

Fixpoint cvea (a : eaexp) : Loc_Set.LocSet.t :=
  match a with
  | EANum n => Loc_Set.LocSet.empty
  | EAt x l => Loc_Set.LocSet.singleton x
  | EAPlus a1 a2 => Loc_Set.LocSet.union (cvea a1) (cvea a2)
  | EAMinus a1 a2 => Loc_Set.LocSet.union (cvea a1) (cvea a2)
  | EAMult a1 a2 => Loc_Set.LocSet.union (cvea a1) (cvea a2)
  end.

(* Collector function for labels *)

Fixpoint clea (a : eaexp) : Label_Set.LabelSet.t :=
  match a with
  | EANum n => Label_Set.LabelSet.empty
  | EAt x l => Label_Set.LabelSet.singleton l
  | EAPlus a1 a2 => Label_Set.LabelSet.union (clea a1) (clea a2)
  | EAMinus a1 a2 => Label_Set.LabelSet.union (clea a1) (clea a2)
  | EAMult a1 a2 => Label_Set.LabelSet.union (clea a1) (clea a2)
  end.

(** Example of extended arithmetic expression **)

Definition example_eaexp : eaexp := EAPlus (EANum 3) (EAMult (EAt EAX l1) (EANum 2)).

Example aexp1 :
    eaeval (l1 |-> (EAX !-> 5)) example_eaexp  = Some 13.
Proof.
reflexivity.
Qed.