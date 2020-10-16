From Rela Require Import Var.
From Rela Require Import Label.
From Rela Require Import Sigma.
From Rela Require Import Lambda.

(* Definition of arithmetic expression*)

Inductive eaexp : Type :=
  | ANum (n : nat)
  | At (x : var) (l : label)
  | APlus (a1 a2 : eaexp)
  | AMinus (a1 a2 : eaexp)
  | AMult (a1 a2 : eaexp).

(* Evaluation *)

Fixpoint eaeval (la : lambda) (a : eaexp) : option nat :=
  match a with
  | ANum n => Some n
  | At x l => 
     match (find_lambda l la) with
     | None => None
     | Some s => find_sigma x s
     end
  | APlus a1 a2 => 
    match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 + a2)
    end
  | AMinus a1 a2 => 
     match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 - a2)
    end
  | AMult a1 a2 => 
     match (eaeval la a1), (eaeval la a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 * a2)
    end
  end.
  
(* Example *)

Definition example_eaexp : eaexp := APlus (ANum 3) (AMult (At X l1) (ANum 2)).

Example aexp1 :
    eaeval (l1 |-> (X !-> 5)) (APlus (ANum 3) (AMult (At X l1) (ANum 2)))
  = Some 13.
Proof.  
reflexivity.
Qed.