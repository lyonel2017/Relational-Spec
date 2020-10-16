From Rela Require Import Sigma.
From Rela Require Import Var.

(* Definition of arithmetic expression*)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(* Notations *)

Coercion AId : var >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).

Open Scope com_scope.

(* Evaluation *)

Fixpoint aeval (st : sigma) (a : aexp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => find_sigma x st  (*Define a notation*)
  | <{a1 + a2}> => 
    match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 + a2)
    end
  | <{a1 - a2}> => 
     match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 - a2)
    end
  | <{a1 * a2}> => 
     match (aeval st a1), (aeval st a2) with
    | None, _ => None
    | _ , None => None
    | Some a1, Some a2 => Some (a1 * a2)
    end
  end.
  
(* Example *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.

Example aexp1 :
    aeval (X !-> 5) <{ (3 + (X * 2))}>
  = Some 13.
Proof. 
simpl. 
reflexivity.
Qed.

