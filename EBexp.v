From Rela Require Import Loc.
From Rela Require Import Label.
From Rela Require Import Sigma.
From Rela Require Import Lambda.
From Rela Require Import EAexp.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(* Definition of extended boolean expression *)

Inductive ebexp : Type :=
  | EBTrue
  | EBFalse
  | EBEq (a1 a2 : eaexp)
  | EBLe (a1 a2 : eaexp)
  | EBNot (b : ebexp)
  | EBAnd (b1 b2 : ebexp)
  | EBOr (b1 b2 : ebexp)
  | EBImp (b1 b2 : ebexp).

(* Evalution of extended boolean expression as option prop *)

Fixpoint ebeval_prop (la : lambda) (b : ebexp) : option Prop :=
  match b with
  | EBTrue      => Some True
  | EBFalse     => Some False
  | EBEq a1 a2   => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _=> None
      | _, None => None
      | Some a1, Some a2 => Some (a1 = a2)
    end
  | EBLe a1 a2  => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _ => None
      | _ , None => None
      | Some a1, Some a2 => Some (a1 <= a2)
    end
  | EBNot b1 =>
    match ebeval_prop la b1 with
     | None => None
     | Some b1 => Some ( ~ b1)
    end
  | EBAnd b1 b2 =>
    match (ebeval_prop la b1), (ebeval_prop la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (b1 /\ b2) 
   end
  | EBOr b1 b2  =>
    match (ebeval_prop la b1), (ebeval_prop la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (b1 \/ b2) 
    end
  | EBImp b1 b2  =>
    match (ebeval_prop la b1), (ebeval_prop la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (b1 -> b2) 
    end
  end.
  
(* Evaluation of extended booleand expression as option bool *)

Fixpoint ebeval_bool (la : lambda) (b : ebexp) : option bool :=
  match b with
  | EBTrue      => Some true
  | EBFalse     => Some false
  | EBEq a1 a2 => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _=> None
      | _, None => None
      | Some a1, Some a2 => Some (a1 =? a2)
    end
  | EBLe a1 a2 => 
    match (eaeval la a1), (eaeval la a2) with
      | None, _ => None
      | _ , None => None
      | Some a1, Some a2 => Some (a1 <=? a2)
    end
  | EBNot b1 =>
    match ebeval_bool la b1 with
     | None => None
     | Some b1 => Some ( negb b1)
    end
  | EBAnd b1 b2 =>
    match (ebeval_bool la b1), (ebeval_bool la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (andb b1 b2) 
   end
  | EBOr b1 b2 =>
    match (ebeval_bool la b1), (ebeval_bool la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (orb b1 b2) 
    end
  | EBImp b1 b2 =>
    match (ebeval_bool la b1), (ebeval_bool la b2) with
     | None, _ => None
     | _ , None => None
     | Some b1, Some b2 => Some (orb (negb b1) b2) 
    end 
  end.

(** Helper function for extended boolean expression **)
(* Collector function for locations*)

Fixpoint cveb (b : ebexp) : Loc_Set.LocSet.t :=
  match b with
  | EBTrue       => Loc_Set.LocSet.empty
  | EBFalse      => Loc_Set.LocSet.empty
  | EBEq a1 a2   => Loc_Set.LocSet.union (cvea a1) (cvea a2)
  | EBLe a1 a2  => Loc_Set.LocSet.union (cvea a1) (cvea a2)
  | EBNot b1    => cveb b1
  | EBAnd b1 b2 => Loc_Set.LocSet.union (cveb b1) (cveb b2)
  | EBOr b1 b2  => Loc_Set.LocSet.union (cveb b1) (cveb b2)
  | EBImp b1 b2 => Loc_Set.LocSet.union (cveb b1) (cveb b2)
  end.

(* Collector function for labels*)

Fixpoint cleb (b : ebexp) : Label_Set.LabelSet.t :=
  match b with
  | EBTrue         => Label_Set.LabelSet.empty
  | EBFalse        => Label_Set.LabelSet.empty
  | EBEq a1 a2     => Label_Set.LabelSet.union (clea a1) (clea a2)
  | EBLe a1 a2     => Label_Set.LabelSet.union (clea a1) (clea a2)
  | EBNot b1       => cleb b1
  | EBAnd b1 b2    => Label_Set.LabelSet.union (cleb b1) (cleb b2)
  | EBOr b1 b2     => Label_Set.LabelSet.union (cleb b1) (cleb b2)
  | EBImp b1 b2    => Label_Set.LabelSet.union (cleb b1) (cleb b2)
  end.

(* Example of extended boolean expression *)

Definition example_ebexp : ebexp := EBAnd EBTrue (EBEq (EAt EAX l1) (EANum 5)).

Example bexp1 :
    ebeval_bool (l1 |-> (EAX !-> 5)) example_ebexp = Some true.
Proof. reflexivity. Qed.

Example bexp2 :
    match ebeval_prop (l1 |-> (EAX !-> 5))  example_ebexp with
    | Some p => p
    | None => False
    end.
Proof. 
simpl. split.
 * auto. 
 * reflexivity. 
Qed.