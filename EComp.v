From Rela Require Import Var.
From Rela Require Import Label.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import EAexp.
From Rela Require Import EBexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Lambda.
Require Import FMapAVL.
Require Import FMaps.
From Coq Require Import OrderedTypeEx.


Inductive ecom : Type :=
| CSkip (l: label)
| CAss (l: label) (x : var) (a : aexp)
| CSeq (c1 c2 : ecom)
| CAssert (l: label) (b: ebexp)
| CIf (l: label) (b : bexp) (c1 c2 : ecom)
| CWhile (l: label) (b : bexp) (c : ecom)
| CCall (l: label) (p : proc).

(* Notations*)

Notation "l : 'skip'"  :=
  (CSkip l) (in custom com at level 85) : com_scope.
Notation "l : x := y"  :=
  (CAss l x y)
    (in custom com at level 85,
        x at level 0,
        y at level 85, no associativity) : com_scope.
Notation "l : 'assert' x"  :=
  (CAssert l x)
    (in custom com at level 85,
        x at level 99, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "l : 'if' x 'then' y 'else' z 'end'" :=
  (CIf l x y z)
    (in custom com at level 85,
        x at level 99,
        y at level 99, 
        z at level 99) : com_scope.
Notation "l : 'while' x 'do' y 'end'" :=
  (CWhile l x y)
    (in custom com at level 85,
        x at level 99, 
        y at level 99) : com_scope.
Notation "l : 'call' x" :=
  (CCall l x)
    (in custom com at level 85,
        x at level 99) : com_scope.

(*Defintion of map Psi: maping procedure name to commands*)

Module Psi.
  Module Proc_Map.

    Module Map := FMapAVL.Make Nat_as_OT.

    Module Facts := Facts Map.

    Include Facts.

  End Proc_Map.

  Definition psi : Type := Proc_Map.Map.t ecom.

  Definition empty_psi: psi:= Proc_Map.Map.empty ecom.

  Definition update_psi (ps:psi) (p:proc) (c: ecom) : psi := Proc_Map.Map.add p c ps.

  Definition find_psi (p : proc) (ps: psi) := Proc_Map.Map.find p ps.

  (** Notation for a "singleton state" with just one variable bound to a value. *)
  Notation "x '#->' v" := (update_psi empty_psi x v) (at level 100).
End Psi.

(*Evaluation*)

Section Play.

Definition bar sp :=
 match sp with
        | None => True
        | Some prop => prop
 end.

Definition test f := 
          match f return bar f -> nat  with
            | Some p => fun _ => 1
            | None   => fun _ => 0
          end.

Lemma use : 2 = 2.
Proof. reflexivity. Qed.

Example truc: test (Some (2=2)) use = 1.
Proof. reflexivity. Qed.


Definition test2 s la l a := 
       let f := ebeval la a in
       let t :=
          match f return bar f -> (option sigma) * lambda  with
            | Some p => fun _ => (Some s, update_lambda la l s)
            | None   => fun _ => (None, empty_lambda)
          end
        in
        t.
        
End Play.

Fixpoint ceval (s : sigma) (la: lambda) (ps: Psi.psi) (c : ecom) (i : nat): (option sigma) * lambda :=
  match i with
  | O  => (None,empty_lambda)
  | S i' =>
    match c with
    | <{ l : skip }> => (Some s, update_lambda la l s)
    | <{ l : x := a1 }> =>
      match aeval s a1 with
      | None => (None, empty_lambda)
      | Some a =>
        match find_sigma x s with
        | None => (None, empty_lambda)
        | Some _ => (Some (update_sigma s x a) , update_lambda la l s)
        end
      end
    | <{ l : assert a }> => (None, empty_lambda)
    | <{ c1 ; c2 }> =>
      match (ceval s la ps c1 i') with
      | (Some s',la') => ceval s' la' ps c2 i'
      | (None,_)  => (None,empty_lambda)
      end
    | <{l: if b then c1 else c2 end }> =>
      match (beval s b) with
      | None => (None,empty_lambda)
      | Some true =>
        match ceval s (update_lambda la l s) ps c1 i' with
        | (Some s' , _)  => (Some s', update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      | Some false =>
        match ceval s (update_lambda la l s) ps c2 i' with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      end
    | <{l:  while b1 do c1 end }> =>
      match (beval s b1) with
      | None => (None,empty_lambda)
      | Some true =>
        match (ceval s (update_lambda la l s) ps <{c1; l:  while b1 do c1 end }> i') with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      | Some false => (Some s, (update_lambda la l s))
      end
    | <{ l : call p }> =>
      match (Psi.find_psi p ps) with
      | None => (None,empty_lambda)
      | Some c' =>
        match (ceval s (update_lambda la l s) ps c' i') with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      end
    end
  end.

(*Examples*)

Definition plus2 : ecom :=
  <{ l1 : X := X + 2 }>.

Definition assertcom : ecom :=
  <{ l1 : assert BEq (At X l1) (ANum 3)}>.

Definition subtract_slowly_body : ecom :=
  <{ l1: Z := Z - 1 ;
     l2: X := X - 1 }>.

Definition if_nothing : ecom :=
  <{ l1: if true then
           l2: skip
         else
           l3: skip
     end}>.

Definition subtract_slowly : ecom :=
  <{ l1: while true do
                 subtract_slowly_body
                 end }>.

Definition fact_in_coq : ecom :=
  <{ 1: Z := X;
     2: Y := 1;
     3: while ~(Z = 0) do
              4: Y := Y * Z;
     5: Z := Z - 1
     end }>.

Print fact_in_coq.

Example ecom3 :
    ceval (X !-> 5) (l1 |-> (X !-> 5)) Psi.empty_psi <{assertcom }> 10 =
    (Some (X !-> 5),(l1 |-> (X !-> 5))).
Proof.
Abort.

Example ecom1 :
    ceval (X !-> 5) empty_lambda Psi.empty_psi <{plus2 }> 10 =
    (Some (X !-> 7),(l1 |-> (X !-> 5))).
Proof.
Abort.

