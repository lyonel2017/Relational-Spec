From Rela Require Import Aexp.
From Rela Require Import Bexp.

(** Notations for arithmetic expression **)

Coercion AId : Var.t >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry aexp.
Declare Scope aexp_scope.
Notation "[ e ]" := e (e custom aexp at level 2) : aexp_scope.

Notation "( x )" := x (in custom aexp, x at level 2) : aexp_scope.
Notation "x" := x (in custom aexp at level 0, x constr at level 0) : aexp_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom aexp at level 0, only parsing,
                  f constr at level 0, x constr at level 2,
                  y constr at level 2) : aexp_scope.
Notation "x + y" := (APlus x y) (in custom aexp at level 2, left associativity) : aexp_scope.
Notation "x - y" := (AMinus x y) (in custom aexp at level 2, left associativity) : aexp_scope.
Notation "x * y" := (AMult x y) (in custom aexp at level 1, left associativity) : aexp_scope.

Open Scope aexp_scope.

Check[3 + (X * 2)].

Close Scope aexp_scope.

(** Notations for boolean expression **)

Declare Custom Entry bexp.
Declare Scope bexp_scope.
Notation "<[ e ]>" := e (e custom bexp at level 4): bexp_scope.
Notation "( x )" := x (in custom bexp, x custom bexp at level 4) : bexp_scope.
Notation "'true'" := true (at level 2).
Notation "'true'"  := BTrue (in custom bexp at level 0) : bexp_scope.
Notation "'false'" := false (at level 2).
Notation "'false'"  := BFalse (in custom bexp at level 0) : bexp_scope.
Notation "x" := x (in custom bexp at level 0, x constr at level 0) : bexp_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom bexp at level 1, only parsing,
                  f constr at level 1, x constr at level 4,
                  y constr at level 4) : bexp_scope.
Notation "x <= y" := (BLe x y) (in custom bexp at level 0,
                      x custom aexp at level 2, y custom aexp at level 2, no associativity) : bexp_scope.
Notation "x = y"  := (BEq x y) (in custom bexp at level 0, 
                      x custom aexp at level 2, y custom aexp at level 2, no associativity) : bexp_scope.
Notation "x && y" := (BAnd x y) (in custom bexp at level 4, left associativity) : bexp_scope.
Notation "x || y" := (BOr x y) (in custom bexp at level 4, left associativity) : bexp_scope.
Notation "'~' b"  := (BNot b) (in custom bexp at level 3, right associativity) : bexp_scope.

Open Scope bexp_scope.
Open Scope aexp_scope.

Axiom b1 : bexp.
Axiom b2 : bexp.
Axiom a1 : aexp.
Axiom a2 : aexp.

Check <[ b2 && b2]>.

Check <[ a1 = a2 ]>.
Check <[ (BTrue) ]>.


Check <[ (true) && ~true ]>.

Check <{ true && ~(X <= 4) }>.

Close Scope aexp_scope.
Close Scope bexp_scope.

(** Notations for extended arithmetic expression **)

Coercion EANum : nat >-> eaexp.

Declare Scope eaexp_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : eaexp_scope.
Notation "( x )" := x (in custom com, x at level 99) : eaexp_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : eaexp_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : eaexp_scope.
Notation "x 'at' l" := 
  (EAt x l)(in custom com at level 0,
           l at level 9, no associativity) : eaexp_scope.
Notation "x + y" := (EAPlus x y) (in custom com at level 50, left associativity) : eaexp_scope.
Notation "x - y" := (EAMinus x y) (in custom com at level 50, left associativity) : eaexp_scope.
Notation "x * y" := (EAMult x y) (in custom com at level 40, left associativity) : eaexp_scope.

(** Notations for extended boolean expression **)

Declare Scope ebexp_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : ebexp_scope.
Notation "'true'"  := true (at level 1).
Notation "'true'"  := EBTrue (in custom com at level 0) : ebexp_scope.
Notation "'false'"  := false (at level 1).
Notation "'false'"  := EBFalse (in custom com at level 0) : ebexp_scope.
Notation "x <= y" := (EBLe x y) (in custom com at level 70, no associativity) : ebexp_scope.
Notation "x = y"  := (EBEq x y) (in custom com at level 70, no associativity) : ebexp_scope.
Notation "x && y" := (EBAnd x y) (in custom com at level 80, left associativity) : ebexp_scope.
Notation "x || y" := (EBOr x y) (in custom com at level 80, left associativity) : ebexp_scope.
Notation "'~' b"  := (EBNot b) (in custom com at level 75, right associativity) : ebexp_scope.
Notation "a '=>' b"  := (EBImp a b) (in custom com at level 80, left associativity) : ebexp_scope.

Check <{true && ~(X at l1 <= 4)}>.

(** Notations for extended command **)

Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
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


Definition assertcom : com := 	
 <{ l1 : assert X at l1 <= 6 }>.

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
