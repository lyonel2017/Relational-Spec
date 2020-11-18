From Coq Require Import PeanoNat.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import EAexp.
From Rela Require Import EBexp.
From Rela Require Import ECom.
From Rela Require Import Proc.
From Coq Require Import Lists.List.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(* Why3 goal *)
Definition set: (nat -> nat) -> nat -> nat -> nat -> nat.
Proof.
intros m x y.
intros x'.
destruct (Nat.eq_dec x x') as [H|H].
exact y.
exact (m x').
Defined.

Lemma set'def:
  forall (f: nat -> nat ) (x:nat) (v:nat) (y:nat),
  ((y = x) -> ((set f x v y) = v)) /\ (~ (y = x) -> ((set f x v y) = (f y))).
Proof.
intros f x v y.
split.
+ intros.
 unfold set.
 destruct (Nat.eq_dec x y).
  * reflexivity.
  * contradiction n.
    rewrite H. reflexivity.
+ intros. 
  unfold set.
 destruct (Nat.eq_dec x y).
  * contradiction H.
    rewrite e. reflexivity.
  * reflexivity.
Qed.

Fixpoint ta (a : aexp) ( m : nat -> nat): nat :=
  match a with
  | ANum n => n
  | AId x => m x
  | APlus a1 a2 =>  (ta a1 m) + (ta a2 m)
  | AMinus a1 a2 => (ta a1 m) - (ta a2 m)
  | AMult a1 a2 => (ta a1 m) * (ta a2 m)
  end.

Fixpoint tb (b : bexp) ( m : nat -> nat) : bool :=
  match b with
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2   => (ta a1 m) =? (ta a2 m)
  | BLe a1 a2  => (ta a1 m) <=? (ta a2 m)
  | BNot  b1      => negb (tb b1 m)
  | BAnd b1 b2  => andb (tb b1 m) (tb b2 m)
  | BOr b1 b2  => orb (tb b1 m) (tb b2 m)
  end.

Fixpoint tea (s : nat -> (nat -> nat)) (a : eaexp) : nat :=
  match a with
  | EANum n => n
  | EAt x l => (s l) x
  | EAPlus a1 a2 => (tea s a1 ) + (tea s a2)
  | EAMinus a1 a2 => (tea s a1 ) - (tea s a2)
  | EAMult a1 a2 => (tea s a1 ) * (tea s a2)
  end.

Fixpoint teb (s : nat -> (nat -> nat)) (b : ebexp) : Prop :=
  match b with
  | EBTrue      => True
  | EBFalse     => False
  | EBEq a1 a2   => (tea s a1) = (tea s a2)
  | EBLe a1 a2  => (tea s a1) <= (tea s a2)
  | EBNot b1 => ~ (teb s b1)
  | EBAnd b1 b2 => (teb s b1) /\ (teb s b2)
  | EBOr b1 b2  => (teb s b1) \/ (teb s b2)
  | EBImp b1 b2  => (teb s b1) -> (teb s b2)
  end.

Definition clause : Type := (ebexp*ebexp*( list nat)).

Fixpoint tc (c : prog') (s : nat -> (nat -> nat)) (m: nat -> nat)
            (fin: (nat -> nat) -> (nat -> (nat -> nat)) -> Prop)
            (annot: Proc.t ->  clause): Prop :=
    match c with
    | pnil => fin m s
    | pconst (CSkip' l) p => 
      tc p (fun l' => if Label.Label.eqb l' l then m else s l') m fin annot
    | pconst (CAss' l x a) p =>
      forall m' : nat -> nat , m' = (set m x (ta a m)) ->
      tc p (fun l' => if Label.Label.eqb l' l then m else s l') m' fin annot
    | pconst (CAssert' l b) p =>
      teb (fun l' => if Label.Label.eqb l' l then m else s l') b -> 
      tc p (fun l' => if Label.Label.eqb l' l then m else s l') m fin annot
    | pconst (CIf' l b p1 p2) p =>
      forall m': nat -> nat , 
        ((tb b m = true -> tc p1 (fun l' => if Label.Label.eqb l' l then m else s l') m (fun m _ => m = m') annot)
         /\
        (tb b m = false -> tc p2 (fun l' => if Label.Label.eqb l' l then m else s l') m (fun m _ => m = m') annot))
        -> tc p (fun l' => if Label.Label.eqb l' l then m else s l') m' fin annot
    | pconst (CWhile' l b c inv ass) p => 
          forall m': nat -> nat , 
            teb (fun l' => if Label.Label.eqb l' Label.Here then m else s l') inv ->
            teb (fun l' => if Label.Label.eqb l' Label.Here then m' else s l') inv ->
            tb b m' = false ->
            tc p (fun l' => if Label.Label.eqb l' l then m else s l') m' fin annot
    | pconst (CCall' l proc) p => 
          let (cont,ass) := annot proc in
          let (pre,post) := cont in
          let s' := (fun l' => if Label.Label.eqb l' Label.Pre then m else s l') in 
          forall m': nat -> nat , 
            teb s' pre ->
            teb (fun l' => if Label.Label.eqb l' Label.Post then m' else s' l') post ->
            tc p (fun l' => if Label.Label.eqb l' l then m else s l') m' fin annot
end.

Fixpoint vc_aux (c : prog') (acc : prog') (s : nat -> (nat -> nat)) (m: nat -> nat)
                (annot: Proc.t ->  clause): Prop := 
 match c with
    | pnil => True
    | pconst (CSkip' l) p => 
      vc_aux p (append (CSkip' l) acc) s m annot
    | pconst (CAss' l x a) p =>
      vc_aux p (append (CAss' l x a) acc) s m annot
    | pconst (CAssert' l b) p =>
      tc acc m s (fun _ s => teb s b) annot /\ vc_aux p (append (CAssert' l b) acc) s m annot
    | pconst (CIf' l b p1 p2) p =>
      tc acc m s (fun s m => tb b m = true -> vc_aux p1 pnil s m annot) annot /\
      tc acc m s (fun s m => tb b m = false -> vc_aux p2 pnil s m annot) annot /\
      vc_aux p (append (CIf' l b p1 p2) acc) s m annot
    | pconst (CWhile' l b c inv ass) p => 
      tc acc m s (fun s m => teb (fun l' => if Label.Label.eqb l' Label.Here then m else s l') inv ) annot /\
 
     (* the historic in not required because we have don't use assigns (for the momment) *)
      (forall m : nat -> nat, forall s: nat -> (nat -> nat),
      teb (fun l' => if Label.Label.eqb l' Label.Here then m else s l') inv ->
      tc p m s (fun s m => teb (fun l' => if Label.Label.eqb l' Label.Here then m else s l') inv ) annot
      )
      vc_aux p (append (CWhile' l b c inv ass) acc) s m annot
    | pconst (CCall' l proc) p => 
      vc_aux p (append (CCall' l proc) acc) s m annot
end.

Fixpoint vc_f (ps: Psi.psi) (annot: Proc.t ->  clause) : Prop := False



(*define function for proving assertion and invariant: generate sub program by visiting program*)