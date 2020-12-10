From Coq Require Import PeanoNat.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import EAexp.
From Rela Require Import EBexp.
From Rela Require Import ECom.
From Rela Require Import Proc.
From Rela Require Import Label.
From Rela Require Import Lambda.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(* Why3 goal *)
Definition set: (nat -> nat) -> nat -> nat -> nat -> nat.
Proof.
intros m x y.
intros x'.
Locate Nat.eq_dec .
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

Fixpoint tc (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (ps: Psi.psi): Prop :=
    match c with
    | CSkip => m = m'
    | CAss x a => m' = (set m x (aeval m a))
    | CAssert b => ebeval_prop (l |-> m; s) b /\ m = m'
    | CIf b p1 p2 =>
        beval m b = true -> tp p1 (l |-> m; s) m (fun m _ => m = m') ps /\
        beval m b = false -> tp p2 (l |-> m; s) m (fun m _ => m = m') ps
    | CWhile b c inv ass =>  
            ebeval_prop (Here |-> m; s) inv /\
            ebeval_prop (Here |-> m; s) inv /\
            beval m' b = false
    | CCall proc => 
          let s' := (Pre |-> m; s) in 
          let (_,annot) := ps proc in
          ebeval_prop s' (Psi.get_pre annot) /\
          ebeval_prop (Post |-> m'; s') (Psi.get_post annot)
    end
  with tp (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)
            (fin: Sigma.sigma -> Lambda.lambda -> Prop)
            (ps: Psi.psi): Prop :=
  match p with
  | pnil => fin m s
  | pconst l c p' => 
    forall m' : Sigma.sigma, tc c l s m m' ps -> tp p' (l |-> m; s) m' fin ps
end.


(*Fixpoint vc_aux (c : prog') (acc : prog') (s : nat -> (nat -> nat)) (m: nat -> nat)
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
end.*)

(*Definition vc_f (ps: Psi.psi): Prop :=
forall (f :Proc.t) la m m', 
  (Psi.get_pre (Psi.get_an ps f)) (Pre |-> m ; la ) -> 
  tp (Psi.get_proc f ps) la m (fun m _ => m = m') ps -> 
  (Psi.get_post (Psi.get_an f ps)) (Post |-> m' ; (Pre |-> m ; la )).*)



(*define function for proving assertion and invariant: generate sub program by visiting program*)