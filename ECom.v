From Rela Require Import Loc.
From Rela Require Import Label.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import EAexp.
From Rela Require Import EBexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Lambda.

(** Defintion of command **)


(** Sigma and Lambda are total function like for the verification condition generator : implies no option type **)


Inductive com : Type :=
| CSkip (l: Label.t)
| CAss (l: Label.t) (x : Loc.t) (a : aexp)
| CSeq (c1 c2 : com)
| CAssert (l: Label.t) (b: ebexp)
| CIf (l: Label.t) (b : bexp) (c1 c2 : com)
| CWhile (l: Label.t) (b : bexp) (c : com)
| CCall (l: Label.t) (p : Proc.t).

Inductive com' : Type :=
| CSkip' (l: Label.t)
| CAss' (l: Label.t) (x : Loc.t) (a : aexp)
| CAssert' (l: Label.t) (b: ebexp)
| CIf' (l: Label.t) (b : bexp) (c1 c2 : prog')
| CWhile' (l: Label.t) (b : bexp) (c : prog') (inv : ebexp) (ass : ( list nat))
| CCall' (l: Label.t) (p : Proc.t)
with prog' : Type := 
| pnil : prog'
| pconst: com' -> prog' -> prog'
.


(** A map from procedure name to commands, called Psi*)

Module Psi.
  Definition psi : Type := Proc_Map.ProcMap.t com.

  Definition empty_psi: psi:= Proc_Map.ProcMap.empty com.

  Definition update_psi (ps:psi) (p:Proc.t) (c: com) : psi := Proc_Map.ProcMap.add p c ps.

  Definition find_psi (p : Proc.t) (ps: psi) := Proc_Map.ProcMap.find p ps.

  (** Notation for a "singleton state" with just one variable bound to a value. *)
  Notation "x '#->' v" := (update_psi empty_psi x v) (at level 100).
End Psi.

(** Evaluation of command as a functional **)

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

End Play.


(* The ceval_f function works on prop and return the set of prop from the assertion that must be verified
  Is it required to check 
*)

Fixpoint ceval_f (s : sigma) (la: lambda) (ps: Psi.psi) (c : com) (i : nat) : (option sigma) * lambda :=
  match i with
  | O  => (None,empty_lambda)
  | S i' =>
    match c with
    | CSkip l => (Some s, update_lambda la l s)
    | CAss l x a1 =>
      match aeval s a1 with
      | None => (None, empty_lambda)
      | Some a =>
        match find_sigma x s with
        | None => (None, empty_lambda)
        | Some _ => (Some (update_sigma s x a) , update_lambda la l s)
        end
      end
    | CAssert l b => 
            match ebeval_bool la b with
              | None  => (None, empty_lambda)
              | Some false => (None, empty_lambda)
              | Some true => (Some s, update_lambda la l s)
             end
  (* require a proof as parameter : function from la to bar prop *)
      (*  let t := 
             match ebeval la a  return bar (ebeval la a ) -> (option sigma) * lambda  with
              | Some p => fun _ => (Some s, update_lambda la l s)
              | None   => fun _ => (None, empty_lambda)
             end
       in t I*)
    | CSeq c1 c2 =>
      match (ceval_f s la ps c1 i') with
      | (Some s',la') => ceval_f s' la' ps c2 i'
      | (None,_)  => (None,empty_lambda)
      end
    | CIf l b c1 c2 =>
      match (beval s b) with
      | None => (None,empty_lambda)
      | Some true =>
        match ceval_f s (update_lambda la l s) ps c1 i' with
        | (Some s' , _)  => (Some s', update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      | Some false =>
        match ceval_f s (update_lambda la l s) ps c2 i' with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      end
    | CWhile l b c =>
      match (beval s b) with
      | None => (None,empty_lambda)
      | Some true =>
        match (ceval_f s (update_lambda la l s) ps (CSeq c (CWhile l b c)) i') with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      | Some false => (Some s, (update_lambda la l s))
      end
    | CCall l p =>
      match (Psi.find_psi p ps) with
      | None => (None,empty_lambda)
      | Some c' =>
        match (ceval_f s (update_lambda la l s) ps c' i') with
        | (Some s' , _)  => (Some s' ,update_lambda la l s)
        | (None, _) => (None,empty_lambda)
        end
      end
    end
  end.

(** Evaluation command as a relation **)

Inductive ceval_r : com -> sigma -> lambda -> Psi.psi -> sigma * lambda -> Prop :=
  | E_Skip : forall s la ps l, 
    ceval_r (CSkip l) s la ps (s,update_lambda la l s)
  | E_Ass : forall s la ps l a new x,
      aeval s a = Some new ->
      Loc_Map.LocMap.mem x s = true ->
      ceval_r (CAss l x a) s la ps (update_sigma s x new, update_lambda la l s)
  | E_Assert: forall s la ps b l,
    match ebeval_prop la b with 
     | Some p => p
     | None => False
     end ->
    ceval_r (CAssert l b) s la ps (s,update_lambda la l s)
  | E_Seq : forall c1 c2 s la s' la' s'' la'' ps,
      ceval_r c1 s la ps (s',la') ->
      ceval_r c2 s' la' ps (s'',la'') -> 
      ceval_r (CSeq c1 c2) s la ps (s'',la'')
  |E_IfTrue : forall s la s' la' ps b c1 c2 l,
      beval s b = Some true ->
      ceval_r c1 s la ps (s', la') ->
      ceval_r (CIf l b c1 c2) s la ps (s',update_lambda la l s)
  |E_IfFalse : forall s la s' la' ps b c1 c2 l,
      beval s b = Some false ->
      ceval_r c2 s la ps (s', la') ->
      ceval_r (CIf l b c1 c2) s la ps (s',update_lambda la l s)
  | E_WhileFalse : forall b s la ps c l,
      beval s b = Some false ->
      ceval_r (CWhile l b c) s la ps (s,(update_lambda la l s))
  | E_WhileTrue : forall b s la s' la' s'' la'' ps c l,
      beval s b = Some true ->
      ceval_r c s la ps (s', la') ->
      ceval_r (CWhile l b c) s' la' ps (s'',la'') ->
      ceval_r (CWhile l b c) s la ps (s'', update_lambda la l s)
  | E_Call : forall s la ps s' la' l p c,
    Psi.find_psi p ps = Some c ->
    ceval_r c s la ps (s',la') ->
    ceval_r (CCall l p) s la ps (s',update_lambda la l s).

(* A proof of Determinisme of evalution as relation*)

(** Helper function for command **)
(* Collector function for locations *)

Fixpoint cvc (c : com)  : Loc_Set.LocSet.t  :=
    match c with
    | CSkip l         => Loc_Set.LocSet.empty
    | CAss l x a      => 
    Loc_Set.LocSet.union (Loc_Set.LocSet.singleton x) (cva a)
    | CAssert l b     => cveb b
    | CSeq c1 c2      => Loc_Set.LocSet.union (cvc c1) (cvc c2)
    | CIf l b c1 c2   =>
      Loc_Set.LocSet.union (cvb b) (Loc_Set.LocSet.union (cvc c1) (cvc c2))
    | CWhile l b c    =>
      Loc_Set.LocSet.union (cvb b) (cvc c)
    | CCall l p       => Loc_Set.LocSet.empty
  end.

(* Collector function for labels *)

Fixpoint clc (c : com)  : Label_Set.LabelSet.t  :=
    match c with
    | CSkip l         => Label_Set.LabelSet.singleton l
    | CAss l x a      => Label_Set.LabelSet.singleton l
    | CAssert l b     => Label_Set.LabelSet.singleton l
    | CSeq c1 c2      => Label_Set.LabelSet.union (clc c1) (clc c2)
    | CIf l b c1 c2   =>
      Label_Set.LabelSet.union (Label_Set.LabelSet.singleton l) 
      (Label_Set.LabelSet.union (clc c1) (clc c2))
    | CWhile l b c    =>
         Label_Set.LabelSet.union 
         (Label_Set.LabelSet.singleton l) 
         (clc c) 
    | CCall l p       => Label_Set.LabelSet.singleton l
  end.

(* Collector function for procedure names *)

Fixpoint cpc (c : com)  : Proc_Set.ProcSet.t  :=
    match c with
    | CSkip l        => Proc_Set.ProcSet.empty
    | CAss l x a     => Proc_Set.ProcSet.empty
    | CAssert l b    => Proc_Set.ProcSet.empty
    | CSeq c1 c2     => Proc_Set.ProcSet.union (cpc c1) (cpc c2)
    | CIf l b c1 c2  =>
      (Proc_Set.ProcSet.union (cpc c1) (cpc c2))
    | CWhile l b c   => cpc c 
    | CCall l p      => Proc_Set.ProcSet.singleton p
  end.

(** Examples of commands **)

Definition plus2 : com := CAss l1 EAX (APlus (AId EAX) (ANum 2)).

Definition assertcom : com := CAssert l1 (EBLe (EAt EAX l1) (EANum 6)).

Example ecom3 :
    ceval_f (EAX !-> 5) (l1 |-> (EAX !-> 5)) Psi.empty_psi assertcom 1 =
    (Some (EAX !-> 5),(l1 |-> (EAX !-> 5))).
Proof.
simpl.
f_equal.
unfold update_lambda.
Abort.
