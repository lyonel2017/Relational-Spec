From Rela Require Import Loc.
From Rela Require Import Label.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import EAexp.
From Rela Require Import EBexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Rela Require Import Lambda.

From Coq Require Export List.

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip
| CAss (x : Loc.t) (a : aexp)
| CAssert (b: ebexp)
| CIf (b : bexp) (p1 p2 : prog)
| CWhile (b : bexp) (p : prog) (inv : ebexp) (ass : (list nat))
| CCall (f : Proc.t)
with prog : Type := 
| pnil : prog
| pconst: Label.t -> com -> prog -> prog
.

Scheme com_prod_ind := Induction for com Sort Prop
with prog_com_ind := Induction for prog Sort Prop.
Combined Scheme com_prog_mutind from com_prod_ind, prog_com_ind.

(** A map from procedure name to commands, called Psi*)

Module Psi.

  (** The clause of the program that can be called **)

  Definition clause : Type := (ebexp * ebexp * (list nat)).

  (** The programs that can be called is a maps from procedure to program **)

  Definition psi : Type := Proc.t -> (prog * clause).

  (** Notation for a "singleton state" with just one variable bound to a value. *)

  Definition update_psi (x:Proc.t) (v: (prog * clause)) (l:psi): psi :=
  fun (x': Label.t) => if Proc.eqb x' x then v else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100).
-
(*  Notation "x '#->' v ; s" := (fun x' => if Proc.eqb x' x then v else s x') (at level 100).*)

  Definition get_pre (an:clause) := 
          let (cont,ass) := an in
          let (pre,post) := cont in
          pre.

  Definition get_post (an:clause) := 
          let (cont,ass) := an in
          let (pre,post) := cont in
          post.

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


(*supprimer acc*)

Fixpoint ceval_com (s : sigma) (l: Label.t) (la: lambda) (ps: Psi.psi) (c : com) (i : nat) (acc : Prop): option (sigma*Prop) :=
  match i with
  | O  => None
  | S i' =>
    match c with
    | CSkip => Some (s, acc)
    | CAss x a1 => Some((x !-> (aeval s a1) ; s), acc)
    | CAssert b  => Some(s,(acc /\ ebeval_prop la b))
    | CIf b p1 p2 =>
      match (beval s b) with
      | true => ceval_prog s (l |-> s ; la ) ps p1 i' acc
      | false => ceval_prog s (l |-> s ; la ) ps p2 i' acc 
      end
   | CWhile b p1 inv ass =>
   let acc := (acc /\ ebeval_prop (Here |-> s ; la ) inv) in
      match (beval s b) with
      | true =>
        match ceval_prog s (l |-> s ; la ) ps p1 i' acc  with
        | Some (s', acc')  => ceval_com s' l la  ps c i' acc'
        | None => None
        end
      | false => Some(s, acc)
      end
    | CCall f =>
    let (p,an) :=  ps f in
        match ceval_prog s (l |-> s ; la ) ps p i' (acc /\ forall la : Lambda.lambda, ebeval_prop (Pre |-> s ; la ) (Psi.get_pre an))  with
        | Some (s' , acc')  => Some( s', (acc' /\ forall la : Lambda.lambda, ebeval_prop (Post |-> s' ; (Pre |-> s ; la )) (Psi.get_post an)))
        | None => None
      end
    end
  end
  
  with ceval_prog (s : sigma) (la: lambda) (ps: Psi.psi) (p : prog) (i : nat) (acc : Prop): option (sigma * Prop) :=
    match i with
      | O => None 
      | S i' =>
          match p with
          | pnil  => Some (s, acc)
          | pconst l c p' => 
              match ceval_com s l la ps c i' acc with
                | None => None
                | Some (s',acc') => ceval_prog s' (l |-> s ; la ) ps p' i' acc'
              end
         end
   end.

(** Evaluation command as a relation **)

(*Inductive ceval_r : com -> sigma -> lambda -> Psi.psi -> sigma * lambda -> Prop :=
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
    ceval_r (CCall l p) s la ps (s',update_lambda la l s).*)







(** Helper function for command **)
(* Collector function for locations *)

Fixpoint cvc (c : com)  : Loc_Set.LocSet.t  :=
    match c with
    | CSkip  => Loc_Set.LocSet.empty
    | CAss x a      =>  Loc_Set.LocSet.union (Loc_Set.LocSet.singleton x) (cva a)
    | CAssert b     => cveb b
    | CIf b c1 c2   => Loc_Set.LocSet.union (cvb b) (Loc_Set.LocSet.union (cvp c1) (cvp c2))
    | CWhile b c _ _    => Loc_Set.LocSet.union (cvb b) (cvp c)
    | CCall p       => Loc_Set.LocSet.empty
    end
with cvp (p : prog) : Loc_Set.LocSet.t :=
  match p with
  | pnil => Loc_Set.LocSet.empty
  | pconst _ c q => Loc_Set.LocSet.union (cvc c) (cvp q) 
  end.

(* Collector function for labels *)

Fixpoint clc (c : com)  : Label_Set.LabelSet.t  :=
    match c with
    | CSkip         => Label_Set.LabelSet.empty
    | CAss x a      => Label_Set.LabelSet.empty
    | CAssert b     => cleb b
    | CIf b p1 p2   => Label_Set.LabelSet.union (clp p1) (clp p2)
    | CWhile b c _ _  =>  clp c 
    | CCall p       => Label_Set.LabelSet.empty
  end
with clp (p : prog) : Label_Set.LabelSet.t :=
  match p with
  | pnil => Label_Set.LabelSet.empty
  | pconst l c q => Label_Set.LabelSet.union
  (Label_Set.LabelSet.union (Label_Set.LabelSet.singleton l) (clc c)) (clp q) 
 end.

(* Collector function for procedure names *)

Fixpoint cpc (c : com)  : Proc_Set.ProcSet.t  :=
    match c with
    | CSkip        => Proc_Set.ProcSet.empty
    | CAss x a     => Proc_Set.ProcSet.empty
    | CAssert b    => Proc_Set.ProcSet.empty
    | CIf b c1 c2  => Proc_Set.ProcSet.union (cpp c1) (cpp c2)
    | CWhile b c _ _   => cpp c 
    | CCall p      => Proc_Set.ProcSet.singleton p
  end
with cpp (p : prog) : Proc_Set.ProcSet.t :=
  match p with
  | pnil => Proc_Set.ProcSet.empty
  | pconst _ c q => Proc_Set.ProcSet.union (cpc c) (cpp q) 
 end.

(** Examples of commands **)

Definition plus2 : prog := pconst l1 (CAss EAX (APlus (AId EAX) (ANum 2))) pnil.

Definition assertcom : prog := pconst l1 (CAssert (EBLe (EAt EAX l1) (EANum 6))) pnil.

Example ecom3 :
forall (s : sigma) (la : lambda),
    ceval_prog (EAX !-> 5 ; s) la (fun _ => (pnil,(EBTrue,EBTrue,nil))) plus2 2 True =
    Some ((EAX !-> 7 ; ((EAX !-> 5 ; s))),True).
Proof.
intros.
reflexivity.
Qed.
