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

 Definition get_proc (ps:psi) (f :Proc.t):= 
          let (p,_) := ps f in
          p.

  Definition get_an (ps:psi) (f :Proc.t):= 
          let (_,ann) := ps f in
          ann.

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

Fixpoint ceval_com (s : sigma) (l: Label.t) (la: lambda) (ps: Psi.psi) (c : com) (i : nat): option sigma :=
  match i with
  | O  => None
  | S i' =>
    match c with
    | CSkip => Some (s)
    | CAss x a1 => Some((x !-> (aeval s a1) ; s))
    | CAssert b  => Some(s)
    | CIf b p1 p2 =>
      match (beval s b) with
      | true => ceval_prog s (l |-> s ; la ) ps p1 i'
      | false => ceval_prog s (l |-> s ; la ) ps p2 i' 
      end
   | CWhile b p1 inv ass =>
      match (beval s b) with
      | true =>
        match ceval_prog s (l |-> s ; la ) ps p1 i' with
        | Some (s')  => ceval_com s' l la  ps c i'
        | None => None
        end
      | false => Some(s)
      end
    | CCall f =>
        match ceval_prog s (l |-> s ; la ) ps (Psi.get_proc ps f) i' with
        | Some (s')  => Some( s')
        | None => None
      end
    end
  end
  with ceval_prog (s : sigma) (la: lambda) (ps: Psi.psi) (p : prog) (i : nat): option sigma :=
    match i with
      | O => None 
      | S i' =>
          match p with
          | pnil  => Some (s)
          | pconst l c p' => 
              match ceval_com s l la ps c i' with
                | None => None
                | Some (s') => ceval_prog s' (l |-> s ; la ) ps p' i'
              end
         end
   end.

(** Evaluation command as a relation **)

Inductive ceval_r_c : com -> sigma -> lambda -> Label.t -> Psi.psi -> sigma -> Prop :=
  | E_Skip : forall s la ps l, 
    ceval_r_c CSkip s la l ps s
  | E_Ass : forall s la ps l x a1,
    ceval_r_c (CAss x a1) s la l ps (x !-> (aeval s a1) ; s)
  | E_Assert: forall s la ps b l,
    ebeval_prop la b ->
    ceval_r_c (CAssert b) s la l ps s
  | E_IfTrue : forall s la s' ps b p1 p2 l,
      beval s b = true ->
      ceval_r_p p1 s (l |-> s ; la ) ps s' ->
      ceval_r_c (CIf b p1 p2) s la l ps s'
  | E_IfFalse : forall s la s' ps b p1 p2 l,
      beval s b = false ->
      ceval_r_p p2 s (l |-> s ; la ) ps s' ->
      ceval_r_c (CIf b p1 p2) s la l ps s'
  | E_WhileFalse : forall b s la ps p l inv ass,
      beval s b = false ->
      ceval_r_c (CWhile b p inv ass) s la l ps s
  | E_WhileTrue : forall b s la s' s'' ps c l inv ass,
      beval s b = true ->
      ceval_r_p c s (l |-> s ; la )  ps s' ->
      ceval_r_c (CWhile b c inv ass) s' la l ps s'' ->
      ceval_r_c (CWhile b c inv ass) s  la l ps s''
  | E_Call : forall s la ps s' l f,
    ceval_r_p (Psi.get_proc ps f) s la ps s' ->
    ceval_r_c (CCall f) s la l ps s'
 with ceval_r_p : prog -> sigma -> lambda -> Psi.psi -> sigma -> Prop :=
  | E_pnil : forall s la ps, ceval_r_p pnil s la ps s
  | E_pconst : forall s s' s'' la ps c l p',
      ceval_r_c c s la l ps s' ->
      ceval_r_p p' s' (l |-> s ; la ) ps s'' ->
      ceval_r_p (pconst l c p') s la ps s''.

(** Function and relational evaluaate to the same thing **)

Theorem ceval_ceval_r: forall p s s' la ps ,
  (exists i, ceval_prog s la ps p i = Some s') ->
  ceval_r_p p s la ps s'.
  Proof.
  intros.
  inversion H as [i E].
  clear H.
  generalize dependent s'.
  generalize dependent s.
  generalize dependent p.
  induction i.
  - intros. simpl in E. discriminate E.
  - intros. destruct p.
    + simpl in E. inversion E. apply E_pnil.
    + simpl in E.  destruct c.
     * simpl in E.
  Abort.


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
    ceval_prog (EAX !-> 5 ; s) la (fun _ => (pnil,(EBTrue,EBTrue,nil))) plus2 2 =
    Some ((EAX !-> 7 ; ((EAX !-> 5 ; s)))).
Proof.
intros.
reflexivity.
Qed.
