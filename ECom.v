From Rela Require Import Loc.
From Rela Require Import Label.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Proc.
From Rela Require Import Sigma.
From Coq Require Import Lia.

From Coq Require Import Lists.List.
Import ListNotations.

(** Definition of history **)

Definition lambda : Type := list (Label.t * sigma).

(** Definition of assertion **)

Definition assertion : Type := sigma -> lambda -> Prop.

(** Defintion of command and program **)

Inductive com : Type :=
| CSkip (l: Label.t)
| CAss (l: Label.t) (x : Loc.t) (a : aexp)
| CSeq (p1 p2 : com)
(*| CAssert (b: assertion )*)
| CIf (l: Label.t) (b : bexp) (p1 p2 : com)
| CWhile (l: Label.t) (b : bexp) (p : com) (inv : assertion) (ass : (list nat))
(* | CCall (f : Proc.t)*).

(** A map from procedure name to commands, called Psi*)

Module Psi.

  (** The programs that can be called is a maps from procedure to program **)

  Definition psi : Type := Proc.t -> com.

  (** Notation for a "singleton state" with just one variable bound to a value. *)

  Definition update_psi (x:Proc.t) (v: com ) (l:psi): psi :=
  fun (x': Label.t) => if Proc.eqb x' x then v else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100, v at next level, right associativity).
End Psi.

(** Evaluation command as a relation **)

Inductive ceval : com -> sigma -> lambda -> Psi.psi -> 
                  sigma -> lambda -> Prop :=
  | E_Skip : forall s ps la l, 
    ceval (CSkip l) s la ps s ((l,s)::la)
  | E_Ass : forall s la l ps x a1 n,
    aeval s a1 = n ->
    ceval (CAss l x a1) s la ps (x !-> n ; s) ((l,s)::la)
  | E_IfTrue : forall s s' la la' l ps b p1 p2,
      beval s b = true ->
      ceval p1 s ((l,s)::la) ps s' la' ->
      ceval (CIf l b p1 p2) s la ps s' ((l,s)::la)
  | E_IfFalse : forall s s' la la' l ps b p1 p2,
      beval s b = false ->
      ceval p2 s ((l,s)::la) ps s' la' ->
      ceval (CIf l b p1 p2) s la ps s' ((l,s)::la)
  | E_Seq : forall s s' s'' la la' la'' ps p1 p2,
      ceval p1 s la ps s' la'->
      ceval p2 s' la' ps s'' la''->
      ceval (CSeq p1 p2) s la ps s'' la''
  | E_WhileFalse : forall b s la l ps p inv ass,
      beval s b = false ->
      ceval (CWhile l b p inv ass) s la ps s ((l,s)::la)
  | E_WhileTrue : forall b s s' s'' la la' la'' l ps p inv ass,
      beval s b = true ->
      ceval p s ((l,s)::la) ps s' la' ->
      ceval (CWhile l b p inv ass) s' la ps s'' la'' ->
      ceval (CWhile l b p inv ass) s  la ps s'' ((l,s)::la).

(** Examples of commands **)

Definition plus2 : com := CAss l1 EAX (APlus (AId EAX) (ANum 2)).

Example ecom3 :
forall (s : sigma),
  ceval plus2 s [] (fun _ => CSkip l1) (EAX !-> (s EAX) + 2 ; s) ((l1, s)::[]).
Proof.
intros.
unfold plus2.
apply E_Ass. simpl. reflexivity.
Qed.

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

Fixpoint ceval_step (s : sigma) (la: lambda) (ps: Psi.psi) (c : com) (i : nat): option (sigma * lambda) :=
  match i with
  | O  => None
  | S i' =>
    match c with
    | CSkip l => Some (s,((l,s)::la))
    | CAss l x a1 => Some((x !-> (aeval s a1) ; s),((l,s)::la))
   (* | CAssert b  => Some(s,((l,s)::la))*)
    | CSeq p1 p2 =>
        match ceval_step s la ps p1 i' with
        | None => None
        | Some (s',la') => ceval_step s' la' ps p2 i'
        end
    | CIf l b p1 p2 =>
      match (beval s b) with
      | true => 
        match ceval_step s ((l,s)::la) ps p1 i' with
        | None => None 
        | Some (s,_) => Some (s,((l,s)::la))
        end
      | false => 
        match ceval_step s ((l,s)::la) ps p2 i' with
        | None => None 
        | Some (s,_) => Some(s,((l,s)::la))
        end
      end
   | CWhile l b p1 inv ass =>
      match (beval s b) with
      | true =>
        match ceval_step s ((l,s)::la) ps p1 i' with
        | Some (s',_)  => 
          match ceval_step s' la ps c i' with
          | None => None 
          | Some (s,_) => Some (s,((l,s)::la))
          end
        | None => None
        end
      | false => Some(s,((l,s)::la))
      end
    end
  end.

Theorem ceval_step_more: forall i1 i2 p s s' la la' ps ,
  i1 <= i2 ->
  ceval_step_prog s la ps p i1 = Some (s', la') ->
  ceval_step_prog s la ps p i2 = Some (s', la').
Proof.
intros i1 i2 p s s' la la' ps Hle Hceval.
generalize dependent i1.
generalize dependent i2.
generalize dependent s.
generalize dependent s'.
generalize dependent la.
generalize dependent la'.
elim p using prog_com_ind with 
  (P :=  fun c : com =>
 forall l i1 i2 s la s' la',
  i1 <= i2 ->
  ceval_step_com s l la ps c i1 = Some (s', la') ->
  ceval_step_com s l la ps c i2 = Some (s', la')).
  * intros. destruct i1.
    - inversion H0.
    - destruct i2.
      + inversion H.
      + simpl in H0. simpl. rewrite H0. reflexivity.
  * intros. destruct i1.
    - inversion H0.
    - destruct i2.
      + inversion H.
      + simpl in H0. simpl. rewrite H0. reflexivity.
  * intros. destruct i1.
    - inversion H0.
    - destruct i2.
      + inversion H.
      + simpl in H0. simpl. rewrite H0. reflexivity.
  * intros. destruct i1.
    - inversion H2.
    - destruct i2.
      + inversion H1.
      + simpl in H2. simpl. destruct (beval s b).
        ** apply (H la' (l |-> s; la) s' s i2 i1).
          -- lia.
          --  assumption.
        ** apply (H0 la' (l |-> s; la) s' s i2 i1).
          -- lia.
          -- assumption.
  * intros. generalize dependent i2.  generalize dependent s. induction i1.
    - intros. simpl in H1. inversion H1.
    - intros. destruct i2.
      + inversion H0.
      + simpl in H1. simpl. destruct (beval s b).
        ** destruct (ceval_step_prog s (l |-> s; la) ps p0 i1) eqn:Heqr1.
          -- destruct (ceval_step_prog s (l |-> s; la) ps p0 i2) eqn:Heqr2.
            ++ destruct p1. destruct p2.
               apply (H l0 (l |-> s; la) s0 s i2 i1) in Heqr1. 
               rewrite Heqr1 in Heqr2. 
               inversion Heqr2.
               rewrite <- H3.
               apply (IHi1 s0).
               assumption. lia. lia.
            ++ destruct p1.
               apply (H l0 (l |-> s; la) s0 s i2 i1) in Heqr1. 
               rewrite Heqr1 in Heqr2. 
               inversion Heqr2.
               lia.
         -- inversion H1.
       ** assumption.
  * intros. destruct i1.
    - inversion Hceval.
    - destruct i2.
      + inversion Hle.
      + simpl in Hceval. simpl. rewrite Hceval. reflexivity.
  * intros. destruct i1.
    - inversion Hceval.
    - destruct i2.
      + inversion Hle.
      + simpl in Hceval. simpl. 
      destruct (ceval_step_com s t la ps c i1) eqn:Heqr1.
       ** destruct p1. apply (H t i1 i2 s la s0 l) in Heqr1.
          rewrite Heqr1. 
          apply (H0 la' (t |-> s; la) s' s0 i2 i1) in Hceval. 
          rewrite Hceval. reflexivity.
          lia. lia.
        ** inversion Hceval.
Qed.

Theorem ceval_step_more_c: forall c l i1 i2 s la s' la' ps,
  i1 <= i2 ->
  ceval_step_com s l la ps c i1 = Some (s', la') ->
  ceval_step_com s l la ps c i2 = Some (s', la').
 Proof.
 Abort.

(** Function and relational evalution evaluate to the same thing **)

(*Theorem ceval_step__ceval: forall p s s' la ps ,
  well_p p ->
  (exists i, ceval_step_prog s la ps p i = Some s') ->
  ceval_p p s la ps s'.
  Proof.
  Abort.
  intros p s s' la ps Well H.
  inversion H as [i E].
  clear H.
  generalize dependent s'.
  generalize dependent s.
  generalize dependent p.
  generalize dependent la.
  induction i as [| i' ].
  - intros. simpl in E. discriminate E.
  - intros. destruct p.
    + simpl in E. inversion E. apply E_pnil.
    + simpl in E. destruct (ceval_step_com s t la ps c i') eqn:Heqr1.
      * apply E_pconst with s0 .
        -- destruct i'.
          ++ simpl in Heqr1. discriminate Heqr1.
          ++ destruct c. 
            ** simpl in Heqr1. inversion Heqr1. subst. apply E_Skip.
            ** simpl in Heqr1. inversion Heqr1. subst. apply E_Ass. reflexivity.
            ** simpl in Well. destruct Well. contradiction H.
            ** simpl in Heqr1. destruct (beval s b) eqn:Heqr.
              --- apply E_IfTrue.
                +++ assumption.
                +++ apply IHi'. 
                  *** simpl in Well. destruct Well. destruct H. assumption.
                  *** apply (ceval_step_more i' (S i') p1 s s0 (t |-> s; la) ps) in Heqr1.
                    assumption.
                    simpl in Well. destruct Well. destruct H. assumption.
                    lia.
              --- apply E_IfFalse.
                +++ assumption.
                +++ apply IHi'. 
                  *** simpl in Well. destruct Well. destruct H. assumption.
                  *** apply (ceval_step_more i' (S i') p2 s s0 (t |-> s; la) ps) in Heqr1.
                    assumption.
                    simpl in Well. destruct Well. destruct H. assumption.
                    lia.
            ** simpl in Heqr1. destruct (beval s b) eqn:Heqr.
              --- destruct (ceval_step_prog s (t |-> s; la) ps p0 i') eqn:Heqr2.
                +++ apply (E_WhileTrue b s la s1 s0 ps p0 t inv ass).
                  *** assumption.
                  *** apply IHi'.
                  ---- simpl in Well. destruct Well. assumption.
                  ---- apply (ceval_step_more i' (S i') p0 s s1 (t |-> s; la) ps) in Heqr2.
                   assumption.
                   simpl in Well. destruct Well. assumption.
                   lia.
                  *** 
           
            inversion Heqr1. subst.
            ** simpl in Well. destruct Well. contradiction H.
            ** simpl in Well. destruct Well. contradiction H.
        -- apply IHi'. 
          ++ simpl in Well. destruct Well. assumption.
          ++  assumption.
      * discriminate E.
Qed.*)

(*Theorem ceval__ceval_step: forall p s s' la ps ,
  well_p p ->
  ceval_p p s la ps s' ->
  (exists i, ceval_step_prog s la ps p i = Some s').
Proof.
Abort.

Theorem ceval_and_ceval_setp_coincide: forall p s s' la ps ,
  well_p p ->
  (ceval_p p s la ps s' <->
  (exists i, ceval_step_prog s la ps p i = Some s')).
Proof.
Abort.*)
