From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Vcg.
From Rela Require Vcg_Opt.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Rela.
Import Vcg.Why3_Set.
Import Vcg.Assn_b.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Program.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lia.

(** Example of arithmetic expression **)

Import AexpNotations.

Example aexp1 :
forall st : sigma,
    aeval (EAX !-> 1 ; st) [? (EAX + °EAX + &EAX) * 2 ?] = 6.
Proof.
reflexivity.
Qed.

(** Example of boolean expression **)

Import BexpNotations.

Example bexp1 :
forall st : sigma,
    beval (EAX !-> 5 ; st) [! true && ~ EAX <= 4 !] = true.
Proof.
reflexivity.
Qed.

(** Examples of commands **)

Import ComNotations.

Definition plus2 : com := <[ EAX := EAX + 2 ]>.

Example ecom3 :
forall (s : sigma),
  ceval plus2 s Psi.empty_psi (EAX !-> (s EAX) + 2 ; s).
Proof.
intros.
unfold plus2.
apply E_Ass. reflexivity.
Qed.

Example ecom4 :
forall (s : sigma),
  ceval <[ assert (fun s => s EAX = 2) ]> (EAX !-> 2 ; s) Psi.empty_psi (EAX !-> 2 ; s).
Proof.
intros.
apply E_Assert. apply get_sigma_same.
Qed.


(** Examples of proofs of Hoare Triples **)

Example Hoare1 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) plus2 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros. auto.
  + simpl;intros.
    rewrite H0.
    rewrite H.
    simpl.
    apply set'def.
    reflexivity.
Qed.

Definition plus3 : com := <[ EAX := EAX + 2; EAX := EAX + 2 ]>.

Example Haore2 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 5) plus3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros. auto.
  + simpl;intros.
    rewrite H1.
    rewrite H0.
    rewrite H.
    simpl.
    apply set'def.
    reflexivity.
Qed.

Definition if2 : com := <[ if EAX = 4 then { plus2 } else { plus2 } end ]>.

Example Hoare3 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 3) if2 Psi.empty_psi .
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl; intros. auto.
  + simpl;intros.
    destruct (beval m (BEq (AId EAX) (ANum 4))) eqn:Hcond.
    - split;intros.
      ** rewrite H1.
         rewrite H.
         apply set'def.
         reflexivity.
      ** apply bexp_eval_true in Hcond.
         contradiction H0.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H0.
      ** rewrite H1.
         rewrite H.
         apply set'def.
         reflexivity.
Qed.

Definition if3 : com := <[ EAX := EAX + 2 ;
                          if EAX = 4 then { plus2 } else { plus2 } end;
                          { plus2 } ]>.

Example Hoare4 : hoare_triple (fun m => m EAX = 1) (fun m' => m' EAX = 7) if3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* eapply correct.
  + simpl;intros. auto.
  + simpl;intros.
    destruct (beval m' (BEq (AId EAX) (ANum 4))) eqn:Hcond.
    - split;intros.
      ** rewrite H3.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply set'def.
         reflexivity.
      ** apply bexp_eval_true in Hcond.
         contradiction H1.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H1.
      ** rewrite H3.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply set'def.
         reflexivity.
Qed.

Definition assert3 : com := <[ assert (fun m => m EAX = 2) ;
                               assert (fun m => m EAX = 2) ]>.

Example Hoare6 : hoare_triple (fun m => m EAX = 2) (fun _ => True) assert3 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros.
    split.
    - assumption.
    - intros.
      rewrite <- H1.
      assumption.
  + simpl; intros. auto.
Qed.

Definition if4 : com := <[ if EAX = 2 then assert (fun m => m EAX = 2) else skip end ]>.

Example Hoare7 : hoare_triple (fun m => m EAX = 2) (fun m' => m' EAX = 2) if4 Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct.
  + simpl;intros.
    split.
    - intros.
      assumption.
    - auto.
  + simpl;intros.
    destruct (beval m (BEq (AId EAX) (ANum 2))) eqn:Hcond.
    - split;intros.
      ** rewrite <- H2.
         assumption.
      ** apply bexp_eval_true in Hcond.
         contradiction H0.
    - split;intros.
      ** apply bexp_eval_false in Hcond.
         contradiction H0.
      ** rewrite <- H1.
         assumption.
Qed.

(** Some ltac to mechanize the extraction of proof obligation from the list construct **)

Ltac ltc3 hy :=
  inversion hy as [H1];
  symmetry in H1;
  apply length_zero_iff_nil in H1;
  subst.

Ltac ltc2 phi hy :=
         destruct (mk_rtc'_def _ _ phi _ _ hy) as (hyr & HYP);
         rewrite HYP;
         clear HYP hy;
         rename hyr into hy.

Ltac ltc7 phi hy H:= 
  ltc2 phi hy;
  split;[clear hy; inversion H; clear H; apply Vcg_Opt.tc'_same 
        | first [ ltc7 phi hy H| simpl;auto]].

Ltac ltc1 phi hy ml H :=
         destruct ml;
         [ discriminate hy
         | first [ltc3 hy; ltc7 phi hy H| ltc1 phi hy ml H]
         ].

Ltac ltc6 phi hy :=
       destruct (mk_rtc_def _ _ phi _ _ hy) as (hyr & HYP);
       rewrite HYP;
       clear HYP hy;
       rename hyr into hy.

Ltac ltc5 phi hy :=
    intro;
    intros H1;
    tryif ltc6 Phi.empty_phi hy;
          eapply consequence_tc_suite;
          [ clear H1; ltc5 phi hy | apply Vcg_Opt.tc_same; apply H1]
    then auto
    else simpl; apply H1.

Ltac ltc4 ml hy phi:=
         destruct ml;
         [ discriminate hy
         | first [ltc3 hy;
                  ltc6 Phi.empty_phi hy;
                  eapply consequence_tc_suite;[ ltc5 phi hy | apply Vcg_Opt.tc_same]
                 | ltc4 ml hy phi]
          ].

Ltac ltc0 phi := apply rcorrect with phi; 
                 [ 
                 | intros ml hy H;
                   ltc1 phi hy ml H
                 | intros ml hy H;
                   ltc4 ml hy phi;
                   clear hy;
                   inversion H;
                   clear H
                ].

(** Examples of proofs of Relational Properties **)

Definition rela_pre3 (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: m3 :: []) => m1 EAX = m2 EAX /\ m2 EAX = m3 EAX
  | _ => False
  end.

Definition rela_post3 (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: m3 :: []) => m1 EAX = m2 EAX /\ m2 EAX = m3 EAX
  | _ => False
  end.

Example Relation3 : relational_prop rela_pre3 rela_post3 
                    (plus2 :: plus2 :: plus2 :: []) Psi.empty_psi.
Proof.
ltc0 Phi.empty_phi.
(* Verification of proofs obligation for procedure *)
+ apply tc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl.
  intros.
  rewrite H3.
  rewrite H.
  rewrite H2.
  rewrite H0.
  rewrite H1.
  split.
  all: try apply Why3_Set.set'def;reflexivity.
Qed.

Definition X1 : Loc.t:= 1.
Definition X2 : Loc.t:= 2.
Definition ret : Loc.t := 3.

Definition comp: com := <[ if X1 <= X2 && ~ X1 = X2 then
                                 ret := 0
                              else
                                 if X2 <= X1 && ~ X1 = X2  then
                                   ret := 2
                                 else ret := 1
                                 end
                              end ]>.

Definition rela_pre_comp (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 X1 = m2 X2 /\ m1 X2 = m2 X1
  | _ => False
  end.

Definition rela_post_comp (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 ret + (m2 ret) = 2
  | _ => False
  end.

Example Relation_comp : relational_prop
                            rela_pre_comp rela_post_comp
                            (comp :: comp :: []) Psi.empty_psi.
Proof.
ltc0 Phi.empty_phi.
(* Verification of auxiliary proofs proof obligation for procedure*)
+ apply tc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl.
  intros.
  destruct H.
  destruct H0.
  -- destruct H2.
     ** subst. lia.
     ** destruct H2.
        +++ subst.
            rewrite (set''def _ _ _ 0).
            rewrite (set''def _ _ _ 2).
            all: try reflexivity.
        +++ subst. lia.
  -- destruct H2.
     ** destruct H3.
        +++ subst.
            rewrite (set''def _ _ _ 2).
            rewrite (set''def _ _ _ 0).
            all: try reflexivity.
        +++ subst. lia.
     ** destruct H4.
        +++  subst. lia.
        +++ destruct H3.
           *** subst. lia.
           *** subst.
               rewrite (set''def _ _ _ 1).
               rewrite (set''def _ _ _ 1).
               all: try reflexivity.
Qed.
