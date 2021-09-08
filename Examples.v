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

(** Examples of proofs of Hoare Triples **)

(* Factorial examples *)

(*
  EEX the result
  EAX the current index
  EBX the size of the first array
  ECX the size of the second array
  EDX the address of the first array
  EFX the address of the second array
  EGX helper register
  EHX helper register
*)

Definition a1: assertion := fun s => 0 <= s(EAX) /\ s(EAX) <= s(EBX) /\
                                                    s(EAX) <= s(ECX).

Definition a2: assertion := fun s => 
   (s(EEX) = 1 /\ (forall k, 0 <= k /\ k < s(EAX)-> s(s(EDX) + k) = s(s(EFX) + k))) \/
   (s(EEX) = 0 /\ (s(EAX) > 0 -> s(s(EDX) + (s(EAX) - 1)) < s(s(EAX) + (s(EFX)-1)))) \/
   (s(EEX) = 2 /\ (s(EAX) > 0 -> s(s(EDX) + (s(EAX) - 1)) > s(s(EAX) + (s(EFX)-1)))).

Definition b := 
[!EAX <= EBX && EAX <= ECX && EEX = 1 && (~ EAX = EBX) && (~ EAX = ECX)!]. 

Definition compare : com := 
<[ EEX := 1;
   EAX := 0;
   while { b } inv (fun s => a1 s /\ a2 s ) do
         EGX := EDX + EAX;
         EGX := °EGX ;
         EHX := EFX + EAX;
         EHX := °EHX;
         assert (fun s => s EHX = s (s EFX + s EAX ) /\ 
                          s EGX = s (s EDX + s EAX ) /\ b s);
         if EGX <= EHX && ~ EGX = EHX then 
            EEX := 0
         else 
            if EHX <= EGX && ~ EGX = EHX then 
                  EEX := 2
            else 
                  skip 
            end
          end;
         EAX := EAX + 1
    end
 ]>.

Ltac mem_s s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax by lia;
       clear Heax.

Ltac mem_d s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax; [ | try (intros HF; inversion HF)];
       clear Heax.

Ltac mem_s_in s l1 l2 v H :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax in H by lia;
       clear Heax.

Ltac mem_d_in s l1 l2 v H:=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax in H; [ | try (intros HF; inversion HF)];
       clear Heax.

Example Hoare1 : hoare_triple (fun m => m(EDX) > 8 /\ m(EFX) > 8 ) 
                              (fun m' => True) compare Psi.empty_psi.
Proof.
apply recursion_hoare_triple with Phi.empty_phi.
* apply correct_proc.
  apply tc_p_empty_psi.
* apply correct;[ | simpl; auto].
  intros.
  apply Vcg_Opt.tc'_same.
  apply Vcg_Opt.Test.tc_test_same.
  intros.
  simpl.
  destruct n.
  - unfold Vcg_Opt.Test.test.
    simpl.
    intros.
    split.
    + unfold a1.
       rewrite H1.
       mem_s m'' EAX EAX 0.
       split; [auto | ].
       mem_d m'' EAX EBX 0.
       mem_d m'' EAX ECX 0.
       split; [apply Proc.Proc.le_0_l | apply Proc.Proc.le_0_l].
    + unfold a2.
      left.
      split.
       ** rewrite H1.
          mem_d m'' EAX EEX 0.
          rewrite H0.
          mem_s m EEX EEX 1.
          reflexivity.
        ** intros.
           rewrite H1 in H2.
           generalize (set'def m'' EAX 0 EAX).
           intros Heax; destruct Heax as ( Heax & _).
           rewrite Heax in H2 by reflexivity.
           destruct H2 as ( _ & He) ;inversion He.
  - destruct n.
    Focus 2.
    destruct n.
    + unfold Vcg_Opt.Test.test.
      simpl.
      intros.
      decompose [and] H4; clear H4.
      destruct H13.
      ** split.
         ++ unfold a1.
            rewrite H14.
            mem_s m''7 EAX EAX (m''7 EAX + 1).
            mem_d m''7 EAX EBX (m''7 EAX + 1).
            mem_d m''7 EAX ECX (m''7 EAX + 1).
            rewrite H10.
            mem_d m''5 EEX EAX 0.
            mem_d m''5 EEX EBX 0.
            mem_d m''5 EEX ECX 0.
            rewrite H8.
            mem_d m''4 EHX EAX (m''4 (m''4 EHX)).
            mem_d m''4 EHX EBX (m''4 (m''4 EHX)).
            mem_d m''4 EHX ECX (m''4 (m''4 EHX)).
            rewrite H6.
            mem_d m''3 EHX EAX (m''3 EFX + m''3 EAX).
            mem_d m''3 EHX EBX (m''3 EFX + m''3 EAX).
            mem_d m''3 EHX ECX (m''3 EFX + m''3 EAX).
            rewrite H7.
            mem_d m''2 EGX EAX (m''2 (m''2 EGX)).
            mem_d m''2 EGX EBX (m''2 (m''2 EGX)).
            mem_d m''2 EGX ECX (m''2 (m''2 EGX)).
            rewrite H5.
            mem_d m' EGX EAX (m' EDX + m' EAX).
            mem_d m' EGX EBX (m' EDX + m' EAX).
            mem_d m' EGX ECX (m' EDX + m' EAX).
            repeat split; lia.
        ++ unfold a2.
           right;left.
           rewrite H11.
           mem_d m''6 EAX EEX (m''6 EAX + 1).
           mem_d m''6 EAX EDX (m''6 EAX + 1).
           mem_d m''6 EAX EFX (m''6 EAX + 1).
           mem_s m''6 EAX EAX (m''6 EAX + 1).
           mem_d m''6 EAX (m''6 EDX + (m''6 EAX + 1 - 1)) (m''6 EAX + 1).
           mem_d m''6 EAX (m''6 EAX + 1 + (m''6 EFX - 1)) (m''6 EAX + 1).
           rewrite H10.
           mem_s m''5 EEX EEX 0.
           split;[reflexivity | ].
           mem_d m''5 EEX EDX 0.
           mem_d m''5 EEX EFX 0.
           mem_d m''5 EEX EAX 0.
           intros.
           mem_d m''5 EEX (m''5 EDX + (m''5 EAX + 1 - 1)) 0.
           mem_d m''5 EEX (m''5 EAX + 1 + (m''5 EFX - 1)) 0.
           rewrite H8 in H9.
           mem_d_in m''4 EHX EGX (m''4 (m''4 EHX)) H9.
           mem_s_in m''4 EHX EHX (m''4 (m''4 EHX)) H9.
           rewrite H6 in H9.
           mem_d_in m''3 EHX EGX (m''3 EFX + m''3 EAX) H9.
           mem_s_in m''3 EHX EHX (m''3 EFX + m''3 EAX) H9.
           mem_d_in m''3 EHX (m''3 EFX + m''3 EAX) (m''3 EFX + m''3 EAX) H9.
           rewrite H7 in H9.

Qed.


Definition assert3 : com := <[ assert (fun m => m EAX = 2) ;
                               skip;
                               assert (fun m => m EAX = 2) ]>.

Example test_tc :
forall m n,
m EAX = 2 -> (nth n (tc_test assert3 Phi.empty_phi) (fun _ => True)) m.
Proof.
simpl.
destruct n.
  * auto.
  * destruct n.
    + unfold test.
      simpl.
      intros.
      destruct H0.
      subst.
      assumption.
    + intros.
      destruct n; [auto|auto].
Qed.


(* TODO *)


(** Some ltac to mechanize the extraction of proof obligation from the list construct 
    in relational property verification **)

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

(* Tras **********************)

(*Definition rela_pre3 (l : list Sigma.sigma) : Prop :=
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
Qed.*)
