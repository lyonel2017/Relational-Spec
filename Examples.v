From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Vcg.
From Rela Require Import Proc.
From Rela Require Vcg_Opt.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Rela.
From Rela Require Import Vcg_Rela.
From Rela Require Import Correct_Rela.
Import Vcg.Why3_Set.
Import Vcg.Assn_b.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Program.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lia.
From Coq Require Import Omega.
Require Import Arith.

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

(** Some ltac to automatize the handling of memory states **)

Ltac mem_s s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax by lia;
       clear Heax.

Ltac mem_d s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax; [ | first [ lia | (intros HF; inversion HF)]];
       clear Heax.

Ltac mem_s_in s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax; clear Heax.

Ltac mem_d_in s l1 l2 v:=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax; clear Heax.

(** Examples of proofs of Hoare Triples with verification condition generator **)

Parameter f : Proc.t.

(* Body of procedure f: perfom multiplication *)

Definition mult: com := <[ 
  if 0 <= X1 && ~ X1 = 0 then
      X2 := X2 + X3;
      X1 := X1 - 1;
      call(f)
  else
    skip
  end ]>.

(* Procedure environment *)

Definition f_psi (x': Proc.t) :=
        if Proc.eqb x' f then mult else Psi.empty_psi x'.

(* Contract of pre and post condition of procedure f *)

Definition f_pre: assertion := fun s => 
   s(X2) = (s(X3)) * (s(X4) - s(X1)) /\
   0 <= (s(X1)) /\ Nat.le (s(X1)) (s(X4)).

Definition f_post: assertion := fun s =>
  s(X2) = (s(X3)) * (s(X4)).

(* Contract environment *)

Definition f_phi (x': Proc.t) :=
        if Proc.eqb x' f then (f_pre,f_post) else Phi.empty_phi x'.

(* Program computing the multiplication of X3 and X4 and put the result in X2 *)

Definition com_1 := <[ 
  X1 := X4;
  X2 := 0;
  call(f)
]>.

Example Hoare_tiple :hoare_triple (fun _ => True) 
                              (fun m => f_post m) com_1 f_psi.
Proof.
apply recursion_hoare_triple with f_phi.
(* Verification of auxiliary proofs proof obligation for procedure*)
* apply correct_proc.
  unfold f_psi, f_phi.
  apply Vcg_Opt.tc_p_same.
  intros f0.
  destruct (Proc.eqb f0 f) eqn: E.
  + split.
     (* Verification of auxilliary proof obligation for procedure f*)
    - apply Vcg_Opt.Tc'_list.tc'_list_same.
      simpl.
      destruct n.
      ** unfold Vcg_Opt.Tc'_list.continuation.
         simpl.
         intros.
         rewrite Proc.eqb_refl.
         simpl.
         unfold f_pre.
         rewrite H2.
         mem_d m'' X1 X2 (m'' X1 - 1).
         mem_d m'' X1 X3 (m'' X1 - 1).
         mem_d m'' X1 X4 (m'' X1 - 1).
         mem_s m'' X1 X1 (m'' X1 - 1).
         rewrite H1.
         mem_s m X2 X2 (m X2 + m X3).
         mem_d m X2 X3 (m X2 + m X3).
         mem_d m X2 X4 (m X2 + m X3).
         mem_d m X2 X1 (m X2 + m X3).
         simpl in H.
         unfold f_pre in H.
         split.
         ++ destruct H.
            replace ((m X4 - (m X1 - 1))) with (S (m X4 - m X1 )).
            rewrite Loc.mul_succ_r.
            all : try lia.
         ++ split. all: try lia.
      ** destruct n; [auto | auto].
    (* Main proof obligation for procedure f : the postconditon hold*)
    - simpl.
      intros.
      destruct H0.
      ** decompose [and] H1;clear H1.
         rewrite Proc.eqb_refl in H6.
         apply H6.
      ** rewrite H1.
         unfold f_post.
         simpl in H.
         unfold f_pre in H.
         decompose [and] H;clear H.
         lia.
  + split.
    - auto.
    - simpl. intros. unfold empty_postcondition. auto.
* apply correct.
  unfold f_psi, f_phi.
  (* Verification of auxilliary proof obligation for command com*)
  + intros. apply Vcg_Opt.tc'_same.
    apply Vcg_Opt.Tc'_list.tc'_list_same.
      simpl.
      destruct n.
      ** unfold Vcg_Opt.Tc'_list.continuation.
         simpl.
         intros.
         rewrite Proc.eqb_refl.
         simpl.
         unfold f_pre.
         rewrite H1.
         mem_s m'' X2 X2 0.
         mem_d m'' X2 X3 0.
         mem_d m'' X2 X4 0.
         mem_d m'' X2 X1 0.
         rewrite H0.
         mem_d m X1 X3 (m X4).
         mem_d m X1 X4 (m X4).
         mem_s m X1 X1 (m X4).
         lia.
      ** destruct n; [auto | auto].
 (* Main proof obligation for command com : the post condition hold*)
  + unfold f_psi, f_phi.
    simpl.  intros.
    rewrite Proc.eqb_refl in H3.
    simpl in H3.
    apply H3.
Qed. 

(** Some ltac to automatize the extraction of proof obligation from the list construct 
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

(** Examples of proofs of Relational Properties 
    with verification condition generator **)

(* Example 1 *)

(* Defintion of a swap functions *)

Definition swap_1: com := <[ X3 := °X1;
                             °X1 := °X2;
                             °X2 := X3
                           ]>.

Definition swap_2: com := <[ °X1 := °X1 + °X2;
                             °X2 := °X1 - °X2;
                             °X1 := °X1 - °X2
                           ]>.

(* Defintion of relational pre and post condition *)

Definition rela_pre (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2) /\
                         m1 X1 > 3 /\ m1 X2 > 3 /\ m2 X1 > 3 /\ m2 X2 > 3 /\
                         m1 X1 <> m1 X2 /\ m2 X1 <> m2 X2
  | _ => False
  end.

Definition rela_post (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2)
  | _ => False
  end.

Example Relation_swap : relational_prop
                            rela_pre rela_post
                            (swap_1 :: swap_2 :: []) Psi.empty_psi.
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
  unfold X1, X2, X3 in *.
  decompose [and] H;clear H.
  decompose [and] H2;clear H2.
  decompose [and] H1;clear H1.
  split.
  * (*<1>*)
    rewrite H6.
    mem_d_in m''0 (m''0 2) 1 (m''0 3).
    mem_d_in m''0 (m''0 2) (m''0 1) (m''0 3).
    rewrite H5.
    mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
    mem_s m'' (m'' 1) (m'' 1) (m'' (m'' 2)).
    rewrite H3.
    mem_d s 3 2 (s (s 1)).
    mem_d s 3 (s 2) (s (s 1)).
    (*<2>*)
    rewrite H8.
    mem_d_in m''2 (m''2 1) 1 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_s m''2 (m''2 1) (m''2 1) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H7.
    mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_s m''1 (m''1 2) (m''1 2) (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_d_in m''1 (m''1 2) (m''1 1) (m''1 (m''1 1) - m''1 (m''1 2)).
    rewrite H.
    mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) (s0 2) (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
    mem_s s0 (s0 1) (s0 1) (s0 (s0 1) + s0 (s0 2)).
    - lia.
    (* all the little things *)
    - rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H7.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H5.
      mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H3.
      mem_d s 3 1 (s (s 1)).
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
      rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
   - rewrite H5.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H3.
      mem_d s 3 2 (s (s 1)).
      lia. 
      rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
 * (*<1>*)
    rewrite H6.
    mem_d_in m''0 (m''0 2) 2 (m''0 3).
    mem_s m''0 (m''0 2) (m''0 2) (m''0 3).
    rewrite H5.
    mem_d_in m'' (m'' 1) 3 (m'' (m'' 2)).
    rewrite H3.
    mem_s s 3 3 (s (s 1)).
    (*<2>*)
    rewrite H8.
    mem_d_in m''2 (m''2 1) 2 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_d_in m''2 (m''2 1) (m''2 2) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H7.
    mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_s m''1 (m''1 2) (m''1 2)  (m''1 (m''1 1) - m''1 (m''1 2)).
    rewrite H.
    mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) (s0 2) (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
    mem_s s0 (s0 1) (s0 1) (s0 (s0 1) + s0 (s0 2)).
    - lia.
      (* all the little things*)
    - rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H7.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H7.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H5.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H3.
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H3.
      mem_d s 3 1 (s (s 1)).
      lia.
Qed.

(* Example 2 *)

(* Defintion of a comparator function *)

Definition comp: com := <[ if X1 <= X2 && ~ X1 = X2 then
                                 ret := 0
                              else
                                 if X2 <= X1 && ~ X1 = X2  then
                                   ret := 2
                                 else ret := 1
                                 end
                              end ]>.

(* Defintion of relational pre and post condition *)

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
            mem_s s ret ret 0.
            mem_s s0 ret ret 2.
            reflexivity.
        +++ subst. lia.
  -- destruct H2.
     ** destruct H3.
        +++ subst.
            mem_s s ret ret 2.
            mem_s s0 ret ret 0.
            reflexivity.
        +++ subst. lia.
     ** destruct H4.
        +++  subst. lia.
        +++ destruct H3.
           *** subst. lia.
           *** subst.
               mem_s s ret ret 1.
               mem_s s0 ret ret 1.
               reflexivity.
Qed.