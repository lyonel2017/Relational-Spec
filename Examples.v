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

Definition f_pre: precondition := fun s =>
   s(X2) = (s(X3)) * (s(X4) - s(X1)) /\
   0 <= (s(X1)) /\ Nat.le (s(X1)) (s(X4)).

Definition f_post: postcondition := fun s _ =>
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

Example hoare_triple_mult: hoare_triple (fun _ => True) f_post com_1 f_psi.
Proof.
apply correct with (cl:=f_phi) (l:=[]).
(* Verification of proof obligation for procedure*)
* unfold f_psi, f_phi.
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
  + intros. simpl in H. unfold empty_precondition in H.
    contradiction.
* unfold f_psi, f_phi.
  (* Verification of auxilliary proof obligation for command com*)
  intros. apply Vcg_Opt.tc'_same.
    apply Vcg_Opt.Tc'_list.tc'_list_same.
      simpl.
      destruct n.
      + unfold Vcg_Opt.Tc'_list.continuation.
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
      + destruct n; [auto | auto].
 (* Main proof obligation for command com : the post condition hold*)
* unfold f_psi, f_phi.
    simpl.  intros.
    rewrite Proc.eqb_refl in H3.
    simpl in H3.
    apply H3.
Qed.

(** Some ltac to automatize the extraction of proof obligation from the list construct
    in relational property verification **)

Ltac ltc2 phi ps hy hyh:=
        destruct (mk_rtc'_def _ _ (phi_call (extract phi) ps) _ _ _ _ hy hyh)
           as (hyr1  & hyr2 & HYP);
        rewrite HYP;
        clear HYP hy hyh;
        rename hyr1 into hy;
        rename hyr2 into hyh.

Ltac ltc7 phi ps hy hyh H:=
  ltc2 phi ps hy hyh;
  split; [ clear hy hyh; simpl H; apply Vcg_Opt.tc'_same
         | first [ltc7 phi ps hy hyh H | simpl;auto] ].
  
Ltac ltc1 phi ps hy hyh ml H :=
         destruct ml;
         [ first [ discriminate hy | first [ltc7 phi ps hy hyh H | simpl;auto] ]
         | first [ discriminate hy | ltc1 phi ps hy hyh ml H ]
         ].

Ltac ltc6 phi ps hy hyh :=
       destruct (mk_rtc_def _ _ (phi_call (extract phi) ps) _ _ _ _ hy hyh) 
           as (hyr1 & hyr2 & HYP);
       rewrite HYP;
       clear HYP hy hyh;
       rename hyr1 into hy;
       rename hyr2 into hyh.

Ltac ltc3 phi ps hy hyh:=
    intro; intro; intros H1; 
    tryif ltc6 phi ps hy hyh
    then 
    eapply consequence_tc_suite;
    [ clear H1; ltc3 phi ps hy hyh
    | apply Vcg_Opt.tc_same; apply H1 ]
    else simpl; apply H1.

Ltac ltc5 phi ps hy hyh :=
    ltc6 phi ps hy hyh;
    eapply consequence_tc_suite;
    [ ltc3 phi ps hy hyh
    | apply Vcg_Opt.tc_same].

Ltac ltc4 ml hy hyh phi ps :=
         destruct ml;
         [ first [ discriminate hy | first [ltc5 phi ps hy hyh | simpl; auto] ]
         | first [ discriminate hy | ltc4 ml hy hyh phi ps ]
         ].

Ltac ltc0 phi l hyh := apply rcorrect 
                with (rcl:=phi) (h:=l) (hyh:=hyh);
                 [
                 | intros ps;
                   split;
                   [ intros ml hy H Hr;
                     ltc1 phi ps hy hyh ml H
                   | intros ml hy H Hr;
                     ltc4 ml hy hyh phi ps;
                     clear hy hyh;
                     simpl in H
                   ]
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

Definition rela_pre : r_precondition := fun l =>
  match l with
  | (m1 :: m2 :: []) => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2) /\
                         m1 X1 > 3 /\ m1 X2 > 3 /\ m2 X1 > 3 /\ m2 X2 > 3 /\
                         m1 X1 <> m1 X2 /\ m2 X1 <> m2 X2
  | _ => False
  end.

Definition rela_post : r_postcondition := fun l _ =>
  match l with
  | (m1 :: m2 :: []) => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2)
  | _ => False
  end.

Example relation_swap : relational_prop
                            rela_pre rela_post
                            (swap_1 :: swap_2 :: []) Psi.empty_psi.
Proof.
assert (hyh :length (swap_1 :: swap_2 :: []) = 
             length (empty_history:: empty_history :: [])).
{  simpl. reflexivity. }
ltc0 R_Phi.empty_r_phi (empty_history :: empty_history :: []) hyh.
(* Verification of proof obligation for procedure*)
+ apply rtc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl.
  intros.
  unfold X1, X2, X3 in *.
  decompose [and] H;clear H.
  decompose [and] H0;clear H0.
  decompose [and] H1;clear H1.
  split.
  * (*<1>*)
    rewrite H12.
    mem_d_in m''0 (m''0 2) 1 (m''0 3).
    mem_d_in m''0 (m''0 2) (m''0 1) (m''0 3).
    rewrite H11.
    mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
    mem_s m'' (m'' 1) (m'' 1) (m'' (m'' 2)).
    rewrite H.
    mem_d s 3 2 (s (s 1)).
    mem_d s 3 (s 2) (s (s 1)).
    (*<2>*)
    rewrite H14.
    mem_d_in m''2 (m''2 1) 1 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_s m''2 (m''2 1) (m''2 1) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H13.
    mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_s m''1 (m''1 2) (m''1 2) (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_d_in m''1 (m''1 2) (m''1 1) (m''1 (m''1 1) - m''1 (m''1 2)).
    rewrite H0.
    mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) (s0 2) (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
    mem_s s0 (s0 1) (s0 1) (s0 (s0 1) + s0 (s0 2)).
    - lia.
    (* all the little things *)
    - rewrite H0.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H13.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H0.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H11.
      mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H.
      mem_d s 3 1 (s (s 1)).
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H.
      mem_d s 3 1 (s (s 1)).
      lia.
      rewrite H.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H11.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H.
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H.
      mem_d s 3 1 (s (s 1)).
      lia.
 * (*<1>*)
    rewrite H12.
    mem_d_in m''0 (m''0 2) 2 (m''0 3).
    mem_s m''0 (m''0 2) (m''0 2) (m''0 3).
    rewrite H11.
    mem_d_in m'' (m'' 1) 3 (m'' (m'' 2)).
    rewrite H.
    mem_s s 3 3 (s (s 1)).
    (*<2>*)
    rewrite H14.
    mem_d_in m''2 (m''2 1) 2 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_d_in m''2 (m''2 1) (m''2 2) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H13.
    mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
    mem_s m''1 (m''1 2) (m''1 2)  (m''1 (m''1 1) - m''1 (m''1 2)).
    rewrite H0.
    mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) (s0 2) (s0 (s0 1) + s0 (s0 2)).
    mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
    mem_s s0 (s0 1) (s0 1) (s0 (s0 1) + s0 (s0 2)).
    - lia.
      (* all the little things*)
    - rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H13.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      mem_d_in m''1 (m''1 2) 2 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H0.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H13.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H0.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H0.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H11.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H.
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H.
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

Definition rela_pre_comp : r_precondition := fun l =>
  match l with
  | (m1 :: m2 :: []) => m1 X1 = m2 X2 /\ m1 X2 = m2 X1
  | _ => False
  end.

Definition rela_post_comp : r_postcondition := fun l _ =>
  match l with
  | (m1 :: m2 :: []) => m1 ret + (m2 ret) = 2
  | _ => False
  end.

Example relation_comp : relational_prop
                            rela_pre_comp rela_post_comp
                            (comp :: comp :: []) Psi.empty_psi.
Proof.
assert (hyh :length (comp :: comp :: []) = 
             length (empty_history:: empty_history :: [])).
{  simpl. reflexivity. }
ltc0 R_Phi.empty_r_phi (empty_history :: empty_history :: []) hyh.
(* Verification of proof obligation for procedure*)
+ apply rtc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl.
  intros.
  destruct H0.
  -- destruct H1.
     ** subst. lia.
     ** destruct H3.
        +++ subst.
            mem_s s ret ret 0.
            mem_s s0 ret ret 2.
            reflexivity.
        +++ subst. lia.
  -- destruct H1.
     ** destruct H2.
        +++ subst.
            mem_s s ret ret 2.
            mem_s s0 ret ret 0.
            reflexivity.
        +++ subst. lia.
     ** destruct H2.
        +++ subst. lia.
        +++ destruct H3.
           *** subst. lia.
           *** subst.
               mem_s s ret ret 1.
               mem_s s0 ret ret 1.
               reflexivity.
Qed.

(* Example 3 *)

(** Examples of proofs of relational properties using relational contract **)

Parameter f2 : Proc.t.

(* Procedure environment *)

Definition f2_psi (x': Proc.t) :=
        if Proc.eqb x' f2 then  <[ X1 := X1 + 1 ]> else Psi.empty_psi x'.

(* Definition of relational contract for procedure f *)

Definition f2_r_pre : r_precondition := fun l =>
  match l with
  | (m1 :: m2 :: []) => m1 X1 < m2 X1
  | _ => False
  end.

Definition f2_r_post : r_postcondition := fun l _ =>
  match l with
  | (m1 :: m2 :: []) => m1 X1 < m2 X1
  | _ => False
  end.

(* Definition of standard contract for procedure f *)

Definition f2_pre : r_precondition := fun l =>
  match l with
  | (m :: []) => True
  | _ => False
  end.

Definition f2_post : r_postcondition := fun l _ =>
  match l with
  | (m1 :: []) => True
  | _ => False
  end.


(* Relational contract environment *)

Scheme Equality for list.

Definition f_r_phi (x': list Proc.t) :=
        if (list_beq  Proc.t) Proc.eqb x' (f2 :: f2 :: []) 
        then (f2_r_pre,f2_r_post) 
        else
            if (list_beq  Proc.t) Proc.eqb x' (f2 :: []) 
            then (f2_pre,f2_post) 
            else R_Phi.empty_r_phi x'.

(** Relation Propery **)

Example relation_mono : relational_prop
                  f2_r_pre f2_r_post
                  (<[ call(f2) ]> :: <[ call(f2) ]> :: []) f2_psi.
Proof.
assert (hyh :length (<[ call(f2) ]>:: <[ call(f2) ]> :: []) = 
             length (empty_history:: empty_history :: [])).
{  simpl. reflexivity. }
ltc0 f_r_phi (empty_history :: empty_history :: []) hyh.
(* Verification of proof obligation for procedure *)
+ unfold rtc_p.
  intros.
  destruct (list_beq Proc.t Proc.eqb f0 [f2; f2]) eqn: E1.
   (* Proof oblication for relational property {f2_r_pre} f2 ~ f2 {f2_r_post} *)
    - apply internal_list_dec_bl in E1 ;[ | apply Proc.eqb_eq ].
      subst.
      destruct m;[ discriminate hy1 | ].
      destruct m;[ discriminate hy1 | ].
      destruct m;[ | discriminate hy1 ].
      split.
       (* Verification of auxilliary proof obligation *)
       * simpl.
         unfold f2_psi.
         rewrite Proc.eqb_refl.
         simpl.
         auto.
       (* Main proof obligation *)
       * simpl.
         unfold f2_psi, f_r_phi.
         simpl.
         rewrite Proc.eqb_refl.
         simpl.
         intros.
         subst.
         mem_s s X1 X1 (s X1 + 1).
         mem_s s0 X1 X1 (s0 X1 + 1).
         simpl in H.
         apply plus_lt_compat_r.
         unfold f_r_phi in H.
         simpl in H.
         rewrite Proc.eqb_refl in H.
         simpl in H.
         assumption.
   (* Verification of proof obligation for procedure f2*)
    - destruct (list_beq Proc.t Proc.eqb f0 [f2]) eqn: E2.
        * apply internal_list_dec_bl in E2 ;[ | apply Proc.eqb_eq ].
          subst.
          destruct m;[ discriminate hy1 | ].
          destruct m;[ | discriminate hy1 ].
          split.
          (* Verification of auxilliary proof obligation *)
          ** simpl.
             unfold f2_psi.
             rewrite Proc.eqb_refl.
             simpl.
             auto.
          (* Main proof obligation *)
          ** simpl.
             unfold f2_psi, f_r_phi.
             simpl.
             rewrite Proc.eqb_refl.
             simpl.
             intros.
             auto.
         * unfold f_r_phi in H.
           rewrite E1 in H.
           rewrite E2 in H.
           simpl in H.
           unfold empty_r_precondition in H.
           contradiction.
(* Proof obligation for relational property 
      {f2_r_pre} <[ call(f2) ]> ~ <[ call(f2) ]> {f2_r_post} 
*)
(* Verification of auxilliary proof obligation *)
+ simpl. unfold f_r_phi. simpl.
  rewrite Bool.andb_false_r.
  rewrite Proc.eqb_refl.
  simpl.
  auto.
+ simpl. unfold f_r_phi. simpl.
  rewrite Bool.andb_false_r.
  rewrite Proc.eqb_refl.
  simpl.
  auto.
(* Main proof obligation *)
+ simpl.
  intros.
  specialize (Hr (f2 :: f2 :: [])).
  unfold f_r_phi in Hr.
  replace (list_beq Proc.t Proc.eqb [f2; f2] [f2; f2]) with true in Hr.
  - specialize (Hr (s :: s0 :: []) (m' :: m'0 :: [])).
    simpl in Hr.
    apply Hr.
    all: try Lia.lia.
    split. apply H0.
    split. apply H1.
    auto.
  - simpl.
    symmetry.
    eapply Bool.andb_true_iff.
    split.
    apply Proc.eqb_eq. reflexivity.
    eapply Bool.andb_true_iff.
    split.
    apply Proc.eqb_eq. reflexivity.
    auto.
 Qed. 
