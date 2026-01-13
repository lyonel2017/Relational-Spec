From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Vcg.
From Rela Require Import Proc.
From Rela Require Vcg_Opt.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Quadruple.
From Rela Require Import Rela.
From Rela Require Import Vcg_Rela.
From Rela Require Import Vcg_Quadruple.
From Rela Require Import Correct_Rela.
From Rela Require Import Correct_Quadruple.
Import Vcg.Why3_Set.
Import Vcg.Assn_b.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lia.
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
apply E_Assi. reflexivity.
Qed.

(** Some ltac to automatize the handling of memory states **)

Ltac mem_s s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax by lia;
       clear Heax.

Ltac mem_s_in s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( Heax & _);
       rewrite Heax; clear Heax.

Ltac mem_d s l1 l2 v :=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax; [ | first [ lia | (intros HF; discriminate HF)]];
       clear Heax.

Ltac mem_d_in s l1 l2 v:=
       generalize (set'def s l1 v l2);
       intros Heax; destruct Heax as ( _ & Heax);
       rewrite Heax; clear Heax.

(** Examples of proofs of Hoare Triples with verification condition generator **)

(* Body of procedure for multiplication *)

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
   s(X2) = s(X3) * (s(X4) - s(X1)) /\
   0 <= s(X1) /\ Nat.le (s(X1)) (s(X4)).

Definition f_post: postcondition := fun s s' =>
  s(X2) = s'(X3) * s'(X4).

(* Contract environment *)

Definition f_phi (x': Proc.t) :=
        if Proc.eqb x' f then (f_pre,f_post) else Phi.empty_phi x'.

(* Program computing the multiplication of X3 and X4 and put the result in X2 *)

Definition com_mult := <[
  X1 := X4;
  X2 := 0;
  call(f)
]>.

(* Proof that command com_mult satisfies the
   postcondition f_post ( X2 = X3 * X4) *)
Example hoare_triple_mult: hoare_triple (fun _ => True) f_post com_mult f_psi.
Proof.
apply correct with (cl:=f_phi) (l:=[]).
(* Verification of proof obligation for procedures *)
* unfold f_psi, f_phi.
  apply Vcg_Opt.tc_p_same.
  intros f0.
  destruct (Proc.eqb f0 f) eqn: E.
  + split.
     (* Verification of auxilliary proof obligation for procedure f *)
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
         destruct H.
         replace ((m X4 - (m X1 - 1))) with (S (m X4 - m X1 )) by lia.
         rewrite Loc.mul_succ_r.
         lia.
      ** destruct n; [auto | auto].
    (* Main proof obligation for procedure f : the postconditon hold*)
    - simpl.
      intros.
      destruct H0.
      ** decompose [and] H1;clear H1.
         rewrite Proc.eqb_refl in H6.
         simpl in H6.
         unfold f_post in H6.
         unfold f_post.
         rewrite  H6.
         rewrite H4.
         mem_d m'' X1 X3 (m'' X1 - 1).
         mem_d m'' X1 X4 (m'' X1 - 1).
         rewrite H2.
         mem_d m X2 X3 (m X2 + m X3).
         mem_d m X2 X4 (m X2 + m X3).
         reflexivity.
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
    unfold f_post in H3.
    unfold f_post.
    rewrite H3.
    rewrite H1.
    mem_d m' X2 X3 0.
    mem_d m' X2 X4 0.
    rewrite H0.
    mem_d m X1 X3 (m X4).
    mem_d m X1 X4 (m X4).
    reflexivity.
Qed.

(** Some ltac to automatize the extraction of proof obligation from
    the list construct in relational property verification **)

Ltac ltc7 :=
  split; [ apply Vcg_Opt.tc'_same
         | first [ltc7| simpl;auto] ].

Ltac ltc1 ml HPre :=
         destruct ml;
         [ first [ simpl in HPre; contradiction HPre | first [ltc7 | simpl;auto]]
         | first [ simpl in HPre; contradiction HPre | ltc1 ml HPre ]
         ].

Ltac ltc5 :=
   apply Vcg_Opt.tc_same;
   cbv delta [ Vcg_Opt.tc] iota beta match;
   intros; first [ ltc5 | simpl;auto ].

Ltac ltc4 ml HPre :=
         destruct ml;
         [ first [ simpl in HPre; contradiction HPre |
                   first [ltc5| simpl; auto] ]
         | first [ simpl in HPre; contradiction HPre| ltc4 ml HPre ]
         ].

Ltac ltc0 phi l := apply rcorrect
                with (rcl:=phi) (h:=l);
                 [
                 | intros ps;
                   split;
                   [ intros ml HPre Hr;
                     ltc1 ml HPre
                   | intros ml HPre Hr;
                       ltc4 ml HPre
                   ]
                ].

(** Examples of proofs of Relational Properties
    with verification condition generator **)

(** Example 1: Swap **)

(* Defintion of two swap functions *)

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
  | [m1; m2] => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2) /\
                         m1 X1 > 3 /\ m1 X2 > 3 /\ m2 X1 > 3 /\ m2 X2 > 3 /\
                         m1 X1 <> m1 X2 /\ m2 X1 <> m2 X2
  | _ => False
  end.

Definition rela_post : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 (m1 X1) = m2 (m2 X1) /\ m1 (m1 X2) = m2 (m2 X2)
  | _ => False
  end.

(* We proof that the swap function are equivalent *)

Example relation_swap : relational_prop
                            rela_pre rela_post
                            [swap_1; swap_2] Psi.empty_psi.
Proof.
  unfold swap_1.
  unfold swap_2.
ltc0 R_Phi.empty_phi [empty_history; empty_history].
(* Verification of proof obligation for procedure*)
+ unfold rtc_p.
  apply rtc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl in H.
  simpl in H0.
  simpl in HPre.
  unfold X1, X2, X3 in *.
  decompose [and] H;clear H.
  decompose [and] H0;clear H0.
  decompose [and] HPre;clear HPre.
  split.
  * (*<1>*)
    rewrite H4.
    mem_d_in m''0 (m''0 2) 1 (m''0 3).
    mem_d_in m''0 (m''0 2) (m''0 1) (m''0 3).
    rewrite H3.
    mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
    mem_s m'' (m'' 1) (m'' 1) (m'' (m'' 2)).
    rewrite H1.
    mem_d s 3 2 (s (s 1)).
    mem_d s 3 (s 2) (s (s 1)).
    (*<2>*)
    rewrite H6.
    mem_d_in m''2 (m''2 1) 1 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_s m''2 (m''2 1) (m''2 1) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H5.
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
    - rewrite H5.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H3.
      mem_d_in m'' (m'' 1) 1 (m'' (m'' 2)).
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H1.
      mem_d s 3 1 (s (s 1)).
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
      rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H3.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H1.
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
 * (*<1>*)
    rewrite H4.
    mem_d_in m''0 (m''0 2) 2 (m''0 3).
    mem_s m''0 (m''0 2) (m''0 2) (m''0 3).
    rewrite H3.
    mem_d_in m'' (m'' 1) 3 (m'' (m'' 2)).
    rewrite H1.
    mem_s s 3 3 (s (s 1)).
    (*<2>*)
    rewrite H6.
    mem_d_in m''2 (m''2 1) 2 (m''2 (m''2 1) - m''2 (m''2 2)).
    mem_d_in m''2 (m''2 1) (m''2 2) (m''2 (m''2 1) - m''2 (m''2 2)).
    rewrite H5.
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
    - rewrite H5.
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
    - rewrite H5.
      mem_d_in m''1 (m''1 2) 1 (m''1 (m''1 1) - m''1 (m''1 2)).
      rewrite H.
      mem_d s0 (s0 1) 1 (s0 (s0 1) + s0 (s0 2)).
      lia.
      rewrite H.
      mem_d s0 (s0 1) 2 (s0 (s0 1) + s0 (s0 2)).
      lia.
    - rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
    - rewrite H3.
      mem_d_in m'' (m'' 1) 2 (m'' (m'' 2)).
      rewrite H1.
      mem_d s 3 2 (s (s 1)).
      lia.
      rewrite H1.
      mem_d s 3 1 (s (s 1)).
      lia.
Qed.

  (** Example 2: Compare **)

(* Defintion of a comparator procedure *)

Definition comp: com :=
<[ if X1 <= X2 && ~ X1 = X2 then
      ret := 0
   else
      if X2 <= X1 && ~ X1 = X2  then
         ret := 2
      else
         ret := 1
      end
   end
]>.

(* Defintion of relational pre and post condition *)

Definition rela_pre_comp : r_precondition := fun l =>
  match l with
  | [m1; m2] => m1 X1 = m2 X2 /\ m1 X2 = m2 X1
  | _ => False
  end.

Definition rela_post_comp : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 ret + (m2 ret) = 2
  | _ => False
  end.

(* We proof anti-symmetry of the compare procedure *)

Example relation_comp : relational_prop
                            rela_pre_comp rela_post_comp
                            [comp; comp] Psi.empty_psi.
Proof.
  unfold comp.
  ltc0 R_Phi.empty_phi [empty_history; empty_history].
(* Verification of proof obligation for procedure*)
+ apply rtc_p_empty_psi.
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ unfold X1, X2 in *.
  simpl in H.
  simpl in H0.
  simpl in HPre.
  unfold X1, X2 in *.
  destruct H.
  -- destruct H0.
     ** subst. lia.
     ** destruct H2.
        +++ subst.
            mem_s s ret ret 0.
            mem_s s0 ret ret 2.
            reflexivity.
        +++ subst. lia.
  -- destruct H1.
     ** destruct H0.
        +++ subst.
            mem_s s ret ret 2.
            mem_s s0 ret ret 0.
            reflexivity.
        +++ subst. lia.
     ** destruct H0.
        +++ subst. lia.
        +++ destruct H3.
           *** subst. lia.
           *** subst.
               mem_s s ret ret 1.
               mem_s s0 ret ret 1.
               reflexivity.
Qed.

(** Example 3: Monotone **)

(** Examples of proofs of relational properties using relational contract **)

(* Procedure environment *)

Definition f2_psi (x': Proc.t) :=
        if Proc.eqb x' f2 then  <[ X1 := X1 + 1 ]> else Psi.empty_psi x'.

(* Definition of relational contract for procedure f *)

Definition f2_r_pre : r_precondition := fun l =>
  match l with
  | [m1; m2] => m1 X1 < m2 X1
  | _ => False
  end.

Definition f2_r_post : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 X1 < m2 X1
  | _ => False
  end.

(* Definition of standard contract for procedure f *)

Definition f2_pre : r_precondition := fun l =>
  match l with
  | [m] => True
  | _ => False
  end.

Definition f2_post : r_postcondition := fun l _ =>
  match l with
  | [m1] => True
  | _ => False
  end.

(* Relational contract environment *)

Scheme Equality for list.

Definition f2_r_phi (x': list Proc.t) :=
        if (list_beq  Proc.t) Proc.eqb x' [f2; f2]
        then (f2_r_pre,f2_r_post)
        else
            if (list_beq  Proc.t) Proc.eqb x' [f2]
            then (f2_pre,f2_post)
            else R_Phi.empty_phi x'.

(* We proof monotony of procedure f2 *)

Example relation_mono : relational_prop
                  f2_r_pre f2_r_post
                  [<[ call(f2);call(f2) ]>;
                   <[ call(f2);call(f2) ]> ] f2_psi.
Proof.
  ltc0 f2_r_phi [empty_history; empty_history].
(* Verification of proof obligation for procedure *)
+ unfold rtc_p.
  intros.
  destruct (list_beq Proc.t Proc.eqb f [f2; f2]) eqn: E1.
   (* Proof oblication for relational property {f2_r_pre} f2 ~ f2 {f2_r_post} *)
    - apply internal_list_dec_bl in E1 ;[ | apply Proc.eqb_eq ].
      subst.
      destruct m ;[ contradiction H | ].
      destruct m ; [ contradiction H| ].
      destruct m;[ | contradiction H ].
      split.
       (* Verification of auxilliary proof obligation *)
       * simpl.  auto.
       (* Main proof obligation *)
       * simpl. intros.  subst.
         mem_s s X1 X1 (s X1 + 1).
         mem_s s0 X1 X1 (s0 X1 + 1).
         simpl in H.
         apply Nat.add_lt_mono_r.
         assumption.
    - destruct (list_beq Proc.t Proc.eqb f [f2]) eqn: E2.
       (* Verification of proof obligation for procedure f2*)
        * apply internal_list_dec_bl in E2 ;[ | apply Proc.eqb_eq ].
          subst.
          destruct m ;[ contradiction H | ].
          destruct m ; [ |contradiction H ].
          split.
          (* Verification of auxilliary proof obligation *)
          ** simpl. auto.
          (* Main proof obligation *)
          ** simpl. auto.
        (* Nothing to do for other procedure *)
         * unfold f2_r_phi in H.
           rewrite E1 in H.
           rewrite E2 in H.
           apply get_r_pre_emphi_false in H.
           contradiction H.
(* Proof obligation for relational property
      {f2_r_pre} <[ call(f2);call(f2) ]> ~ <[ call(f2);call(f2) ]> {f2_r_post}
*)
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl in HPre.
  specialize (Hr [f2; f2]).
  generalize (Hr [s; s0 ] [m''; m''0]).
  intros H2.
  specialize (Hr [m''; m''0 ] [m'; m'0]).
  simpl in Hr.
  simpl in H2.
  apply Hr.
  all: try lia.
  split. apply H.
  split. apply H0.
  auto.
  apply H2.
  all: try lia.
  split. apply H.
  split. apply H0.
  auto.
 Qed.

(** Example 4: Nat Sum **)

(** Examples of proofs of relational properties using relational contract **)

(* Defintion of a functions that sum up all natural from 0 to X2*)

Definition f3_body: com := <[
  if X1 <= X2 && ~ X1 = X2 then
      X3 := X3 + X1;
      X1 := X1 + 1;
      call(f3)
  else
    skip
  end ]>.

(* Procedure environment *)

Definition f3_psi (x': Proc.t) :=
        if Proc.eqb x' f3 then f3_body else Psi.empty_psi x'.

(* Definition of relational contract for procedure f *)

Definition f3_r_pre : r_precondition := fun l =>
  match l with
  | [m1; m2] => m2 X1 <= m2 X2 /\ ~ (m2 X1 = m2 X2) /\
                        m1 X2 = m2 X2 /\
                        m1 X1 = m2 X1 + 1 /\
                        m1 X3 = m2 X3 + m2 X1
  | _ => False
  end.

Definition f3_r_post : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 X3 = m2 X3
  | _ => False
  end.

(* Definition of standard contract for procedure f *)

Definition f3_pre : r_precondition := fun l =>
  match l with
  | [m] => True
  | _ => False
  end.

Definition f3_post : r_postcondition := fun l_pre l_post =>
  match l_pre, l_post with
  | [m_post],[m_pre] => m_pre X1 >= m_pre X2 -> m_pre X3 = m_post X3
  | _,_ => False
  end.

(* Definition of relational pre and post condition *)

Definition r_pre : r_precondition := fun l =>
  match l with
  | [m1; m2] => m1 X2 = m2 X2
  | _ => False
  end.

Definition r_post : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 X3 = m2 X3
  | _ => False
  end.

(* Relational contract environment *)

Definition f3_r_phi (x': list Proc.t) :=
        if (list_beq  Proc.t) Proc.eqb x' [f3;f3]
        then (f3_r_pre,f3_r_post)
        else
            if (list_beq  Proc.t) Proc.eqb x' [f3]
            then (f3_pre,f3_post)
            else R_Phi.empty_phi x'.

(* We proof that summing all natural starting from 0 or 1 is equivalent *)

Example relation_sum : relational_prop
                  r_pre r_post
                  [<[ X1:= 1; X3 := 0; call(f3) ]>;
                   <[ X1:= 0; X3 := 0; call(f3) ]> ] f3_psi.
Proof.
  ltc0 f3_r_phi [empty_history; empty_history].
(* Verification of proof obligation for procedure *)
+ unfold rtc_p.
  intros.
  destruct (list_beq Proc.t Proc.eqb f [f3; f3]) eqn: E1.
   (* Proof oblication for relational property {f2_r_pre} f2 ~ f2 {f2_r_post} *)
    - apply internal_list_dec_bl in E1 ;[ | apply Proc.eqb_eq ].
      subst.
      destruct m;[ contradiction H | ].
      destruct m;[ contradiction H | ].
      destruct m;[ |  contradiction H ].
      split.
       (* Verification of auxilliary proof obligation *)
       * split.
         ++ apply Vcg_Opt.tc'_same.
            apply Vcg_Opt.Tc'_list.tc'_list_same.
            destruct n.
            ** simpl. unfold Vcg_Opt.Tc'_list.continuation.
               simpl. intros. auto.
           **  destruct n; [simpl;auto | simpl;auto].
         ++ split; [| simpl; auto].
            apply Vcg_Opt.tc'_same.
            apply Vcg_Opt.Tc'_list.tc'_list_same.
            destruct n.
            ** simpl. unfold Vcg_Opt.Tc'_list.continuation.
               simpl. auto.
            ** destruct n; [simpl;auto | simpl;auto].
       (* Main proof obligation *)
       * cbv delta [ fold_proc map f3_psi f3 Nat.eqb f3_body] iota beta match.
         ltc5.
         simpl in H.
         simpl in H1.
         simpl in H2.
         destruct H2.
         ++ destruct H1.
          ** specialize (H0 [f3; f3] [m''0;m''2] [m'; m'0]).
             simpl in H0.
             apply H0; clear H0.
             all: try lia.
             split. apply H4.
             split. apply H3.
             auto.
             decompose [and] H3;clear H3.
             decompose [and] H4;clear H4.
             rewrite H10.
             mem_d m'' X1 X2 (m'' X1 + 1).
             mem_d m'' X1 X3 (m'' X1 + 1).
             mem_s m'' X1 X1 (m'' X1 + 1).
             rewrite H3.
             mem_d s X3 X2 (s X3 + s X1).
             mem_d s X3 X1 (s X3 + s X1).
             mem_s s X3 X3 (s X3 + s X1).
             rewrite H6.
             mem_d m''1 X1 X2 (m''1 X1 + 1).
             mem_d m''1 X1 X3 (m''1 X1 + 1).
             mem_s m''1 X1 X1 (m''1 X1 + 1).
             rewrite H0.
             mem_d s0 X3 X2 (s0 X3 + s0 X1).
             mem_d s0 X3 X1 (s0 X3 + s0 X1).
             mem_s s0 X3 X3 (s0 X3 + s0 X1).
             simpl in H.
             lia.
          ** decompose [and] H3;clear H3.
             simpl in H.
             decompose [and] H;clear H.
             rewrite H4.
             rewrite <- H8.
             rewrite H7.
             mem_d m''1 X1 X3 (m''1 X1 + 1).
             rewrite H5.
             mem_s s0 X3 X3 (s0 X3 + s0 X1).
             lia.
             rewrite H7.
             mem_s m''1 X1 X1 (m''1 X1 + 1).
             mem_d m''1 X1 X2 (m''1 X1 + 1).
             rewrite H5.
             mem_d s0 X3 X1 (s0 X3 + s0 X1).
             mem_d s0 X3 X2 (s0 X3 + s0 X1).
             lia.
         ++ destruct H1.
          ** simpl in H. lia.
          ** simpl in H. lia.
    - destruct (list_beq Proc.t Proc.eqb f [f3]) eqn: E2.
       (* Verification of proof obligation for procedure f3*)
        * apply internal_list_dec_bl in E2 ;[ | apply Proc.eqb_eq ].
          subst.
          destruct m;[ contradiction H | ].
          destruct m;[ | contradiction H ].
          split.
          (* Verification of auxilliary proof obligation *)
          ** split.
             ++ apply Vcg_Opt.tc'_same.
                apply Vcg_Opt.Tc'_list.tc'_list_same.
                destruct n.
                -- simpl. unfold Vcg_Opt.Tc'_list.continuation.
                   simpl. auto.
                -- destruct n; [simpl;auto | simpl;auto].
             ++ simpl. auto.
          (* Main proof obligation *)
          ** cbv delta [ fold_proc map f3_psi f3 Nat.eqb f3_body] iota beta match.
             ltc5.
             simpl in H.
             simpl in H1.
             destruct H1.
             ++ lia.
             ++ rewrite H2.
                reflexivity.
    (* Nothing to do for other procedure *)
     * unfold f3_r_phi in H.
       rewrite E1 in H.
       rewrite E2 in H.
       apply get_r_pre_emphi_false in H.
       contradiction H.
(* Proof obligation for main relational property *)
(* Verification of auxilliary proof obligation *)
+ apply Vcg_Opt.Tc'_list.tc'_list_same.
  destruct n.
  ++ simpl. unfold Vcg_Opt.Tc'_list.continuation.
     simpl. intros. auto.
  ++ destruct n; [simpl; auto | simpl; auto].
+ apply Vcg_Opt.Tc'_list.tc'_list_same.
  simpl.
  destruct n.
  ++ simpl; unfold Vcg_Opt.Tc'_list.continuation.
     simpl. auto.
  ++ destruct n; [simpl; auto | simpl; auto].
(* Main proof obligation *)
+ simpl in HPre.
  simpl in H.
  simpl in H0.
  decompose [and] H0;clear H0.
  decompose [and] H;clear H.
  destruct (s X2) eqn:Horig.
  * rewrite <- H8.
    rewrite <- H4.
    rewrite H7.
    mem_s m'' X3 X3 0.
    rewrite H3.
    mem_s m''1 X3 X3 0.
    reflexivity.
    - rewrite H3.
      mem_d m''1 X3 X1 0.
      mem_d m''1 X3 X2 0.
      rewrite H1.
      mem_s s0 X1 X1 0.
      mem_d s0 X1 X2 0.
      lia.
    - rewrite H7.
      mem_d m'' X3 X1 0.
      mem_d m'' X3 X2 0.
      rewrite H0.
      mem_s s X1 X1 1.
      mem_d s X1 X2 1.
      lia.
 * specialize (Hr [f3; f3] [m''0; m''2] [m'; m'0]).
    simpl in Hr.
    apply Hr.
    all: try lia.
    split. apply H10.
    split. apply H6.
    auto.
    rewrite H3.
    mem_d m''1 X3 X1 0.
    mem_d m''1 X3 X2 0.
    mem_s m''1 X3 X3 0.
    rewrite H1.
    mem_s s0 X1 X1 0.
    mem_d s0 X1 X2 0.
    rewrite H7.
    mem_d m'' X3 X1 0.
    mem_d m'' X3 X2 0.
    mem_s m'' X3 X3 0.
    rewrite H0.
    mem_s s X1 X1 1.
    mem_d s X1 X2 1.
    lia.
 Qed.

(** Example 5: Monotone diff **)

(** Examples of proofs of relational properties using relational contract **)

(* Procedure environment *)

Definition f24_psi (x': Proc.t) :=
        if Proc.eqb x' f2 then  <[ X1 := X1 + 1 ]> else
        if Proc.eqb x' f4 then  <[ X1 := X1 + 2 ]> else
        Psi.empty_psi x'.

(* Definition of relational contract for procedure f *)

Definition f24_r_pre : r_precondition := fun l =>
  match l with
  | [m1; m2] => m1 X1 < m2 X1
  | _ => False
  end.

Definition f24_r_post : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 X1 < m2 X1
  | _ => False
  end.

(* Definition of standard contract for procedure f *)

Definition f4_pre : r_precondition := fun l =>
  match l with
  | [m] => True
  | _ => False
  end.

Definition f4_post : r_postcondition := fun l _ =>
  match l with
  | [m1] => True
  | _ => False
  end.

(* Relational contract environment *)

Definition f24_r_phi (x': list Proc.t) :=
        if (list_beq  Proc.t) Proc.eqb x' [f2; f4]
        then (f2_r_pre,f2_r_post)
        else
            if (list_beq  Proc.t) Proc.eqb x' [f2]
            then (f2_pre,f2_post) else
                if (list_beq  Proc.t) Proc.eqb x' [f4]
                then (f4_pre,f4_post)
                else R_Phi.empty_phi x'.

(* We proof monotonie of procedure f2 in respect to f4 *)

Example relation_mono_diff : relational_prop
                  f24_r_pre f24_r_post
                  [<[ call(f2)]>;
                   <[ call(f4)]> ] f24_psi.
Proof.
ltc0 f24_r_phi [empty_history; empty_history].
(* Verification of proof obligation for procedure *)
+ unfold rtc_p.
  intros.
  destruct (list_beq Proc.t Proc.eqb f [f2; f4]) eqn: E1.
   (* Proof oblication for relational property {f2_r_pre} f2 ~ f4 {f2_r_post} *)
    - apply internal_list_dec_bl in E1 ;[ | apply Proc.eqb_eq ].
      subst.
      destruct m;[ contradiction H| ].
      destruct m;[ contradict H | ].
      destruct m;[ | contradict H ].
      split.
       (* Verification of auxilliary proof obligation *)
       * simpl. auto.
       (* Main proof obligation *)
       * simpl.
         intros.  subst.
         mem_s s X1 X1 (s X1 + 1).
         mem_s s0 X1 X1 (s0 X1 + 2).
         simpl in H.
         apply Nat.add_lt_mono;[assumption| auto].
    - destruct (list_beq Proc.t Proc.eqb f [f2]) eqn: E2.
       (* Verification of proof obligation for procedure f2*)
        * apply internal_list_dec_bl in E2 ;[ | apply Proc.eqb_eq ].
          subst.
          destruct m;[ contradict H | ].
          destruct m;[ | contradict H ].
          split.
          (* Verification of auxilliary proof obligation *)
          ** simpl. auto.
          (* Main proof obligation *)
          ** simpl. intros. auto.
         * destruct (list_beq Proc.t Proc.eqb f [f4]) eqn: E3.
       (* Verification of proof obligation for procedure f2*)
          ++ apply internal_list_dec_bl in E3 ;[ | apply Proc.eqb_eq ].
             subst.
             destruct m;[ contradict H | ].
             destruct m;[ | contradict H ].
             split.
             (* Verification of auxilliary proof obligation *)
             *** simpl. auto.
             (* Main proof obligation *)
             *** simpl. intros. auto.
          (* Nothing to do for other procedure *)
           ++ unfold f24_r_phi in H.
              rewrite E1 in H.
              rewrite E2 in H.
              rewrite E3 in H.
              apply get_r_pre_emphi_false in H.
              contradiction H.
(* Proof obligation for relational property
      {f24_r_pre} <[ call(f2) ]> ~ <[ call(f4) ]> {f24_r_post}
*)
(* Verification of auxilliary proof obligation *)
+ simpl. auto.
+ simpl. auto.
(* Main proof obligation *)
+ simpl in HPre.
  intros.
  specialize (Hr [f2; f4] [s; s0 ] [m'; m'0]).
  simpl in Hr.
  apply Hr.
  all: try lia.
  split. apply H.
  split. apply H0.
  auto.
 Qed.


(** Example 6: Monotone diff **)

Definition l: com := <[
 if EAX <= 10 then
    EDX := EBX + EAX;
    EDX := °EDX;
    EEX := ECX + EAX;
    EEX := °EEX;
    if EDX = EEX then
      EAX := EAX + 1;
      call(f)
    else
      EFX := 1
    end
  else
   EFX := 0
 end ]>.

Definition r: com := <[
 if EAX <= 10 then
    EDX := EBX + EAX;
    EDX := °EDX;
    EEX := ECX + EAX;
    EEX := °EEX;
    if EDX = EEX then
      EAX := EAX + 1;
      EDX := EBX + EAX;
      EDX := °EDX;
      EEX := ECX + EAX;
      EEX := °EEX;
      if EDX = EEX then
        EAX := EAX + 1;
        call(f)
      else
        EFX := 1
      end
    else
      EFX := 1
    end
 else
   EFX := 0
 end ]>.

(* Procedure environment *)

Definition asyn_psi (x': Proc.t) :=
  if Proc.eqb x' f2 then l
  else
    if Proc.eqb x' f3 then r
    else Psi.empty_psi x'.

(* Definition of relational contract for procedure f *)

Definition equal_separation m1 m2 :=
  8 < m1 EBX /\ m1 EBX + 10 < m1 ECX /\
  8 < m2 EBX /\ m2 EBX + 10 < m2 ECX /\
  forall x, 0 <= x < 10 -> m1 (m1 EBX + x) = m2 (m2 EBX + x) /\
  forall x, 0 <= x < 10 -> m1 (m1 ECX + x) = m2 (m2 ECX + x).

Definition inv_pre : q_precondition :=
  fun m1 m2 =>
   equal_separation m1 m2 /\
   (m1 EAX < m2 EAX -> forall x, m1 EAX <= x /\ x < m2 EAX -> m1 (EBX + x) = m1 (ECX + x)) /\
   (m2 EAX < m1 EAX -> forall x, m2 EAX <= x /\ x < m1 EAX -> m2 (EBX + x) = m1 (ECX + x)).

Definition inv_post : q_postcondition := fun m1 m2  _ _ =>  m1 EFX = m2 EFX.

(*Le gauche preserve le fait qu'il est en avance quant il est en avance*)
Definition L : q_cond := fun m1 m2 =>
          andb (m1 EAX <=? 10) (m1 EAX <? m2 EAX \/ m2 EAX <? m1 EAX).

(*Le droite preser le fait qu'il est en avance quant il est en avance*)
Definition R : q_cond := fun m1 m2 =>
          andb (m2 EAX <? 10) (m1 EAX <? m2 EAX \/ m2 EAX <? m1 EAX).

Definition LR1 : q_cond := fun m1 m2 =>
      andb (10 <? (m1 EAX)) (10 <? (m2 EAX)).

Definition LR2 : q_cond := fun m1 m2 =>
      andb ((m1 EAX) <=? 10) ((m2 EAX) <? 10).

Definition LR : q_cond := fun m1 m2 => orb (LR1 m1 m2) (LR2 m1 m2).

(* Definition of relational pre and post condition *)

Definition r_pre_cond : r_precondition := fun l =>
  match l with
  | [m1; m2] => equal_separation m1 m2
  | _ => False
  end.

Definition r_post_cond : r_postcondition := fun l _ =>
  match l with
  | [m1; m2] => m1 EFX = m2 EFX
  | _ => False
  end.

(* Relational contract environment *)

Definition q_phi (f f': Proc.t) :=
        if andb (Proc.eqb f f2) (Proc.eqb f' f3)
        then (inv_pre,inv_post,L,R,LR)
        else Q_Phi.empty_phi f f'.

(* We proof that summing all natural starting from 0 or 1 is equivalent *)

Example relation_eq : relational_prop
                  r_pre r_post
                  [<[ EAX:= 0; EFX := 0; call(f2) ]>;
                   <[ EAX:= 0; EFX := 0; call(f3) ]> ] asyn_psi.
Proof.
apply qrcorrect with (rcl:=R_Phi.empty_phi) (qcl:=q_phi) (h:=[]).
- apply rtc_p_empty_psi.
- unfold qtc_p.
  intros f1 f2 ps1 ps2.
  unfold q_phi.
  case_eq (((f1 =? Proc.f2) && (f2 =? Proc.f3))%bool);simpl.
  intros [h1 h2]%andb_prop.
  + unfold inv_post, inv_pre, LR, L, R.
    split.
    * intros ml1 ml2 [[HPre1 [HPre2 HPre3]] [Ht [HLR [HL HR]]]].
      unfold asyn_psi.
      rewrite h1, h2.
      assert (H1: f2 = f3) by now apply Proc.eqb_eq.
      rewrite H1;simpl. clear H1.
      unfold l, r.
      split.
      -- unfold qtc';split; apply Vcg_Opt.tc'_same.
         ++ apply Vcg_Opt.Tc'_list.tc'_list_same.
            destruct n.
            simpl. unfold Vcg_Opt.Tc'_list.continuation.
            simpl. intros. auto.
            destruct n; [simpl;auto | simpl;auto].
         ++ apply Vcg_Opt.Tc'_list.tc'_list_same.
            destruct n.
            simpl. unfold Vcg_Opt.Tc'_list.continuation.
            simpl. intros. auto.
            destruct n; [simpl;auto | simpl;auto].
      -- unfold qtc.
         apply Vcg_Opt.tc_same.
         cbv delta [ Vcg_Opt.tc] iota beta match.
         intros.
         apply Vcg_Opt.tc_same.
         cbv delta [ Vcg_Opt.tc] iota beta match.
         intros.
         (* destruct H;simpl in H. *)
         (* decompose [and] H1;clear H1. *)
         (* destruct H0;simpl in H0. *)
         (* decompose [and] H1;clear H1. *)
         admit.
   * split.
     -- intros ml1 ml2 [[HPre1 [HPre2 HPre3]] [Ht HL ]].
        unfold asyn_psi.
        rewrite h1.
        unfold l.
        split.
        ++ unfold qtc';split; apply Vcg_Opt.tc'_same.
           apply Vcg_Opt.Tc'_list.tc'_list_same.
           destruct n.
           simpl. unfold Vcg_Opt.Tc'_list.continuation.
           simpl. intros. auto.
           destruct n; [simpl;auto | simpl;auto].
           apply Vcg_Opt.Tc'_list.tc'_list_same.
            destruct n.
            simpl. unfold Vcg_Opt.Tc'_list.continuation.
            simpl. intros. auto.
            destruct n; [simpl;auto | simpl;auto].
      ++  unfold qtc.
         apply Vcg_Opt.tc_same.
         cbv delta [ Vcg_Opt.tc] iota beta match.
         intros.
         apply Vcg_Opt.tc_same.
         cbv delta [ Vcg_Opt.tc] iota beta match.
         intros.
          admit.
   -- split;[admit |].
      intros m1 m2 [H1 [H2 [H3 H4]]].
      unfold LR1, LR2.

(* (** Example 6: Monotone diff **) *)

(* Parameter op : Com.com. *)

(* Definition op_psi (x': Proc.t) := *)
(*         if Proc.eqb x' Proc.op then op else Psi.empty_psi x'. *)

(* (* Definition of relational contract for procedure op *) *)

(* Definition op_r_contract_det : r_postcondition := fun l1 l2 => *)
(*   match l1,l2 with *)
(*   | [m1; m2], [m1'; m2'] => m1'(l) = m2'(l) /\ m1'(r) = m2'(r) -> m1(ret) = m2(ret) *)
(*   | _,_ => False *)
(*   end. *)

(* Definition op_r_contract_comm : r_postcondition := fun l1 l2 => *)
(*   match l1,l2 with *)
(*   | [m1; m2], [m1'; m2'] => m1'(l) = m2'(r) /\ m1'(r) = m2'(l) -> m1(ret) = m2(ret) *)
(*   | _,_ => False *)
(*   end. *)

(* Definition op_r_pre : r_precondition := fun l => *)
(*   match l with *)
(*   | [m1; m2] => m1(a) = m2(a) /\ m1(b) = m2(b) *)
(*   | _ => False *)
(*   end. *)

(* Definition op_r_post : r_postcondition := fun l _ => *)
(*   match l with *)
(*   | [m1; m2] => m1(ret) = m2(ret) *)
(*   | _ => False *)
(*   end. *)

(* Definition op_post : r_postcondition :=  fun l1 l2 => *)
(*   match l1, l2 with *)
(*   | [m],[m'] =>  m(x) = m'(x) /\ m(y) = m'(y) /\ *)
(*                  m(a) = m'(a) /\ m(b) = m'(b) *)
(*   | _,_ => False *)
(*   end. *)

(* Definition com1 := <[l := a; r := b; call(Proc.op); l := ret ; r := ret; call(Proc.op)]>. *)
(* Definition com2 := <[l := a; r := b; call(Proc.op); x := ret ; *)
(*                      l := b; r := a; call(Proc.op); y := ret; *)
(*                      l := x; r := y; call(Proc.op) ]>. *)

(* (* Relational contract environment *) *)

(* Definition op_r_phi (x': list Proc.t) := *)
(*         if (list_beq  Proc.t) Proc.eqb x' [Proc.op; Proc.op] *)
(*         then (fun _ => True ,fun l l' => op_r_contract_det l l' /\ op_r_contract_comm l l') *)
(*         else if (list_beq  Proc.t) Proc.eqb x' [Proc.op] *)
(*             then (fun _ => True,op_post) *)
(*             else R_Phi.empty_phi x'. *)

(* (* We proof monotonie of procedure f2 in respect to f4 *) *)

(* Example relation_op_goal : relational_prop *)
(*                   op_r_pre op_r_post [com1; com2] op_psi. *)
(* Proof. *)
(*   unfold com1, com2. *)
(* ltc0 op_r_phi [empty_history; empty_history]. *)
(* (* Verification of proof obligation for procedure *) *)
(* + admit. *)
(* + admit. *)
(* + admit. *)
(* (* Main proof obligation *) *)
(* + simpl in HPre. *)
(*   simpl in H. *)
(*   simpl in H0. *)
(*   decompose [and] H0;clear H0. *)
(*   decompose [and] H;clear H. *)
(*   (* clear H5 H12 H20 H29 H37. *) *)
(*   (* assert(H44: 2 = 2) by lia. *) *)
(*   (* assert(H45: 0 < 2) by lia. *) *)
(*   (* assert(H46: proc_call Proc.op m''3 m' ps /\ proc_call Proc.op m''13 m'0 ps /\ True). *) *)
(*   (* { split. assumption. split. assumption. auto. } *) *)
(*   (* generalize (Hr [Proc.op; Proc.op] [m''3; m''13] [m'; m'0] H44 H44 H45 H46 I); simpl; intro. *) *)
(*   (* destruct H1. *) *)
(*   (* apply H1. *) *)
(*   (* clear H1 H5 H46. *) *)
(*   (* rewrite H6. *) *)
(*   (* mem_s m''2 r r (m''2 ret). *) *)
(*   (* mem_d m''2 r l (m''2 ret). *) *)
(*   (* rewrite H10. *) *)
(*   (* mem_s m''1 l l (m''1 ret). *) *)
(*   (* mem_d m''1 l ret (m''1 ret). *) *)
(*   (* rewrite H36. *) *)
(*   (* mem_d m''12 r l (m''12 y). *) *)
(*   (* mem_s m''12 r r (m''12 y). *) *)
(*   (* rewrite H30. *) *)
(*   (* mem_s m''11 l l (m''11 x). *) *)
(*   (* mem_d m''11 l y (m''11 x). *) *)
(*   (* rewrite H34. *) *)
(*   (* mem_d m''10 y x (m''10 ret). *) *)
(*   (* mem_s m''10 y y (m''10 ret). *) *)
(*   (* split. *) *)
(*   (* * rewrite H31. *) *)
(*   (*   rewrite H27. *) *)
(*   (*   mem_d m''8 r x (m''8 a). *) *)
(*   (*   rewrite H21. *) *)
(*   (*   mem_d m''7 l x (m''7 b). *) *)
(*   (*   rewrite H25. *) *)
(*   (*   mem_s m''6 x x (m''6 ret). *) *)
(*   (*   assert(H46: proc_call Proc.op m''0 m''1 ps /\ proc_call Proc.op m''5 m''6 ps /\ True). *) *)
(*   (*   { split. assumption. split. assumption. auto. } *) *)
(*   (*   generalize (Hr [Proc.op; Proc.op] [m''0; m''5] [m''1; m''6] H44 H44 H45 H46 I); simpl; intro. *) *)
(*   (*   destruct H1. *) *)
(*   (*   apply H1. *) *)
(*   (*   clear H1 H5 H46. *) *)
(*   (*   rewrite H4. *) *)
(*   (*   mem_d m'' r l (m'' b). *) *)
(*   (*   mem_s m'' r r (m'' b). *) *)
(*   (*   rewrite H2. *) *)
(*   (*   mem_s s l l (s a). *) *)
(*   (*   mem_d s l b (s a). *) *)
(*   (*   rewrite H19. *) *)
(*   (*   mem_d m''4 r l (m''4 b). *) *)
(*   (*   mem_s m''4 r r (m''4 b). *) *)
(*   (*   rewrite H0. *) *)
(*   (*   mem_s s0 l l (s0 a). *) *)
(*   (*   mem_d s0 l b (s0 a). *) *)
(*   (*   assumption. *) *)
(*   (* * assert(H46: proc_call Proc.op m''0 m''1 ps /\ proc_call Proc.op m''9 m''10 ps /\ True). *) *)
(*   (*   { split. assumption. split. assumption. auto. } *) *)
(*   (*   generalize (Hr [Proc.op; Proc.op] [m''0; m''9] [m''1; m''10] H44 H44 H45 H46 I); simpl; intro. *) *)
(*   (*   destruct H1. *) *)
(*   (*   apply H5. *) *)
(*   (*   clear H1 H5 H46. *) *)
(*   (*   rewrite H4. *) *)
(*   (*   mem_d m'' r l (m'' b). *) *)
(*   (*   mem_s m'' r r (m'' b). *) *)
(*   (*   rewrite H2. *) *)
(*   (*   mem_s s l l (s a). *) *)
(*   (*   mem_d s l b (s a). *) *)
(*   (*   rewrite H27. *) *)
(*   (*   mem_d m''8 r l (m''8 a). *) *)
(*   (*   mem_s m''8 r r (m''8 a). *) *)
(*   (*   rewrite H21. *) *)
(*   (*   mem_s m''7 l l (m''7 b). *) *)
(*   (*   mem_d m''7 l a (m''7 b). *) *)
(*   (*   rewrite H25. *) *)
(*   (*   mem_d m''6 x b (m''6 ret). *) *)
(*   (*   mem_d m''6 x a (m''6 ret). *) *)
(*   (*   rewrite H26. *) *)
(*   (*   rewrite H24. *) *)
(*   (*   rewrite H19. *) *)
(*   (*   mem_d m''4 r a (m''4 b). *) *)
(*   (*   mem_d m''4 r b (m''4 b). *) *)
(*   (*   rewrite H0. *) *)
(*   (*   mem_d s0 l a (s0 a). *) *)
(*   (*   mem_d s0 l b (s0 a). *) *)
(*   (*   assumption. *) *)
(* Admitted. *)


(* (*Two procedure that performes a recursice operation twice on two location but not in *)
(* the same order on the location *)

(* Generalize the skeduling rule for loops to recursive procedure. *)

(* *) *)


(* (* Definition op_psi (x': Proc.t) := *) *)
(* (*         if Proc.eqb x' Proc.op then op else Psi.empty_psi x'. *) *)

(* (* (* Definition of relational contract for procedure op *) *) *)

(* (* Definition op_r_contract_det : r_postcondition := fun l1 l2 => *) *)
(* (*   match l1,l2 with *) *)
(* (*   | [m1; m2], [m1'; m2'] => m1'(l) = m2'(l) /\ m1'(r) = m2'(r) -> m1(ret) = m2(ret) *) *)
(* (*   | _,_ => False *) *)
(* (*   end. *) *)

(* (* Definition op_r_contract_comm : r_postcondition := fun l1 l2 => *) *)
(* (*   match l1,l2 with *) *)
(* (*   | [m1; m2], [m1'; m2'] => m1'(l) = m2'(r) /\ m1'(r) = m2'(l) -> m1(ret) = m2(ret) *) *)
(* (*   | _,_ => False *) *)
(* (*   end. *) *)

(* (* Definition op_r_pre : r_precondition := fun l => *) *)
(* (*   match l with *) *)
(* (*   | [m1; m2] => m1(a) = m2(a) /\ m1(b) = m2(b) *) *)
(* (*   | _ => False *) *)
(* (*   end. *) *)

(* (* Definition op_r_post : r_postcondition := fun l _ => *) *)
(* (*   match l with *) *)
(* (*   | [m1; m2] => m1(ret) = m2(ret) *) *)
(* (*   | _ => False *) *)
(* (*   end. *) *)

(* (* Definition op_post : r_postcondition :=  fun l1 l2 => *) *)
(* (*   match l1, l2 with *) *)
(* (*   | [m],[m'] =>  m(x) = m'(x) /\ m(y) = m'(y) /\ *) *)
(* (*                  m(a) = m'(a) /\ m(b) = m'(b) *) *)
(* (*   | _,_ => False *) *)
(* (*   end. *) *)

(* (* Definition com1 := <[l := a; r := b; call(Proc.op); l := ret ; r := ret; call(Proc.op)]>. *) *)
(* (* Definition com2 := <[l := a; r := b; call(Proc.op); x := ret ; *) *)
(* (*                      l := b; r := a; call(Proc.op); y := ret; *) *)
(* (*                      l := x; r := y; call(Proc.op) ]>. *) *)

(* (* (* Relational contract environment *) *) *)

(* (* Definition op_r_phi (x': list Proc.t) := *) *)
(* (*         if (list_beq  Proc.t) Proc.eqb x' [Proc.op; Proc.op] *) *)
(* (*         then (fun _ => True ,fun l l' => op_r_contract_det l l' /\ op_r_contract_comm l l') *) *)
(* (*         else if (list_beq  Proc.t) Proc.eqb x' [Proc.op] *) *)
(* (*             then (fun _ => True,op_post) *) *)
(* (*             else R_Phi.empty_r_phi x'. *) *)

(* (* (* We proof monotonie of procedure f2 in respect to f4 *) *) *)

(* (* Example relation_op_goal : relational_prop *) *)
(* (*                   op_r_pre op_r_post [com1; com2] op_psi. *) *)
(* (* Proof. *) *)
