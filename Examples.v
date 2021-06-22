From Rela Require Import Sigma.
From Rela Require Import Loc.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import Com.
From Rela Require Import Vcg.
From Rela Require Import Hoare_Triple.
From Rela Require Import Correct.
From Rela Require Import Rela.
Import Vcg.Why3_Set.
Import Vcg.Assn_b.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Program.
Require Import Eqdep_dec.
From Coq Require Import Lia.

(** Example of arithmetic expression **)

Import AexpNotations.

Definition example_aexp : aexp := [? EAX + 2 + (°EAX * 2) ?].

Example aexp1 :
forall st : sigma,
    aeval (EAX !-> 5 ; st) example_aexp = 13.
Proof.
reflexivity.
Qed.

(** Example of boolean expression **)

Import BexpNotations.

Definition example_bexp : bexp := [! true && ~ °EAX <= 4 !].

Print Visibility.

Example bexp1 :
forall st : sigma,
    beval (EAX !-> 5 ; st) example_bexp = true.
Proof.
reflexivity.
Qed.

(** Examples of commands **)

Import ComNotations.

Definition plus2 : com := <[ EAX := °EAX + 2 ]>.

Example ecom3 :
forall (s : sigma),
  ceval plus2 s Psi.empty_psi (EAX !-> (s EAX) + 2 ; s).
Proof.
intros.
unfold plus2.
apply E_Ass. reflexivity. reflexivity.
Qed.

Definition assert2 : com := <[ assert (fun s => s EAX = 2) ]>.

Example ecom4 :
forall (s : sigma),
  ceval assert2 (EAX !-> 2 ; s) Psi.empty_psi (EAX !-> 2 ; s).
Proof.
intros.
unfold assert2.
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

Definition plus3 : com := <[ EAX := °EAX + 2; EAX := °EAX + 2 ]>.

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

Definition if2 : com := <[ if °EAX = 4 then { plus2 } else { plus2 } end ]>.

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

Definition if3 : com := <[ EAX := °EAX + 2 ;
                          if °EAX = 4 then { plus2 } else { plus2 } end;
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

Definition if4 : com := <[ if °EAX = 2 then assert (fun m => m EAX = 2) else skip end ]>.

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


(** Examples of proofs of Relational Properties **)

Definition rela_pre2 (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 EAX = m2 EAX
  | _ => False
  end.

Definition rela_post2 (l : list Sigma.sigma) : Prop :=
  match l with
  | (m1 :: m2 :: []) => m1 EAX = m2 EAX
  | _ => False
  end.

Example Relation2 : relational_prop rela_pre2 rela_post2 (plus2 :: plus2 :: []) Psi.empty_psi.
Proof.
apply rcorrect  with Phi.empty_phi.
(* Verification of proofs proof obligation for procedure *)
+ apply tc_p_empty_psi.
(* Extracting auxiliary proofs proof obligation *)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct (mk_rtc'_def plus2 (plus2::[]) Phi.empty_phi s ml hy) as (hyr & HYP).
    rewrite HYP.
    split.
    - simpl. auto.
    - destruct ml.
      ++ discriminate hyr.
      ++ destruct (mk_rtc'_def plus2 [] Phi.empty_phi s0 ml hyr) as (hyr2 & HYP2).
        rewrite HYP2.
        split.
        ** simpl. auto.
        ** inversion hyr2.
          symmetry in H1.
          apply length_zero_iff_nil in H1.
          subst.
          simpl.
          (* Verification of auxiliary proofs proof obligation *)
           auto.
(* Extracting main proof obligation *)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct (mk_rtc_def rela_post2 plus2 (plus2::[]) Phi.empty_phi s ml hy) as (hyr & HYP).
    rewrite HYP.
    destruct ml.
    - discriminate hyr.
    - assert (H1 : length ([] : list com) = length ml).
      { inversion hyr. reflexivity. }
      eapply Vcg.consequence_tc_suite.
      ++ intros.
         destruct (mk_rtc_def (fun l : list sigma => rela_post2 (s1 :: l)) plus2 [] Phi.empty_phi s0 ml hyr) as (hyr2 & HYP2).
         rewrite HYP2.
         replace hyr2 with H1.
         ** apply (Vcg.consequence_tc_suite _ _ _ (fun m' => s1 EAX = m' EAX)).
            -- intros.
               inversion hyr2.
               symmetry in H4.
               apply length_zero_iff_nil in H4.
               subst.
               simpl.
               apply H2.
           -- apply H0.
         ** apply eq_proofs_unicity.
            intros.
            lia.
      ++ (* Extracting relational precondition *) 
         inversion H1.
         symmetry in H2.
         apply length_zero_iff_nil in H2.
         subst.
         simpl in H.
         (* Proof on main proof obligation *)
         simpl.
         intros.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply Why3_Set.set'def.
         reflexivity.
Qed.

Definition X1 : Loc.t:= 1.
Definition X2 : Loc.t:= 2.
Definition ret : Loc.t := 3.

Definition comp: com := <[ if °X1 <= °X2 && ~ °X1 = °X2 then
                                 ret := 0
                              else
                                 if °X2 <= °X1 && ~ °X1 = °X2  then
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
apply rcorrect  with Phi.empty_phi.
(* Verification of proofs proof obligation for procedure *)
+ apply tc_p_empty_psi.
(* Extracting auxiliary proofs proof obligation *)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct (mk_rtc'_def comp (comp::[]) Phi.empty_phi s ml hy) as (hyr & HYP).
    rewrite HYP.
    split.
    - simpl. auto. (* Verification of auxiliary proofs proof obligation for function 1*)

    - destruct ml.
      ++ discriminate hyr.
      ++ destruct (mk_rtc'_def comp [] Phi.empty_phi s0 ml hyr) as (hyr2 & HYP2).
        rewrite HYP2.
        split.
        ** simpl. auto. (* Verification of auxiliary proofs
                           proof obligation for function 1*)

        ** inversion hyr2.
          symmetry in H1.
          apply length_zero_iff_nil in H1.
          subst.
          simpl.  auto.
(* Extracting main proof obligation *)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct
      (mk_rtc_def rela_post_comp comp
      (comp::[]) Phi.empty_phi s ml hy) as (hyr & HYP).
    rewrite HYP.
    destruct ml.
    - discriminate hyr.
    - assert (H1 : length ([] : list com) = length ml).
      { inversion hyr. reflexivity. }
      eapply Vcg.consequence_tc_suite.
      ++ intros.
         destruct
           (mk_rtc_def (fun l : list sigma => rela_post_comp (s1 :: l))
            comp [] Phi.empty_phi s0 ml hyr) as (hyr2 & HYP2).
         rewrite HYP2.
         replace hyr2 with H1.
         ** apply (Vcg.consequence_tc_suite _ _ _ (fun m' => s1 ret + m' ret = 2)).
            -- intros.
               inversion hyr2.
               symmetry in H4.
               apply length_zero_iff_nil in H4.
               subst.
               simpl.
               apply H2.
           -- apply Vcg_Opt.tc_same. apply H0.
         ** apply eq_proofs_unicity.
            intros.
            lia.
      ++ (* Extracting relational precondition *)
         inversion H1.
         symmetry in H2.
         apply length_zero_iff_nil in H2.
         subst.
         simpl in H.
         (* Proof on main proof obligation *)
         apply Vcg_Opt.tc_same.
         simpl.
         intros.
         destruct H.
         destruct H0.
         -- destruct H2.
            ** subst.
            assert(H6: False).
            { lia. }
            contradiction H6.
            ** destruct H5.
              +++ subst.
                  rewrite (set''def _ _ _ 0).
                  rewrite (set''def _ _ _ 2).
                  all: try reflexivity.
              +++ subst.
                  assert(H6: False).
                  { lia. }
                  contradiction H6.
          -- destruct H2.
            ** destruct H4.
              +++ subst.
                  rewrite (set''def _ _ _ 2).
                  rewrite (set''def _ _ _ 0).
                  all: try reflexivity.
              +++ subst.
                  assert(H6: False).
                  { lia. }
                  contradiction H6.
            ** destruct H4.
              +++  subst.
                   assert(H6: False).
                   { lia. }
                   contradiction H6.
              +++ destruct H5.
                  *** subst.
                      subst.
                      assert(H6: False).
                      { lia. }
                      contradiction H6.
                  *** subst.
                      rewrite (set''def _ _ _ 1).
                      rewrite (set''def _ _ _ 1).
                      all: try reflexivity.
Qed.
