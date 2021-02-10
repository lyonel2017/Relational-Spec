From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Loc.

Require Import Program.
Require Import Eqdep_dec.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.

(** Definition of relational assertion **)

Definition r_assertion : Type := list sigma  -> Prop.

(* Definition of the relational evaluation of program*)

Inductive rceval : list com -> list sigma -> Psi.psi -> list sigma -> Prop :=
  | E_Empty : forall ps,
      rceval [] [] ps []
 | E_Seq : forall c qc s q s' q' ps,
      ceval c s ps s' ->
      rceval qc q ps q' ->
      rceval (c::qc) (s::q) ps (s'::q').

(* Definition of relational properties *)

Definition relational_prop (P Q: r_assertion) (c : list com) (ps : Psi.psi) : Prop := 
 forall s s',  length s = length c -> length s' = length c ->
               P s -> rceval c s ps s' -> Q s'.

(* A Hoare Triple is a Relational Property for one program *)

Section play_ground.

Lemma list_length_one:
forall (A: Type) (h:A) (q : list A), length (h :: q) = 1 -> q = [].
Proof.
intros.
simpl in H.
apply eq_add_S in H.
apply length_zero_iff_nil in H.
assumption.
Qed.

Lemma rela_hoare :
forall P Q c ps,
hoare_triple (fun s => P [s]) (fun s => Q [s]) c ps ->
relational_prop P Q [c] ps.
Proof.
unfold hoare_triple.
unfold relational_prop.
intros.
inversion H3;subst.
apply list_length_one in H0.
apply list_length_one in H1.
subst.
eapply H.
apply H2.
assumption.
Qed.

End play_ground.

(* Defintion of the verification condition generator for relational properties
   We use only the verification condition generator for Hoare Triples *)

Program Fixpoint rtc (cl : list com) (ml: list Sigma.sigma)
            (ps: Psi.psi) (suite : list Sigma .sigma -> Prop) 
            (hy:length cl = length ml): Prop :=
 match cl ,ml with
 | [],[] => suite []
 | c :: qc, m :: qm => 
   tc c m ps (fun m' => rtc qc qm ps (fun l => suite (m'::l))  _)
 | _, _ => !
end.

Next Obligation.
destruct cl.
- simpl in hy.
  symmetry in hy.
  apply length_zero_iff_nil in hy.
  subst ml.
  contradiction H0.
  split.
  reflexivity.
  reflexivity.
- destruct ml as [|m qm].
  discriminate hy.
  eapply H.
  split.
  reflexivity.
  reflexivity.
Qed.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as ( _ & contra).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (_ & contra ).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

(* Same as above but for the auxiliare goals*)

Program Fixpoint rtc' (cl : list com) (ml: list Sigma.sigma)
            (ps: Psi.psi)  
            (hy:length cl = length ml): Prop :=
 match cl ,ml with
 | [],[] => True
 | c :: qc, m :: qm => 
   tc' c m ps /\ rtc' qc qm ps _
 | _, _ => !
end.

Next Obligation.
destruct cl.
- simpl in hy.
  symmetry in hy.
  apply length_zero_iff_nil in hy.
  subst ml.
  contradiction H0.
  split.
  reflexivity.
  reflexivity.
- destruct ml as [|m qm].
  discriminate hy.
  eapply H.
  split.
  reflexivity.
  reflexivity.
Qed.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as ( _ & contra).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (_ & contra ).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

(* Facts about rtc and rtc' *)

Lemma mk_rtc_def :
forall P h q pi s sl (hy:length (h::q) = length (s::sl)),
exists (hyr:length q = length sl),
rtc (h :: q) (s::sl) pi P hy  =
tc h s pi (fun m' => rtc q sl pi (fun l => P (m'::l)) hyr).
Proof.
intros.
eexists.
program_simpl.
Qed.

Lemma mk_rtc'_def :
forall h q pi s sl (hy:length (h::q) = length (s::sl)),
exists (hyr:length q = length sl),
rtc' (h :: q) (s::sl) pi hy  =
(tc' h s pi /\ rtc' q sl pi hyr).
Proof.
intros.
eexists.
program_simpl.
Qed.

(* Connect between Hoare Triple and Relational Properties *)

Lemma hoare_rela :
forall (P Q: r_assertion) h q ps pi sl (hy:length q = length sl), 
(forall s2 s3 : sigma,
P (s2 :: sl) -> ceval h s2 ps s3 -> 
rtc q sl pi (fun sl : list sigma => Q (s3 :: sl)) hy) =
hoare_triple (fun s => P (s:: sl) ) 
             (fun s' => rtc q sl pi (fun sl : list sigma => Q (s' :: sl)) hy)
              h ps.
Proof.
intros.
unfold hoare_triple.
reflexivity.
Qed.

(* Proof that one can use a verification condition generator to proof Relational Properties *)

Lemma correct :
forall ps,
forall p (P Q: r_assertion),
(forall ml (hy:length p = length ml), 
P ml -> rtc' p ml ps hy) ->
(forall ml (hy:length p = length ml), 
P ml -> rtc p ml ps Q hy) -> 
relational_prop P Q p ps.
Proof.
intros ps p.
unfold relational_prop.
induction p.
*  intros.
   specialize (H0 []).
   simpl in H0.
   apply length_zero_iff_nil in H1.
   apply length_zero_iff_nil in H2.
   subst.
   apply H0.
   reflexivity.
   assumption.
*  intros.
   destruct s.
   + discriminate H1.
   + destruct s'.
   - discriminate H2.
   - inversion H4;subst.
    specialize (IHp (fun sl => P (s :: sl)) (fun sl => Q (s1 :: sl))).
    simpl in IHp.
    generalize H13.
    generalize H3.
    inversion H1.
    inversion H2.
    generalize H7.
    generalize H6.
    eapply IHp.
    ** intros.
       symmetry in H1.
       assert (hy2: length (a ::p) = length (s::ml)).
       {intros. simpl. rewrite hy. reflexivity. }
       specialize (H (s :: ml) hy2 H5).
       destruct (mk_rtc'_def a p ps s ml hy2) as (hyr & HYP).
       rewrite HYP in H.
       destruct H.
       replace hy with hyr.
       apply H8.
       apply eq_proofs_unicity.
       intros.
       lia.
    ** intros.
       generalize H10.
       generalize H5.
       generalize s s1.
       rewrite hoare_rela.
       eapply correct.
       ++ intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          specialize (H (m :: ml) hy2 H8).
          destruct (mk_rtc'_def a p ps m ml hy2) as (hyr & HYP).
          rewrite HYP in H.
          destruct H.
          replace hy with hyr.
          apply H.
          apply eq_proofs_unicity.
          intros.
          lia.
       ++ intros.
          assert (hy2: length (a ::p) = length (m::ml)).
          {intros. simpl. rewrite hy. reflexivity. }
          destruct (mk_rtc_def Q a p ps m ml hy2) as (hyr & HYP).
          specialize (H0 (m::ml) hy2).
          rewrite HYP in H0.
          replace hy with hyr.
          apply H0.
          assumption.
          apply eq_proofs_unicity.
          intros.
          lia.
Qed.

(* Examples of proofs of Relational Properties *)

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
apply correct.
(* Extract auxiliary proofs and proof it*)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct (mk_rtc'_def plus2 (plus2::[]) Psi.empty_psi s ml hy) as (hyr & HYP).
    rewrite HYP.
    split.
    - simpl. auto.
    - destruct ml.
      ++ discriminate hyr.
      ++ destruct (mk_rtc'_def plus2 [] Psi.empty_psi s0 ml hyr) as (hyr2 & HYP2).
        rewrite HYP2.
        split.
        ** simpl. auto.
        ** inversion hyr2.
          symmetry in H1.
          apply length_zero_iff_nil in H1.
          subst.
          simpl. auto.
(* Extract main proof *)
+ intros.
  destruct ml.
  * discriminate hy.
  * destruct (mk_rtc_def rela_post2 plus2 (plus2::[]) Psi.empty_psi s ml hy) as (hyr & HYP).
    rewrite HYP.
    destruct ml.
    - discriminate hyr.
    - assert (H1 : length ([] : list com) = length ml).
      { inversion hyr. reflexivity. }
      eapply consequence_tc_suite.
      ++ intros.
         destruct (mk_rtc_def (fun l : list sigma => rela_post2 (s1 :: l)) plus2 [] Psi.empty_psi s0 ml hyr) as (hyr2 & HYP2).
         rewrite HYP2.
         replace hyr2 with H1.
         ** apply (consequence_tc_suite _ _ _ (fun m' => s1 EAX = m' EAX)).
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
      ++ (* Extract relational precondition *) 
         inversion H1.
         symmetry in H2.
         apply length_zero_iff_nil in H2.
         subst.
         simpl in H.
         (* Proof on main goal *)
         simpl.
         intros.
         rewrite H2.
         rewrite H0.
         rewrite H.
         apply Why3_Set.set'def.
         reflexivity.
Qed.