From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Rela.

From Coq Require Import Program.
From Coq Require Import Eqdep_dec.
From Coq Require Import Lists.List.
Import ListNotations.

(** Defintion of the verification condition generator for relational properties,
   using the verification condition generator for Hoare Triples **)

Definition r_suite : Type := list Sigma.sigma -> list history -> Prop.

Program Fixpoint rtc (cl : list com) (ml: list Sigma.sigma) (hl: list history)
            (cls: Phi.phi) (suite : r_suite)
            (hy1:length cl = length ml) (hy2:length cl = length hl): Prop :=
 match cl,ml,hl with
 | [],[],[] => suite [] []
 | c :: qc, m :: qm, h :: qh =>
   tc c m h cls (fun m' h' => rtc qc qm qh cls (fun lm lh => suite (m'::lm) (h' :: lh)) _ _)
 | _,_,_ => !
end.

Next Obligation.
destruct cl.
- simpl in hy1.
  symmetry in hy1.
  apply length_zero_iff_nil in hy1.
  simpl in hy2.
  symmetry in hy2.
  apply length_zero_iff_nil in hy2.
  subst ml hl.
  contradiction H0.
  split.
  reflexivity.
  split.
  reflexivity. reflexivity.
- destruct ml as [|m qm].
  discriminate hy1.
  destruct hl as [|h hm].
  discriminate hy2.
  eapply H.
  split.
  reflexivity.
  split.
  reflexivity. reflexivity.
Qed.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as ( _ & contra).
destruct contra as ( _ & contra).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as ( _ & contra).
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as (_ & contra ).
destruct contra as (contra & _).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (_ & contra ).
destruct contra as (_ & contra ).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

(** Connect between Hoare Triple and Relational Properties **)

Lemma hoare_rela :
forall (P: r_precondition) (Q: r_postcondition) 
h q ps pi sl hl (hy1:length q = length sl) (hy2:length q = length hl),
(forall s2 s3 : sigma,
P (s2 :: sl) -> ceval h s2 ps s3 ->
rtc q sl hl pi (fun sl' _ => Q (s3 :: sl') (s2 :: sl)) hy1 hy2) =
hoare_triple (fun s => P (s:: sl) )
     (fun s' s => rtc q sl hl pi (fun sl' _ => Q (s' :: sl') (s :: sl)) hy1 hy2)
              h ps.
Proof.
intros.
unfold hoare_triple.
reflexivity.
Qed.

(** Defintion of the generator of auxiliare goals for relational properties **)

Program Fixpoint rtc' (cl : list com) (ml: list Sigma.sigma)
            (hl: list history) (cls : Phi.phi)
            (hy1:length cl = length ml) (hy2:length cl = length hl): Prop :=
 match cl,ml,hl with
 | [],[],[] => True
 | c :: qc, m :: qm, h :: qh =>
   tc' c m h cls /\ rtc' qc qm qh cls _ _
 | _,_, _ => !
end.

Next Obligation.
destruct cl.
- simpl in hy1.
  symmetry in hy1.
  apply length_zero_iff_nil in hy1.
  simpl in hy2.
  symmetry in hy2.
  apply length_zero_iff_nil in hy2.
  subst ml.
  subst hl.
  contradiction H0.
  split.
  reflexivity.
  split.
  reflexivity. reflexivity.
- destruct ml as [|m qm].
  discriminate hy1.
  destruct hl as [|h qh].
  discriminate hy2.
  eapply H.
  split.
  reflexivity.
  split.
  reflexivity. reflexivity.
Qed.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as ( _ & contra).
destruct contra as ( _ & contra).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as ( _ & contra).
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (contra & _).
discriminate contra.
intros contra.
destruct contra as (_ & contra ).
destruct contra as (contra & _).
discriminate contra.
Defined.

Next Obligation.
split.
intros.
intros contra.
destruct contra as (_ & contra ).
destruct contra as (_ & contra ).
discriminate contra.
intros contra.
destruct contra as (contra & _).
discriminate contra.
Defined.

(** Facts about rtc and rtc' **)

Lemma mk_rtc_def :
forall c q pi s sl h hl 
(hy1:length (c::q) = length (s::sl)) (hy2:length (c::q) = length (h::hl)),
exists (hyr1:length q = length sl),
exists (hyr2:length q = length hl),
forall P,
rtc (c :: q) (s::sl) (h::hl) pi P hy1 hy2  =
tc c s h pi (fun m' h' => rtc q sl hl pi (fun ml hl => P (m'::ml) (h'::hl)) hyr1 hyr2).
Proof.
intros.
eexists.
eexists.
program_simpl.
Qed.

Lemma mk_rtc'_def :
forall c q pi s sl h hl 
(hy1:length (c::q) = length (s::sl))
(hy2:length (c::q) = length (h::hl)),
exists (hyr1:length q = length sl),
exists (hyr2:length q = length hl),
rtc' (c :: q) (s::sl) (h::hl)pi hy1 hy2  =
(tc' c s h pi /\ rtc' q sl hl pi hyr1 hyr2).
Proof.
intros.
eexists.
eexists.
program_simpl.
Qed.