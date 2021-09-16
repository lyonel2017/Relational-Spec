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

Program Fixpoint rtc (cl : list com) (ml: list Sigma.sigma)
            (cls: Phi.phi) (suite : r_assertion)
            (hy:length cl = length ml): Prop :=
 match cl ,ml with
 | [],[] => suite []
 | c :: qc, m :: qm =>
   tc c m cls (fun m' => rtc qc qm cls (fun l => suite (m'::l))  _)
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

(** Connect between Hoare Triple and Relational Properties **)

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

(** Defintion of the generator of auxiliare goals for relational properties **)

Program Fixpoint rtc' (cl : list com) (ml: list Sigma.sigma)
            (cls : Phi.phi)
            (hy:length cl = length ml): Prop :=
 match cl ,ml with
 | [],[] => True
 | c :: qc, m :: qm =>
   tc' c m cls /\ rtc' qc qm cls _
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

(** Facts about rtc and rtc' **)

Lemma mk_rtc_def :
forall h q pi s sl (hy:length (h::q) = length (s::sl)),
exists (hyr:length q = length sl),
forall P,
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