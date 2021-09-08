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

(*Definition tc_p (ps: Psi.psi) (cl : Phi.phi) : Prop :=
    forall f m, (get_pre (cl f)) m -> tc' (ps f) m cl /\
                tc (ps f) m cl (get_post (cl f)).*)
                
(* Relation contract translation *)

(* TODO :
  We need: 
  
  Parameter is_call : proc -> sigma -> sigma -> Prop
  Axiom connection ceval (call f) s ps s' -> is_call f s s'
  
  Check if a translation implies the initial relationnal properties
  
  Check if we need to distinguished the call: probably no
  *)

(* use simpl termination to get the proc_call to be generated and get 
   generalization : add a vcg specificaly for termination in file vcg
   and the notion of termination and total correcness 
   in the file Hoare triple *)

(* The notion of co-termination can be added in futur work *)

(* The vcg add proc_call after each procedure call *)

(* The rule for using relational properties is a form of cut.
  Maybe in the proof of compleness it can be shown that it is not
  required. But it allow clear/smaller proofs *)
  
Definition proc_call f s s' := forall ps, ceval (CCall f) s ps s'.

(*Program Fixpoint proc_to_pred p s s' (hy:length cl = length ml): Prop:=
match p, s, s' with
| [] , [], [] => True
| h :: q, s:: qs, s' :: qs' => proc_call p s s' /\ proc_to_pred q qs qs' _
| _, _, _ => !
end.

Definition tr (rcl:R_Phi.r_phi) := 
   forall p s s', proc_to_pred p -> (get_r_pre (rcl p)) s -> (get_r_post (rcl p)) s'.*)