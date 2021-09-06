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