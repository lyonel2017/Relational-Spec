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

(** Definition of a relational verification condition generator for procedures **)

Definition rtc_p (ps: Psi.psi) (cl : Phi.phi) (rcl : R_Phi.r_phi) : Prop :=
    forall f m, 
    let c := (map ps f) in
    let h := (map (fun _ => []) f) in
    forall (hy1:length c = length m) (hy2:length c = length h),
    (get_r_pre (rcl f)) m -> rtc' c m h cl hy1 hy2 /\
                             rtc c m h cl (fun m' _ => (get_r_post (rcl f)) m' m) hy1 hy2.

(** Translation of a list of procedure call to Prop **)

Parameter proc_call: Proc.Proc.t -> sigma -> sigma -> Prop.

Axiom test: forall y s s' ps, ceval (CCall y) s ps s' <-> proc_call y s s'.

Program Fixpoint proc_to_pred p s s' (hy1:length p = length s) 
                                     (hy2:length p = length s'): Prop:=
match p, s, s' with
| [] , [], [] => True
| h :: q, s:: qs, s' :: qs' => proc_call h s s' /\ proc_to_pred q qs qs' _ _
| _, _, _ => !
end.

Next Obligation.
destruct p.
- simpl in hy1.
  symmetry in hy1.
  apply length_zero_iff_nil in hy1.
  simpl in hy2.
  symmetry in hy2.
  apply length_zero_iff_nil in hy2.
  subst s.
  subst s'.
  contradiction H0.
  split.
  reflexivity.
  split.
  reflexivity. reflexivity.
- destruct s as [|s qs].
  discriminate hy1.
  destruct s' as [|s' qs'].
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

(** Facts about proc_to_pred**)

Lemma mk_proc_to_pred_def :
forall c q s sl s' sl'
(hy1:length (c::q) = length (s::sl)) (hy2:length (c::q) = length (s'::sl')),
exists (hyr1:length q = length sl),
exists (hyr2:length q = length sl'),
proc_to_pred (c :: q) (s::sl) (s'::sl') hy1 hy2  =
(proc_call c s s' /\ proc_to_pred q sl sl' hyr1 hyr2).
Proof.
intros.
eexists.
eexists.
program_simpl.
Qed.

Lemma rceval_proc_to_prod p s s' ps (hy1:length p = length s) (hy2:length p = length s') :
proc_to_pred p s s' hy1 hy2 -> rceval (fold_call p) s ps s' .
Proof.
generalize dependent hy2.
generalize dependent hy1.
generalize dependent s'.
generalize dependent s.
induction p; intros.
  + destruct s;[| inversion hy1].
    destruct s';[| inversion hy2].
    simpl. apply E_Empty.
  + destruct s;[inversion hy1| ].
    destruct s';[inversion hy2| ].
    specialize (mk_proc_to_pred_def a p s s0 s1 s' hy1 hy2) as (hyr1 & hyr2 & HYP).
    rewrite HYP in H.
    simpl.
    apply E_Seq.
    - apply test. apply H.
    - inversion hy1.
      inversion hy2.
     apply IHp with (hy1:= hyr1)(hy2:= hyr2). apply H.
Qed.

(** Translation of a relational contract into Prop **)

Definition tr (rcl:R_Phi.r_phi) :=
   forall p s s' (hy1:length p = length s) (hy2:length p = length s'),
          0 < length p ->
          proc_to_pred p s s' hy1 hy2 ->
          (get_r_pre (rcl p)) s -> (get_r_post (rcl p)) s' s.

(** Facts about tr **)

Lemma tr_relational_prop (rcl:R_Phi.r_phi) (ps: Psi.psi):
(forall p, 0 < length p -> 
     relational_prop (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_call p) ps)
          -> tr rcl.
Proof.
intros H p s s' hy1 hy2 hy Hcall Hrp.
  apply H.
  + apply hy.
  + rewrite fold_call_length.
    symmetry. assumption.
  + rewrite fold_call_length.
    symmetry. assumption.
  + assumption.
  + eapply rceval_proc_to_prod in Hcall. 
    apply Hcall.
Qed.

(**  **)

Definition phi_call (cl : Phi.phi) := 
    fun x => (get_pre (cl x), (fun m' m => (get_post (cl x)) m' m /\ proc_call x m m')).

Lemma phi_call_hoare (ps: Psi.psi) (cl : Phi.phi) :
  (forall p, hoare_triple (get_pre (cl p)) (get_post (cl p)) (CCall p) ps) ->
  (forall p, hoare_triple (get_pre (phi_call cl p)) (get_post (phi_call  cl p)) (CCall p) ps).
Proof.
intros.
intros s s' Hpre Heval.
split.
* generalize p, s, s', Hpre, Heval.
  apply H.
* eapply test. apply Heval.
Qed.
