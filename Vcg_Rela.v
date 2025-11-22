From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Sem.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.
From Rela Require Import Rela.

From Stdlib Require Import Lists.List.
Import ListNotations.

(** Definition of the verification condition generator for relational properties,
    using the verification condition generator for Hoare Triples **)

Definition r_suite : Type := list Sigma.sigma -> list history -> Prop.

Fixpoint rtc
  (cl : list com) (ml: list Sigma.sigma) (hl: list history)
  (cls: Phi.phi) (suite : r_suite): Prop :=
  match cl,ml,hl with
  | [],[],[] => suite [] []
  | c :: qc, m :: qm, h :: qh =>
      tc c m h cls (fun m' h' => rtc qc qm qh cls (fun lm lh => suite (m'::lm) (h' :: lh)))
 | _,_,_ => False
end.

(** Connect between Hoare Triple and Relational Properties **)

Lemma hoare_rela :
  forall (P: r_precondition) (Q: r_postcondition)
    h q ps cll sl hl,
    (forall s2 s3 : sigma,
        P (s2 :: sl) -> ceval h s2 ps s3 ->
        rtc q sl hl cll (fun sl' _ => Q (s3 :: sl') (s2 :: sl))) =
      hoare_triple (fun s => P (s:: sl) )
        (fun s' s => rtc q sl hl cll (fun sl' _ => Q (s' :: sl') (s :: sl)))
        h ps.
Proof.
intros.
unfold hoare_triple.
reflexivity.
Qed.

(** Defintion of the generator of auxiliare goals for relational properties **)

Fixpoint rtc'
  (cl : list com)
  (ml: list Sigma.sigma)
  (hl: list history)
  (cls : Phi.phi): Prop :=
  match cl,ml,hl with
  | [],[],[] => True
  | c :: qc, m :: qm, h :: qh =>
      tc' c m h cls /\ rtc' qc qm qh cls
  | _,_,_ => False
  end.

(** Translation of a list of procedure call to Prop **)

Definition proc_call f s s' ps := ceval (CCall f) s ps s'.

Fixpoint proc_to_pred p s s' ps : Prop:=
  match p, s, s' with
  | [] , [], [] => True
  | h :: q, s:: qs, s' :: qs' =>
      proc_call h s s' ps /\ proc_to_pred q qs qs' ps
  | _, _, _ => False
  end.

Lemma rceval_proc_to_prod  p s s' ps :
  proc_to_pred p s s' ps  -> rceval (fold_call p) s ps s' .
Proof.
generalize dependent s'.
generalize dependent s.
generalize dependent ps.
induction p; intros.
- destruct s ;[|contradiction H].
  destruct s';[|contradiction H].
  apply E_Empty.
- destruct s ;[contradiction H|].
  destruct s';[contradiction H|].
  simpl.
  apply E_Seq.
  + apply H.
  + apply IHp. apply H.
Qed.

(** Translation of a relational contract into Prop **)

Definition tr (rcl:R_Phi.phi) ps :=
  forall p s s',
    0 < length p ->
    proc_to_pred p s s' ps ->
    (get_r_pre (rcl p)) s -> (get_r_post (rcl p)) s' s.

(** Facts about tr **)

Lemma tr_relational_prop (rcl:R_Phi.phi) (ps: Psi.psi):
(forall p, 0 < length p ->
     relational_prop (get_r_pre (rcl p)) (get_r_post (rcl p)) (fold_call p) ps)
          -> tr rcl ps.
Proof.
  intros H p s s' Hp Hcall HPre.
  apply H.
  - assumption.
  - rewrite fold_call_length.
    revert Hcall.
    clear.
    revert s. revert s'.
    induction p;intros.
    + destruct s;[reflexivity| contradiction Hcall].
    + destruct s;[contradiction Hcall|].
      simpl. f_equal.
      destruct s';[contradiction Hcall|].
      eapply IHp.
      apply Hcall.
  - rewrite fold_call_length.
    revert Hcall.
    clear.
    revert s. revert s'.
    induction p;intros.
    + destruct s;[|contradiction Hcall].
      destruct s';[reflexivity|contradiction Hcall].
    + destruct s;[contradiction Hcall|].
      destruct s';[contradiction Hcall|].
      simpl. f_equal.
      eapply IHp.
      apply Hcall.
  - assumption.
  - eapply rceval_proc_to_prod in Hcall.
    apply Hcall.
Qed.

(** Adding proc_call to post condition of procedure contract **)

Definition phi_call (cl : Phi.phi) ps :=
  fun x => (get_pre (cl x),
          (fun m' m => (get_post (cl x)) m' m /\ proc_call x m m' ps)).

(* Facts about phi_call *)

Lemma phi_call_hoare (ps: Psi.psi) (cl : Phi.phi) :
  (forall p, hoare_triple (get_pre (cl p)) (get_post (cl p)) (CCall p) ps) ->
  (forall p, hoare_triple
          (get_pre (phi_call cl ps p))
          (get_post (phi_call cl ps p))
          (CCall p) ps).
Proof.
intros.
intros s s' Hpre Heval.
split.
* generalize p, s, s', Hpre, Heval.
  apply H.
* apply Heval.
Qed.

(** Extract standard procedure contract from relational procedure contract **)

Definition extract rcl := fun y:Proc.Proc.t =>
  (fun m => get_r_pre (rcl [y]) [m], fun m' m =>  get_r_post (rcl [y]) [m'] [m]).

(* Facts about Extract *)

Lemma hd_length_1 s: length s = 1 -> [hd default_sigma s] = s.
Proof.
intros.
destruct s.
* discriminate H.
* inversion H.
  rewrite length_zero_iff_nil in H1.
  subst.
  simpl.
  reflexivity.
Qed.

Lemma rela_hoare_extract rcl ps:
  (forall p : list Proc.Proc.t,
      0 < length p ->
      relational_prop
        (get_r_pre (rcl p))
        (get_r_post (rcl p))
        (fold_call p) ps) ->
  (forall p, hoare_triple
          (get_pre ((extract rcl) p))
          (get_post ((extract rcl) p)) (CCall p) ps).
Proof.
  intros.
  assert (H1 : 0 < 1); auto.
  specialize (H [p] H1). simpl in H.
  apply Single_Rela_Prop.one_rela_is_hoare.
  simpl.
  intros s s' hy1 hy2 Hpre Heval.
  inversion hy1.
  inversion hy2.
  rewrite hd_length_1 by apply H3.
  rewrite hd_length_1 by apply H2.
  apply H. all: try assumption.
  rewrite hd_length_1 in Hpre by apply H2.
  assumption.
Qed.

(** Definition of a relational verification condition generator for procedures **)

Definition rtc_p (ps: Psi.psi) (rcl : R_Phi.phi) : Prop :=
    forall f m ps',
    let c := fold_proc ps f in
    let h := (map (fun _ => empty_history) f) in
    let cl := phi_call (extract rcl) ps' in
    (get_r_pre (rcl f)) m -> tr rcl ps' ->
    rtc' c m h cl /\  rtc c m h cl (fun m' _ => (get_r_post (rcl f)) m' m).

Lemma get_r_pre_emphi_false m f :
  get_r_pre (R_Phi.empty_phi f) m -> False.
Proof.
  simpl.
  unfold empty_r_precondition.
  auto.
Qed.

Lemma rtc_p_empty_psi : rtc_p Psi.empty_psi R_Phi.empty_phi.
Proof.
  unfold rtc_p.
  intros.
  apply get_r_pre_emphi_false in H.
  contradiction H.
Qed.
