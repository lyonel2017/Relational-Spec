From Rela Require Import Vcg.
From Rela Require Import Com.
From Rela Require Import Bexp.
From Rela Require Import Sigma.
From Rela Require Import Hoare_Triple.

Require Import Program.
Require Import Eqdep_dec.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.

(** Definition of assertion **)

Definition r_assertion : Type := list sigma  -> Prop.

Inductive rceval : list com -> list sigma -> Psi.psi -> list sigma -> Prop :=
  | E_Empty : forall ps,
      rceval [] [] ps []
 | E_Seq : forall c qc s q s' q' ps,
      ceval c s ps s' ->
      rceval qc q ps q' ->
      rceval (c::qc) (s::q) ps (s'::q').

Definition relational_prop (P Q: r_assertion) (c : list com) (ps : Psi.psi) : Prop := 
 forall s s',  length s = length c -> length s' = length c ->
               P s -> rceval c s ps s' -> Q s'.

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

Program Fixpoint rtc (cl : list com) (ml: list Sigma.sigma)
            (ps: Phi.phi) (suite : list Sigma .sigma -> Prop) 
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

Lemma correct :
forall ps pi,
forall p (P Q: r_assertion),
(forall ml (hy:length p = length ml), 
P ml -> rtc p ml pi Q hy) -> 
relational_prop P Q p ps.
Proof.
intros ps pi p.
unfold relational_prop.
induction p.
*  intros.
   specialize (H []).
   simpl in H.
   apply length_zero_iff_nil in H0.
   apply length_zero_iff_nil in H1.
   subst.
   apply H.
   reflexivity.
   assumption.
*  intros.
   destruct s.
   + discriminate H0.
   + destruct s'.
   - discriminate H1.
   - inversion H3;subst.
    specialize (IHp (fun sl => P (s :: sl)) (fun sl => Q (s1 :: sl))).
    simpl in IHp.
    generalize H12.
    generalize H2.
    inversion H0.
    inversion H1.
    generalize H6.
    generalize H5.
    eapply IHp.
    intros.
    generalize H9.
    generalize H4.
    generalize s s1.
    rewrite hoare_rela.
    eapply (correct _ _ pi).
    intros.
    assert (hy2: length (a ::p) = length (m::ml)).
    {intros. simpl. rewrite hy. reflexivity. }
    destruct (mk_rtc_def Q a p pi m ml hy2) as (hyr & HYP).
    specialize (H (m::ml) hy2).
    rewrite HYP in H.
    replace hy with hyr.
    apply H.
    assumption.
    apply eq_proofs_unicity.
    intros.
    lia.
Qed.