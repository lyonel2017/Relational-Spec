From Coq Require Import PeanoNat.
From Rela Require Import Aexp.
From Rela Require Import Bexp.
From Rela Require Import ECom.
From Rela Require Import Proc.
From Rela Require Import Label.
From Rela Require Import Lambda.
From Rela Require Import Sigma.
From Rela Require Import Loc.

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

From Coq Require Import Lia.

Definition set: (Loc.t -> nat) -> Loc.t -> nat -> Loc.t -> nat.
Proof.
intros m x y.
intros x'.
destruct (Loc.eq_dec x x') as [H|H].
exact y.
exact (m x').
Defined.

Lemma set'def:
  forall (f: Loc.t -> nat ) (x: Loc.t) (v:nat) (y: Loc.t),
  ((y = x) -> ((set f x v y) = v)) /\ (~ (y = x) -> ((set f x v y) = (f y))).
Proof.
intros f x v y.
split.
+ intros.
 unfold set.
 destruct (Loc.eq_dec x y).
  * reflexivity.
  * contradiction n.
    rewrite H. reflexivity.
+ intros. 
  unfold set.
 destruct (Loc.eq_dec x y).
  * contradiction H.
    rewrite e. reflexivity.
  * reflexivity.
Qed.

(** Definition of Precondtion **)

Definition precondition : Type := sigma -> Prop.

Definition empty_precondition : precondition := (fun _ => True).

(** Defintion of Postcondtion **)

Definition postcondition : Type := sigma -> sigma -> Prop.

Definition empty_postcondition :  postcondition := (fun _ _ => True).

(** Definition of a contract **)

Definition clause : Type := precondition * postcondition.

Definition empty_clause : clause := (empty_precondition, empty_postcondition). 

Module Phi.

  (** The programs that can be called is a maps from procedure to program **)

  Definition phi : Type := Proc.t -> clause.

  Definition update_psi (x:Proc.t) (v: clause) (l:phi): phi :=
  fun (x': Label.t) => if Proc.eqb x' x then v else l x'.

  Notation "x '#->' v ; l" := (update_psi x v l)(at level 100, v at next level, right associativity).

  Definition get_pre (an:clause) := 
          let (pre,post) := an in
          pre.

  Definition get_post (an:clause) := 
          let (pre,post) := an in
          post.

End Phi.

Inductive branch (A B C : Prop) : Prop :=  
  | Then : A -> B -> branch A B C
  | Else : ~ A -> C -> branch A B C.

Fixpoint tc (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (ps: Phi.phi) (suite : Prop) : Prop :=
    match c with
    | CSkip => m = m' -> suite
    | CAss x a => (m' = set m x (aeval m a)) -> suite
    | CAssert b => b m s -> m = m' -> suite
    | CIf b p1 p2 =>
         forall m1, tp p1 (l |-> m1; s) m1 ps (fun m1' _ => 
             forall m2, tp p2 (l |-> m2;s) m2 ps (fun m2' _ => 
               (branch (beval m b = true) (m' = m1' /\ m = m1) (m' = m2' /\ m = m2) -> suite) 
            )
         )
    | CWhile b p inv _ => inv m (l |->m; s) -> inv m' (l |->m; s) -> beval m b = false -> suite 
    end
 with tp (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)  (ps: Phi.phi)
            (fin: Sigma.sigma -> Lambda.lambda -> Prop)  : Prop :=
  match p with
  | pnil => fin m s
  | pconst l c p' => forall m', tc c l s m m' ps (tp p' (l |-> m; s) m' ps fin)
end.

Definition empty_phi: Phi.phi := fun _ => empty_clause.

Lemma test1 : forall s m,  m EAX = 1 -> tp plus2 s m empty_phi (fun m' s' => m' EAX = 3) .
Proof.
simpl.
intros.
Abort.

Definition plus3 : prog := pconst l1 (CAss EAX (APlus (AId EAX) (ANum 2)))
                          (pconst l2 (CAss EAX (APlus (AId EAX) (ANum 2))) pnil).

Lemma test2 : forall s m, m EAX = 1 -> tp plus3 s m empty_phi (fun m' s' => m' EAX = 5).
Proof.
  simpl.
  intros.
Abort.

Definition if2 : prog := pconst l1 (CIf (BEq (AId EAX) (ANum 4)) plus2 plus2 ) pnil.

Lemma test3 : forall s m, m EAX = 1 -> tp if2 s m empty_phi ( fun m' s' => m' EAX = 3).
Proof.
  simpl.
  intros.
Abort.

Definition if3 : prog := pconst l1 (CAss EAX (APlus (AId EAX) (ANum 2)))
                         (pconst l1 (CIf (BEq (AId EAX) (ANum 4)) plus2 plus2) plus2).

Lemma test4 : forall s m, m EAX = 1 -> tp if3 s m empty_phi ( fun m' s' => m' EAX = 3).
Proof.
  simpl.
  intros.
Abort.

Lemma test5 : forall s m1 m2, m1 EAX = m2 EAX -> 
                              tp plus2 s m1 empty_phi ( fun m1' _ => 
                              tp plus2 s m2 empty_phi ( fun m2' _ =>
                                     m1' EAX = m2' EAX)).
Proof.
  simpl.
  intros.
Abort.

Fixpoint tc' (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (ps: Phi.phi) (suite : Prop) : Prop :=
    match c with
    | CSkip => tc c l s m m' ps suite
    | CAss x a => tc c l s m m' ps suite
    | CAssert b => b m s /\ tc c l s m m' ps suite
    | CIf b p1 p2 => 
         (beval m b = true -> tp' p1 (l |->m; s) m ps) /\
         (beval m b = false -> tp' p2 (l |->m; s) m ps) /\
          tc c l s m m' ps suite
    | CWhile b p inv _ => 
      (beval m b = true -> inv m (l |->m; s)) /\ 
      (beval m b = true -> forall mi, inv mi (l |->m; s) -> 
                           tp p (l |->m; s) m ps (fun sf mf => inv sf mf)) /\ 
      (beval m b = true -> forall mi, inv mi (l |->m; s) -> tp' p (l |->m; s) m ps) /\ 
      tc c l s m m' ps suite
    end
 with tp' (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)  (ps: Phi.phi) : Prop :=
  match p with
  | pnil => True
  | pconst l c p' => forall m', tc' c l s m m' ps (tp' p' (l |-> m; s) m' ps)
end.

Definition truc3 : prog := pconst l1 (CAssert (fun m _ => m EAX = 2))
                          (pconst l2 (CAssert (fun m _ => m EAX = 2)) pnil).
                          
Lemma test4 : forall s m, (m EAX = 2) -> tp' truc3 s m  empty_phi .
Proof.
intros.
simpl.
intros.
split. 
  * assumption.
  * intros. split.
    - rewrite <- H1. assumption.
    - intros. auto. 
Qed.

Definition if4 : prog := pconst l1 (CIf (BEq (AId EAX) (ANum 2)) (pconst l1 (CAssert (fun m _ => m EAX = 2)) pnil) pnil) pnil.

Lemma test5 : forall s m, (m EAX = 2) -> tp' if4 s m  empty_phi .
Proof.
intros.
simpl.
intros.
split. 
  * intros. split. all: try auto.
  * split.
    - auto.
    - intros. auto. 
Qed.
 
(*Fixpoint tc' (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (suite : Prop -> Prop-> Prop) (fin : Prop) (vc : Prop)
            (ps: Phi.phi): Prop :=
    match c with
    | CSkip => suite vc (m = m')
    | CAss x a => suite vc (m' = set m x (aeval m a))
    | CAssert b => suite (vc /\ (fin -> b m s)) (m = m' /\ b m s)
    | _ => suite vc (True)
    end
 with tp' (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)
            (fin: Prop) (vc :Prop)
            (ps: Phi.phi) : Prop :=
  match p with
  | pnil => vc
  | pconst l c p' => 
       forall m', tc' c l s m m' (fun (vcs : Prop) (vc : Prop) => 
                     tp' p' (l |-> m; s) m' (vc -> fin) vcs ps ) fin vc ps
end.*)



(**************************************************************)
(*                      TRASH                                 *)
(**************************************************************)


(*

Fixpoint tc (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (ps: Phi.phi) (suite : Prop -> Prop) : Prop :=
    match c with
    | CSkip => suite (m = m')
    | CAss x a => suite (m' = set m x (aeval m a))
    | CAssert b => suite (m = m' /\ b m s)
    | CIf b p1 p2 =>
         tp p1 s m ps (fun m1 _ => 
             tp p2 s m ps (fun m2 _ => 
               suite (branch (beval m b = true) (m' = m1) (m' = m2)) 
            )
         )
    | _ => suite (True)
    end
 with tp (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)  (ps: Phi.phi)
            (fin: Sigma.sigma -> Lambda.lambda -> Prop)  : Prop :=
  match p with
  | pnil => fin m s
  | pconst l c p' => 
       forall m', tc c l s m m' ps (fun (vc : Prop)  => 
                      tp p' (l |-> m; s) m' ps (fun mf sf => vc -> fin mf sf)
                  )
end.

*)



(*Definition vc_f (ps: Psi.psi): Prop :=
forall (f :Proc.t) la m m', 
  (Psi.get_pre (Psi.get_an ps f)) (Pre |-> m ; la ) -> 
  tp (Psi.get_proc f ps) la m (fun m _ => m = m') ps -> 
  (Psi.get_post (Psi.get_an f ps)) (Post |-> m' ; (Pre |-> m ; la )).*)




(*

Fixpoint tc (c : com) (l: Label.t) (s : Lambda.lambda) (m m' : Sigma.sigma)
            (ps: Phi.phi): Prop :=
    match c with
    | CSkip => m = m'
    | CAss x a => m' = (set m x (aeval m a))
    | CAssert b => b m s /\ m = m'
    | _ => False
    end
  with tp (p : prog) (s : Lambda.lambda) (m: Sigma.sigma)
            (fin: Sigma.sigma -> Lambda.lambda -> Prop)
            (ps: Phi.phi) : Prop :=
  match p with
  | pnil => fin m s
  | pconst l c p' => 
    forall m' : Sigma.sigma, 
        tp p' (l |-> m; s) m' (fun mf sf => tc c l s m m' ps -> fin mf sf) ps 
end.

Lemma correct :
forall p ps pi m la m' la' i,
well_p p ->
tp p la m (fun m la => m = m' /\ la = la') pi ->
ceval_step_prog m la ps p i = Some(m', la') \/ 
ceval_step_prog m la ps p i = None.
Proof.
intros p ps pi m la m' la' i Well.
generalize dependent m.
generalize dependent la.
generalize dependent m'.
generalize dependent la'.
generalize dependent Well.
elim p using prog_com_ind with 
  (P :=  fun c : com =>
   well_c c ->
   forall m m' la l,
      tc c l la m m' pi ->
      ceval_step_com m l la ps c i  = Some (m', (l |-> m ; la )) \/
      ceval_step_com m l la ps c i  = None).
    * intros. destruct (ceval_step_com m l la ps CSkip i) eqn:Heqr.
      - left. destruct p0.
        destruct i.
        + discriminate Heqr.
        + simpl in H0. simpl in Heqr. inversion Heqr;subst. reflexivity.
      - right. reflexivity.
    * intros. contradiction H.
    * intros. contradiction H.
    * intros. contradiction H1.
    * intros. contradiction H0.
    * intros. destruct (ceval_step_prog m la ps pnil i) eqn:Heqr.
      - left. destruct p0.
        destruct i.
        + discriminate Heqr.
        + simpl in H. simpl in Heqr. destruct H. inversion Heqr;subst. reflexivity.
      - right. reflexivity. 
    * intros.
      destruct (ceval_step_prog m la ps (pconst t c p0) i) eqn: Heqr1.
        - left. destruct p1.
          destruct i.
          + discriminate Heqr1.
          + simpl in Heqr1.
          destruct (ceval_step_com m t la ps c i) eqn: Heqr2.
            ** destruct i.
              -- discriminate Heqr2.
              -- destruct p1.
                 simpl in H1.
                 specialize (H1 s0).
                 destruct H1.
                 apply H0 in H2. destruct H2.
                 apply H in H1. destruct H1.
                 apply (ceval_step_more (S i) ( S (S i))) in Heqr1.
                 rewrite H2 in Heqr1.
                 inversion Heqr1;subst.
                 reflexivity.
                 lia.
                 simpl in Well.

Qed.*)

(*define function for proving assertion and invariant: generate sub program by visiting program*)