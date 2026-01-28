From Coq Require Import
     Program.Basics
     Program.Tactics
     Program.Equality
     Logic.FunctionalExtensionality
     Relations
     Sets.Ensembles
     Vectors.Fin
     QArith.QArith
     QArith.Qreals.

Set Universe Polymorphism.
Generalizable All Variables.

Record CSet (A : Type) := {
  inner  : Ensemble A ;
  outer  : Ensemble A ;
  disjoint : forall x, inner x -> ~ outer x
}.

Arguments inner {_} _.
Arguments outer {_} _.
Arguments disjoint {_} _.
Arguments Included {_} _.

Definition CSet_subset {A} (s t : CSet A) : Prop :=
  Included (inner s) (inner t) /\ Included (outer t) (outer s).

Lemma CSet_subset_trans {A} (s t u : CSet A) :
  CSet_subset s t -> CSet_subset t u -> CSet_subset s u.
Proof.
  intros [h1 h2] [h3 h4].
  split; intros x hx; auto.
Qed.

Definition CSet_union {A} (s t : CSet A) : CSet A.
Proof.
  refine {|
    inner := fun x => (outer s x -> inner t x) /\ (outer t x -> inner s x) ;
    outer := fun x => outer s x /\ outer t x
  |}.
  intros x [h1 h2] [hs ht].
  eapply (disjoint t x); [ apply h1; exact hs | exact ht ].
Defined.

Lemma CSet_union_outer_eq {A} (s t : CSet A) :
  forall x, outer (CSet_union s t) x <-> (outer s x /\ outer t x).
Proof. firstorder. Qed.

Lemma CSet_union_mono {A} {s t u v : CSet A} :
  CSet_subset s t -> CSet_subset u v -> CSet_subset (CSet_union s u) (CSet_union t v).
Proof.
  intros [st1 st2] [uv1 uv2]; split.
  - intros x [h1 h2]; split.
    + intros a. apply uv1, h1, st2, a.
    + intros a. apply st1, h2, uv2, a.
  - intros x [h1 h2]; split; [apply st2|apply uv2]; assumption.
Qed.

Definition CSet_empty {A} : CSet A.
Proof.
  refine {| inner := (fun _ => False); outer := (fun _ => True) |}.
  intros x h _; exact h.
Defined.

Lemma CSet_empty_subset {A} (s : CSet A) : CSet_subset CSet_empty s.
Proof. split; firstorder. Qed.


Definition fin_snoc {n A} (f : Fin.t n -> A) (a : A) : Fin.t (S n) -> A :=
  fun p => Fin.caseS' p (fun _ => A) a f.

Lemma fin_snoc_castSucc {n A} (f : Fin.t n -> A) (a : A) (i : Fin.t n) :
  fin_snoc f a (Fin.FS i) = f i.
Proof. reflexivity. Qed.

Lemma fin_snoc_last {n A} (f : Fin.t n -> A) (a : A) :
  fin_snoc f a (Fin.F1) = a.
Proof. reflexivity. Qed.

Fixpoint CSet_FinUnion {A} {n : nat} (s : Fin.t n -> CSet A) : CSet A :=
  match n as m return (Fin.t m -> CSet A) -> CSet A with
  | O =>
      fun _ => CSet_empty
  | S n' =>
      fun s =>
        CSet_union
          (CSet_FinUnion (fun i => s (Fin.FS i)))
          (s Fin.F1)
  end s.

Lemma CSet_FinUnion_outer_iff {A} :
  forall n (s : Fin.t n -> CSet A) x,
    outer (CSet_FinUnion s) x <-> (forall i, outer (s i) x).
Proof.
  induction n as [|n IH]; intros s x.
  - simpl. split; intro H; [|tauto]. intro H2. exact (Fin.case0 (fun _ => _) H2).
  - simpl.
    rewrite <- CSet_union_outer_eq.
    split.
    + intros [Hx1 Hx2] i.
      exact (Fin.caseS' i (fun i => outer (s i) x) Hx2 (fun j => proj1 (IH _ x) Hx1 j)).
    + intros Hall. split.
      * apply (IH _ _). intros i. exact (Hall (Fin.FS i)).
      * exact (Hall Fin.F1).
Qed.

Definition CSet_antiSubset {A} (s t : CSet A) : Prop :=
  exists x, inner s x /\ outer t x.

Lemma CSet_antiSubset_mono_left {A} {s t u : CSet A} :
  CSet_antiSubset s u -> CSet_subset s t -> CSet_antiSubset t u.
Proof.
  intros [x [hx1 hx2]] [h1 _]. exists x; split; [apply h1; exact hx1|exact hx2].
Qed.

Lemma CSet_antiSubset_union_mono {A} {s t u : CSet A} :
  CSet_antiSubset (CSet_union s u) (CSet_union t u) -> CSet_antiSubset s t.
Proof.
  intros [x [[h11 h12] [h21 h22]]].
  exists x. split; [| exact h21].
  apply h12. exact h22.
Qed.

Lemma CSet_subset_not_antiSubset {A} {s t : CSet A} :
  CSet_subset s t -> ~ CSet_antiSubset s t.
Proof.
  intros [h1 h2] [x [hx hy]].
  apply (disjoint s x).
  - exact hx.
  - apply h2. exact hy.
Qed.

Module Cuts.
Record t := {
  L : Q -> Prop ;
  U : Q -> Prop ;
  lower : forall x, L x -> forall y, Qle y x -> L y ;
  upper : forall x, U x -> forall y, Qle x y -> U y ;
  open_L : forall x, L x -> exists y, L y /\ Qlt x y ;
  open_U : forall x, U x -> exists y, U y /\ y < x ;
  L_lt_U : forall x, L x -> forall y, U y -> Qlt x y
}.

Definition le_q (x : t) (q : Q) : Prop :=
  forall y, Qlt q y -> U x y.

Definition ge_q (x : t) (q : Q) : Prop :=
  forall y, Qlt y q -> L x y.

Lemma not_gt_of_le_q (x : t) (q : Q) :
  le_q x q -> ~ L x q.
Proof.
  intros hle hL.
  destruct (open_L x q hL) as [y [HyL Hylt]].
  specialize (hle y Hylt). 
  pose proof (L_lt_U x y HyL y hle) as contra.
  now apply (Qlt_irrefl y).
Qed.

Lemma not_lt_of_ge_q (x : t) (q : Q) :
  ge_q x q -> ~ U x q.
Proof.
  intros hge hU.
  destruct (open_U x q hU) as [y [HyU Hylt]].
  specialize (hge y Hylt).
  pose proof (L_lt_U x y hge y HyU) as contra.
  now apply (Qlt_irrefl y).
Qed.

Lemma le_q_of_lt {x : t} {q : Q} (h : U x q) : le_q x q.
Proof.
  intros y hy. eapply upper; eauto. apply Qlt_le_weak, hy.
Qed.

Lemma ge_q_of_gt {x : t} {q : Q} (h : L x q) : ge_q x q.
Proof.
  intros y hy. eapply lower; eauto. apply Qlt_le_weak, hy.
Qed.

Lemma le_q_mono {x : t} {q r : Q} :
  le_q x q -> Qle q r -> le_q x r.
Proof.
  intros hq qr y hyr. apply hq. eapply Qle_lt_trans.
  - exact qr.
  - exact hyr.
Qed.

Lemma ge_q_mono {x : t} {q r : Q} :
  ge_q x q -> Qle r q -> ge_q x r.
Proof.
  intros hq qr y hyr. apply hq. eapply Qlt_le_trans.
  - exact hyr.
  - exact qr.
Qed.

End Cuts.

Notation Cuts := Cuts.t.

Definition Icc (a b : Q) : CSet Cuts.
Proof.
  refine {|
    inner := fun r => Cuts.ge_q r a /\ Cuts.le_q r b ;
    outer := fun r => (Cuts.ge_q r a -> Cuts.L r b) /\ (Cuts.le_q r b -> Cuts.U r a)
  |}.
  intros r [Hga Hlb] [H1 H2].
  eapply Cuts.not_gt_of_le_q.
  - exact Hlb.
  - apply H1; exact Hga.
Defined.

Definition Ioo (a b : Q) : CSet Cuts.
Proof.
  refine {|
    inner := fun r => Cuts.L r a /\ Cuts.U r b ;
    outer := fun r => (Cuts.L r a -> Cuts.ge_q r b) /\ (Cuts.U r b -> Cuts.le_q r a)
  |}.
  intros r [HLa HUb] [H1 H2].
  eapply Cuts.not_gt_of_le_q.
  - apply H2, HUb.
  - exact HLa.
Defined.

Lemma Icc_mono_right (a b c : Q) (h : Qle b c) :
  CSet_subset (Icc a b) (Icc a c).
Proof.
  split.
  - intros r [Hga Hlb]. split; [assumption|].
    intros y hy. apply Hlb. eapply Qle_lt_trans; [exact h|exact hy].
  - intros r [Hga Hlb]. split.
    + intros H. eapply Cuts.lower; [exact (Hga H)| exact h].
    + intros H. apply Hlb. eapply Cuts.le_q_mono; [apply H|assumption].
Qed.

Lemma Icc_mono_left (a b c : Q) (h : Qle c a) :
  CSet_subset (Icc a b) (Icc c b).
Proof.
  split.
  - intros r [Hga Hlb]. split; [|assumption].
    intros y hy. apply Hga. eapply Qlt_le_trans; [exact hy|exact h].
  - intros r [Hga Hlb]. split.
    + intros H. apply Hga. eapply Cuts.ge_q_mono; [apply H|assumption].
    + intros H. eapply Cuts.upper; [exact (Hlb H)| exact h].
Qed.

Lemma Icc_sub_Ioo (a b c d : Q) (hac : Qlt c a) (hbd : Qlt b d) :
  CSet_subset (Icc a b) (Ioo c d).
Proof.
  split.
  - intros r [Hga Hlb]. split.
    + apply Hga. exact hac.
    + apply Hlb. exact hbd.
  - intros r [H1 H2]. split.
    + intros H.
      apply (H1 (H c hac)).
      exact hbd.
    + intros H.
      apply (H2 (H d hbd)).
      exact hac.
Qed.
Lemma Icc_sub_Icc_union (a b c : Q) :
  CSet_subset (Icc a c) (CSet_union (Icc a b) (Icc b c)).
Proof.
  split.
  - intros r [Hga Hlc]. split.
    + intros [Hgb Hlb]. split; [apply Cuts.ge_q_of_gt, (Hgb Hga)| exact Hlc].
    + intros [Hgb Hlb]. split; [exact Hga| apply Cuts.le_q_of_lt, (Hlb Hlc)].
  - intros r [[H1 H2] [H3 H4]]. split.
    + intros H. apply H3. apply Cuts.ge_q_of_gt. apply H1. exact H.
    + intros H. apply H2. apply Cuts.le_q_of_lt. apply H4. exact H.
Qed.

Lemma Icc_empty {a b : Q} (hab : a > b) :
  CSet_subset (Icc a b) (CSet_empty).
Proof.
  split.
  - intros r [Hga Hlb]. exfalso.
    eapply Cuts.not_gt_of_le_q; [exact Hlb| exact (Hga b hab)].
  - intros r _. split; intros H; [ now specialize (H b hab) | now specialize (H a hab) ].
Qed.

Definition Covered (s : CSet Cuts) (n : nat)
           (qs rs : Fin.t n -> Q) : Prop :=
  CSet_subset s (CSet_FinUnion (fun i => Ioo (qs i) (rs i))).

Lemma Covered_mono {s t : CSet Cuts} {n} {qs rs} :
  Covered s n qs rs -> CSet_subset t s -> Covered t n qs rs.
Proof. intros H1 H2. eapply CSet_subset_trans; eauto. Qed.

Lemma Covered_snoc {s t: CSet Cuts} {n} {qs rs} (hs : Covered s n qs rs)
      (qn rn : Q) (ht : CSet_subset t (Ioo qn rn)) :
  Covered (CSet_union s t) (S n) (fin_snoc qs qn) (fin_snoc rs rn).
Proof.
  unfold Covered in *.
  simpl. 
  eapply CSet_union_mono.
  - change (CSet_subset s (CSet_FinUnion (fun i : Fin.t n => Ioo (qs i) (rs i)))) in hs.
    refine (CSet_subset_trans _ _ _ hs _).
    split; [intros x hx; exact hx | firstorder].
  - change (CSet_subset t (Ioo (fin_snoc qs qn Fin.F1) (fin_snoc rs rn Fin.F1))).
    now rewrite !fin_snoc_last.
Qed.

Definition UnCovered (s : CSet Cuts) (n : nat)
           (qs rs : Fin.t n -> Q) : Prop :=
  CSet_antiSubset s (CSet_FinUnion (fun i => Ioo (qs i) (rs i))).

Lemma UnCovered_mono {s t : CSet Cuts} {n} {qs rs} :
  UnCovered s n qs rs -> CSet_subset s t -> UnCovered t n qs rs.
Proof. intros H1 H2. now eapply CSet_antiSubset_mono_left; [exact H1|exact H2].
Qed.

Lemma UnCovered_snoc {s : CSet Cuts} {n} {qs rs} (qn rn : Q)
      (hs : UnCovered (CSet_union s (Ioo qn rn)) (S n) (fin_snoc qs qn) (fin_snoc rs rn)) :
  UnCovered s n qs rs.
Proof.
  unfold UnCovered in *.
  eapply CSet_antiSubset_union_mono; eauto.
Qed.

Lemma Covered_not_UnCovered {s : CSet Cuts} {n} {qs rs} :
  Covered s n qs rs -> ~ UnCovered s n qs rs.
Proof. intros H. eapply CSet_subset_not_antiSubset, H. Qed.

Definition middleRat (x y : Q) : Q := ((x + y) / 2)%Q.

Lemma Qplus_diag {q : Q}: q+q == 2 * q.
Proof.
  unfold Qeq.
  simpl.
  ring_simplify.
  simpl.
  replace (Z.pow_pos (QDen q) 2) with (Z.pos (Qden q * Qden q)).
  - reflexivity.
  - apply (eq_trans (Pos2Z.inj_mul (Qden q) (Qden q))).
    apply eq_sym.
    apply (eq_trans (Z.pow_pos_fold (QDen q) 2)).
    ring.
Qed.

Lemma middleRat_lt_right_of_lt {x y : Q} :
  x < y -> middleRat x y < y.
Proof.
  intros Hxy. unfold middleRat.
  apply (Qmult_lt_l _ _  2).
  - compute.
    reflexivity.
  - setoid_replace ((2*((x+y)/2))) with (x+y) by now apply Qmult_div_r; discriminate.
    setoid_replace ((2*y)) with (y+y) by now apply (Qeq_sym _ _ Qplus_diag).
    apply Qplus_lt_le_compat; [exact Hxy|apply Qle_refl].
Qed.

Lemma left_lt_middleRat_of_lt {x y : Q} :
  x < y -> x < middleRat x y.
Proof.
  intros Hxy. unfold middleRat.
  apply (Qmult_lt_l _ _  2).
  - compute.
    reflexivity.
  - setoid_replace ((2*x)) with (x+x) by now apply (Qeq_sym _ _ Qplus_diag).
    setoid_replace (2*((x+y)/2)) with (x+y) by now apply Qmult_div_r; discriminate.
    setoid_replace (x+y) with (y+x) by apply Qplus_comm.
    apply Qplus_lt_le_compat; [exact Hxy|apply Qle_refl].
Qed.

Module ELR.
Record t := {
  L : Q -> Prop ;
  lower : forall x, L x -> forall y, Qle y x -> L y ;
  open_L : forall x, L x -> exists y, L y /\ Qlt x y ;
}.

Definition ge_q (x : t) (q : Q) : Prop :=
  forall y, Qlt y q -> L x y.

Definition Icc_outer (q r : Q) (x : t) : Prop :=
  ge_q x q -> L x r.

Definition Ioo_outer (q r : Q) (x : t) : Prop :=
  L x q -> ge_q x r.

End ELR.

Notation ELR := ELR.t.

Program Definition MaxCoveredEndELR (a : Q) (ι : Type)
        (qs rs : ι -> Q) : ELR :=
  {|
    ELR.L := fun q => exists q', q < q' /\ exists (n : nat) (is : Fin.t n -> ι),
                Covered (Icc a q') n (fun i => qs (is i)) (fun i => rs (is i))
  |}.
Next Obligation.
  exists H; split; [eapply Qle_lt_trans; eauto|].
  exists H2, H3.
  exact H4.
Qed.
Next Obligation.
  exists (middleRat x H). split.
  - exists H. split.
    + apply middleRat_lt_right_of_lt, H0.
    + exists H1, H2; exact H3.
  - apply left_lt_middleRat_of_lt, H0.
Qed.

Lemma outer_MaxCoveredEndELR (a : Q) (ι : Type) (qs rs : ι -> Q) :
  forall i, ELR.Ioo_outer (qs i) (rs i) (MaxCoveredEndELR a ι qs rs).
Proof.
  intros i.
  intros [q [hq1 [n [is [Hci Hco]]]]] q' hq'.
  exists (middleRat q' (rs i)).
  split.
  + apply left_lt_middleRat_of_lt.
    exact hq'.
  + exists (S n), (fin_snoc is i).
    split.
    * intros x [hx1 hx2].
      split.
      -- simpl.
         intro h.
         destruct (Hco x h) as [h1 h2].
         split.
         ++ exact (Cuts.lower _ _ (h1 hx1) _ (Qlt_le_weak _ _ hq1)).
         ++ exact (hx2 _ (middleRat_lt_right_of_lt hq')).
      -- simpl.
         intros [h1 h2].
         apply Hci.
         split.
         ++ exact hx1.
         ++ apply (Cuts.le_q_mono (h2 (hx2 _ (middleRat_lt_right_of_lt hq')))).
            exact (Qlt_le_weak _ _ hq1).
    * simpl.
      intros x [hx1 [hx2 hx3]].
      destruct (Hco x hx1) as [h1 h2].
      split.
      -- intro h.
         refine (hx2 _ _ (middleRat_lt_right_of_lt hq')).
         exact (Cuts.lower _ _ (h1 h) _ (Qlt_le_weak _ _ hq1)).
      -- intro h.
         apply h2.
         refine (Cuts.le_q_mono (hx3 _) (Qlt_le_weak _ _ hq1)).
         exact (h _ (middleRat_lt_right_of_lt hq')).
Qed.

Lemma MaxCoveredEndELR_ge (a : Q) (ι : Type) (qs rs : ι -> Q) :
  ELR.ge_q (MaxCoveredEndELR a ι qs rs) a.
Proof.
  intros y hy.
  exists (middleRat y a).
  split.
  - exact (left_lt_middleRat_of_lt hy).
  - exists O, (Fin.case0 _).
    split.
    + intros x [hx1 hx2].
      exfalso.
      exact (Cuts.not_gt_of_le_q _ _ hx2 (hx1 _ (middleRat_lt_right_of_lt hy))).
    + intros x hx.
      split.
      * intro h.
        exact (h _ (middleRat_lt_right_of_lt hy)).
      * intro h.
        exact (h _ (middleRat_lt_right_of_lt hy)).
Qed.

Theorem HeineBorelL (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    Covered (Icc a b) n (fun i => qs (is i)) (fun i => rs (is i)).
Proof.
  set (c := MaxCoveredEndELR a ι qs rs).
  assert (Hc_in : ELR.Icc_outer a b c).
  { apply h. intros i. apply outer_MaxCoveredEndELR. }
  destruct (Hc_in (MaxCoveredEndELR_ge a ι qs rs)) as [b' Hb'].
  destruct Hb' as [hb [n [is Hcov]]].
  exists n, is.
  eapply CSet_subset_trans; [exact (Icc_mono_right _ _ _ (Qlt_le_weak _ _ hb))|exact Hcov].
Qed.

Print Assumptions HeineBorelL.

Definition ELR_toCuts (x : ELR) : Cuts := {|
  Cuts.L := ELR.L x ;
  Cuts.U := fun _ => False ;
  Cuts.lower := ELR.lower x ;
  Cuts.upper := fun _ h => False_ind _ h ;
  Cuts.open_L := ELR.open_L x ;
  Cuts.open_U := fun _ h => False_ind _ h ;
  Cuts.L_lt_U := fun _ hL _ hU => False_ind _ hU
|}.

Theorem HeineBorel_ELR (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, ELR.Ioo_outer (qs (is i)) (rs (is i)) r) -> ELR.Icc_outer a b r).
Proof.
  destruct (HeineBorelL a b ι qs rs h) as [n [is Hcov]].
  exists n, is.
  intros r Hr.
  assert (Hr' : outer (CSet_FinUnion (fun i => Ioo (qs (is i)) (rs (is i)))) (ELR_toCuts r)).
  {
    apply (proj2 (CSet_FinUnion_outer_iff _ _ _)).
    intros i.
    split.
    - exact (Hr i).
    - intros hU. exfalso. exact hU.
  }
  destruct Hcov as [Hinner Houter].
  destruct (Houter (ELR_toCuts r) Hr') as [Hga Hlb].
  intros hinner.
  exact (Hga hinner).
Qed.

Module EUR.
Record t := {
  U : Q -> Prop ;
  upper : forall x, U x -> forall y, Qle x y -> U y ;
  open_U : forall x, U x -> exists y, U y /\ y < x
}.

Definition le_q (x : t) (q : Q) : Prop :=
  forall y, Qlt q y -> U x y.

Definition Ioo_outer (q r : Q) (x : t) : Prop :=
  U x r -> le_q x q.

Definition Icc_outer (q r : Q) (x : t) : Prop :=
  le_q x r -> U x q.

End EUR.

Notation EUR := EUR.t.

Definition EUR_toCuts (x : EUR) : Cuts := {|
  Cuts.L := fun _ => False ;
  Cuts.U := EUR.U x ;
  Cuts.lower := fun _ h => False_ind _ h ;
  Cuts.upper := EUR.upper x ;
  Cuts.open_L := fun _ h => False_ind _ h ;
  Cuts.open_U := EUR.open_U x ;
  Cuts.L_lt_U := fun _ hL _ => False_ind _ hL
|}.

Theorem EUR_FinCovering_of_ELR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, EUR.Ioo_outer (qs (is i)) (rs (is i)) r) -> EUR.Icc_outer a b r).
Proof.
  destruct (HeineBorelL a b ι qs rs h) as [n [is Hcov]].
  exists n, is.
  intros r Hr.
  assert (Hr' : outer (CSet_FinUnion (fun i => Ioo (qs (is i)) (rs (is i)))) (EUR_toCuts r)).
  {
    apply (proj2 (CSet_FinUnion_outer_iff _ _ _)).
    intros i.
    split.
    - intros hL. exfalso. exact hL.
    - exact (Hr i).
  }
  destruct Hcov as [Hinner Houter].
  destruct (Houter (EUR_toCuts r) Hr') as [Hga Hlb].
  intros hinner.
  exact (Hlb hinner).
Qed.

Theorem EUR_Covering_of_ELR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r)) :
  (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r).
Proof.
  intros r Hr.
  destruct (EUR_FinCovering_of_ELR_Covering a b ι qs rs h) as [n [is His]].
  apply His.
  intros i.
  exact (Hr (is i)).
Qed.

Program Definition MaxCoveredEndEUR (b : Q) (ι : Type)
        (qs rs : ι -> Q) : EUR :=
  {|
    EUR.U := fun q => exists q', q' < q /\ exists (n : nat) (is : Fin.t n -> ι),
                Covered (Icc q' b) n (fun i => qs (is i)) (fun i => rs (is i))
  |}.
Next Obligation.
  exists H; split; [eapply Qlt_le_trans; eauto|].
  exists H2, H3.
  exact H4.
Qed.
Next Obligation.
  exists (middleRat H x). split.
  - exists H. split.
    + apply left_lt_middleRat_of_lt, H0.
    + exists H1, H2; exact H3.
  - apply middleRat_lt_right_of_lt, H0.
Qed.

Lemma outer_MaxCoveredEndEUR (b : Q) (ι : Type) (qs rs : ι -> Q) :
  forall i, EUR.Ioo_outer (qs i) (rs i) (MaxCoveredEndEUR b ι qs rs).
Proof.
  intros i.
  intros [q [hq1 [n [is [Hci Hco]]]]] q' hq'.
  exists (middleRat (qs i) q').
  split.
  + apply middleRat_lt_right_of_lt.
    exact hq'.
  + exists (S n), (fin_snoc is i).
    split.
    * intros x [hx1 hx2].
      split.
      -- simpl.
         intro h.
         destruct (Hco x h) as [h3 h4].
         split.
         ++ exact (hx1 _ (left_lt_middleRat_of_lt hq')).
         ++ exact (Cuts.upper _ _ (h4 hx2) _ (Qlt_le_weak _ _ hq1)).
      -- simpl.
         intros [h1 h2].
         apply Hci.
         split.
         ++ apply (Cuts.ge_q_mono (h1 (hx1 _ (left_lt_middleRat_of_lt hq')))).
            exact (Qlt_le_weak _ _ hq1).
         ++ exact hx2.
    * simpl.
      intros x [hx1 [hx2 hx3]].
      destruct (Hco x hx1) as [h4 h5].
      split.
      -- intro h.
         apply h4.
         refine (Cuts.ge_q_mono (hx2 _) (Qlt_le_weak _ _ hq1)).
         exact (h _ (left_lt_middleRat_of_lt hq')).
      -- intro h.
         refine (hx3 _ _ (left_lt_middleRat_of_lt hq')).
         exact (Cuts.upper _ _ (h5 h) _ (Qlt_le_weak _ _ hq1)).
Qed.

Lemma MaxCoveredEndEUR_le (b : Q) (ι : Type) (qs rs : ι -> Q) :
  EUR.le_q (MaxCoveredEndEUR b ι qs rs) b.
Proof.
  intros y hy.
  exists (middleRat b y).
  split.
  - exact (middleRat_lt_right_of_lt hy).
  - exists O, (Fin.case0 _).
    split.
    + intros x [hx1 hx2].
      exfalso.
      exact (Cuts.not_lt_of_ge_q _ _ hx1 (hx2 _ (left_lt_middleRat_of_lt hy))).
    + intros x hx.
      split.
      * intro h.
        exact (h _ (left_lt_middleRat_of_lt hy)).
      * intro h.
        exact (h _ (left_lt_middleRat_of_lt hy)).
Qed.

Theorem HeineBorelU (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    Covered (Icc a b) n (fun i => qs (is i)) (fun i => rs (is i)).
Proof.
  set (c := MaxCoveredEndEUR b ι qs rs).
  assert (Hc_in : EUR.Icc_outer a b c).
  { apply h. intros i. apply outer_MaxCoveredEndEUR. }
  destruct (Hc_in (MaxCoveredEndEUR_le b ι qs rs)) as [a' Ha'].
  destruct Ha' as [ha [n [is Hcov]]].
  exists n, is.
  eapply CSet_subset_trans; [exact (Icc_mono_left _ _ _ (Qlt_le_weak _ _ ha))|exact Hcov].
Qed.

Theorem HeineBorel_EUR (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, EUR.Ioo_outer (qs (is i)) (rs (is i)) r) -> EUR.Icc_outer a b r).
Proof.
  destruct (HeineBorelU a b ι qs rs h) as [n [is Hcov]].
  exists n, is.
  intros r Hr.
  assert (Hr' : outer (CSet_FinUnion (fun i => Ioo (qs (is i)) (rs (is i)))) (EUR_toCuts r)).
  {
    apply (proj2 (CSet_FinUnion_outer_iff _ _ _)).
    intros i.
    split.
    - intros hU. exfalso. exact hU.
    - exact (Hr i).
  }
  destruct Hcov as [Hinner Houter].
  destruct (Houter (EUR_toCuts r) Hr') as [Hga Hlb].
  intros hinner.
  exact (Hlb hinner).
Qed.

Theorem ELR_FinCovering_of_EUR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, ELR.Ioo_outer (qs (is i)) (rs (is i)) r) -> ELR.Icc_outer a b r).
Proof.
  destruct (HeineBorelU a b ι qs rs h) as [n [is Hcov]].
  exists n, is.
  intros r Hr.
  assert (Hr' : outer (CSet_FinUnion (fun i => Ioo (qs (is i)) (rs (is i)))) (ELR_toCuts r)).
  {
    apply (proj2 (CSet_FinUnion_outer_iff _ _ _)).
    intros i.
    split.
    - exact (Hr i).
    - intros hU. exfalso. exact hU.
  }
  destruct Hcov as [Hinner Houter].
  destruct (Houter (ELR_toCuts r) Hr') as [Hga Hlb].
  intros hinner.
  exact (Hga hinner).
Qed.

Theorem ELR_Covering_of_EUR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r)) :
  (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r).
Proof.
  intros r Hr.
  destruct (ELR_FinCovering_of_EUR_Covering a b ι qs rs h) as [n [is His]].
  apply His.
  intros i.
  exact (Hr (is i)).
Qed.

Module LR.
Record t := {
  L : Q -> Prop ;
  lower : forall x, L x -> forall y, Qle y x -> L y ;
  open_L : forall x, L x -> exists y, L y /\ Qlt x y ;
  inhabited : exists x, L x
}.

Definition ge_q (x : t) (q : Q) : Prop :=
  forall y, Qlt y q -> L x y.

Definition Icc_outer (q r : Q) (x : t) : Prop :=
  ge_q x q -> L x r.

Definition Ioo_outer (q r : Q) (x : t) : Prop :=
  L x q -> ge_q x r.

Definition toELR (x : t) : ELR :=
  {|
    ELR.L := L x ;
    ELR.lower := lower x ;
    ELR.open_L := open_L x
  |}.

End LR.
  
Notation LR := LR.t.

Definition ELR_toLR (x : ELR) (h : exists y, ELR.L x y) : LR :=
  {|
    LR.L := ELR.L x ;
    LR.lower := ELR.lower x ;
    LR.open_L := ELR.open_L x ;
    LR.inhabited := h
  |}.

Theorem ELR_Covering_of_LR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, LR.Ioo_outer (qs i) (rs i) r) -> LR.Icc_outer a b r)) :
  (forall r, (forall i, ELR.Ioo_outer (qs i) (rs i) r) -> ELR.Icc_outer a b r).
Proof.
  intros r Hr.
  intros ha.
  assert (hinh : exists y, ELR.L r y).
  {
    exists (a-1).
    apply ha.
    apply (Qplus_lt_l _ _ (-a)).
    ring_simplify.
    compute.
    reflexivity.
  }
  exact (h (ELR_toLR r hinh) Hr ha).
Qed.

Theorem HeineBorel_LR (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, LR.Ioo_outer (qs i) (rs i) r) -> LR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, LR.Ioo_outer (qs (is i)) (rs (is i)) r) -> LR.Icc_outer a b r).
Proof.
  destruct (HeineBorel_ELR a b ι qs rs (ELR_Covering_of_LR_Covering a b ι qs rs h)) as [n [is Hcov]].
  exists n, is.
  intro r.
  intro hIoo. 
  exact (Hcov (LR.toELR r) hIoo).
Qed.

Module UR.
Record t := {
  U : Q -> Prop ;
  upper : forall x, U x -> forall y, Qle x y -> U y ;
  open_U : forall x, U x -> exists y, U y /\ y < x ;
  inhabited : exists x, U x
}.

Definition le_q (x : t) (q : Q) : Prop :=
  forall y, Qlt q y -> U x y.

Definition Icc_outer (q r : Q) (x : t) : Prop :=
  le_q x r -> U x q.

Definition Ioo_outer (q r : Q) (x : t) : Prop :=
  U x r -> le_q x q.

Definition toEUR (x : t) : EUR :=
  {|
    EUR.U := U x ;
    EUR.upper := upper x ;
    EUR.open_U := open_U x
  |}.

End UR.
  
Notation UR := UR.t.

Definition EUR_toUR (x : EUR) (h : exists y, EUR.U x y) : UR :=
  {|
    UR.U := EUR.U x ;
    UR.upper := EUR.upper x ;
    UR.open_U := EUR.open_U x ;
    UR.inhabited := h
  |}.

Theorem EUR_Covering_of_UR_Covering (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, UR.Ioo_outer (qs i) (rs i) r) -> UR.Icc_outer a b r)) :
  (forall r, (forall i, EUR.Ioo_outer (qs i) (rs i) r) -> EUR.Icc_outer a b r).
Proof.
  intros r Hr.
  intros hb.
  assert (hinh : exists y, EUR.U r y).
  {
    exists (b+1).
    apply hb.
    apply (Qplus_lt_r _ _ (-b)).
    ring_simplify.
    compute.
    reflexivity.
  }
  exact (h (EUR_toUR r hinh) Hr hb).
Qed.

Theorem HeineBorel_UR (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, UR.Ioo_outer (qs i) (rs i) r) -> UR.Icc_outer a b r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, UR.Ioo_outer (qs (is i)) (rs (is i)) r) -> UR.Icc_outer a b r).
Proof.
  destruct (HeineBorel_EUR a b ι qs rs (EUR_Covering_of_UR_Covering a b ι qs rs h)) as [n [is Hcov]].
  exists n, is.
  intro r.
  intro hIoo. 
  exact (Hcov (UR.toEUR r) hIoo).
Qed.