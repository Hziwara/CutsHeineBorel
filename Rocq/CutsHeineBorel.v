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

Record Cuts := {
  L : Q -> Prop ;
  U : Q -> Prop ;
  lower : forall x, L x -> forall y, Qle y x -> L y ;
  upper : forall x, U x -> forall y, Qle x y -> U y ;
  open_L : forall x, L x -> exists y, L y /\ Qlt x y ;
  open_U : forall x, U x -> exists y, U y /\ y < x ;
  L_lt_U : forall x, L x -> forall y, U y -> Qlt x y
}.

Definition le_q (x : Cuts) (q : Q) : Prop :=
  forall y, Qlt q y -> U x y.

Definition ge_q (x : Cuts) (q : Q) : Prop :=
  forall y, Qlt y q -> L x y.

Lemma not_gt_of_le_q (x : Cuts) (q : Q) :
  le_q x q -> ~ L x q.
Proof.
  intros hle hL.
  destruct (open_L x q hL) as [y [HyL Hylt]].
  specialize (hle y Hylt). 
  pose proof (L_lt_U x y HyL y hle) as contra.
  now apply (Qlt_irrefl y).
Qed.

Lemma not_lt_of_ge_q (x : Cuts) (q : Q) :
  ge_q x q -> ~ U x q.
Proof.
  intros hge hU.
  destruct (open_U x q hU) as [y [HyU Hylt]].
  specialize (hge y Hylt).
  pose proof (L_lt_U x y hge y HyU) as contra.
  now apply (Qlt_irrefl y).
Qed.

Lemma le_q_of_lt {x : Cuts} {q : Q} (h : U x q) : le_q x q.
Proof.
  intros y hy. eapply upper; eauto. apply Qlt_le_weak, hy.
Qed.

Lemma ge_q_of_gt {x : Cuts} {q : Q} (h : L x q) : ge_q x q.
Proof.
  intros y hy. eapply lower; eauto. apply Qlt_le_weak, hy.
Qed.

Lemma le_q_mono {x : Cuts} {q r : Q} :
  le_q x q -> Qle q r -> le_q x r.
Proof.
  intros hq qr y hyr. apply hq. eapply Qle_lt_trans.
  - exact qr.
  - exact hyr.
Qed.

Definition Icc (a b : Q) : CSet Cuts.
Proof.
  refine {|
    inner := fun r => ge_q r a /\ le_q r b ;
    outer := fun r => (ge_q r a -> L r b) /\ (le_q r b -> U r a)
  |}.
  intros r [Hga Hlb] [H1 H2].
  eapply not_gt_of_le_q.
  - exact Hlb.
  - apply H1; exact Hga.
Defined.

Definition Ioo (a b : Q) : CSet Cuts.
Proof.
  refine {|
    inner := fun r => L r a /\ U r b ;
    outer := fun r => (L r a -> ge_q r b) /\ (U r b -> le_q r a)
  |}.
  intros r [HLa HUb] [H1 H2].
  eapply not_gt_of_le_q.
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
    + intros H. eapply lower; [exact (Hga H)| exact h].
    + intros H. apply Hlb. eapply le_q_mono; [apply H|assumption].
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
    + intros [Hgb Hlb]. split; [apply ge_q_of_gt, (Hgb Hga)| exact Hlc].
    + intros [Hgb Hlb]. split; [exact Hga| apply le_q_of_lt, (Hlb Hlc)].
  - intros r [[H1 H2] [H3 H4]]. split.
    + intros H. apply H3. apply ge_q_of_gt. apply H1. exact H.
    + intros H. apply H2. apply le_q_of_lt. apply H4. exact H.
Qed.

Lemma Icc_empty {a b : Q} (hab : a > b) :
  CSet_subset (Icc a b) (CSet_empty).
Proof.
  split.
  - intros r [Hga Hlb]. exfalso.
    eapply not_gt_of_le_q; [exact Hlb| exact (Hga b hab)].
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

Program Definition MaxCoveredEndCut (a : Q) (ι : Type)
        (qs rs : ι -> Q) : Cuts :=
  {|
    L := fun q => exists q', q < q' /\ exists (n : nat) (is : Fin.t n -> ι),
                Covered (Icc a q') n (fun i => qs (is i)) (fun i => rs (is i)) ;
    U := fun q => exists q', q' < q /\ forall (n : nat) (is : Fin.t n -> ι),
                UnCovered (Icc a q') n (fun i => qs (is i)) (fun i => rs (is i))
  |}.
Next Obligation.
  exists H; split; [eapply Qle_lt_trans; eauto|].
  exists H2, H3.
  exact H4.
Qed.
Next Obligation.
  exists H; split; [eapply Qlt_le_trans; eauto|].
  exact H2.
Qed.
Next Obligation.
  exists (middleRat x H). split.
  - exists H. split.
    + apply middleRat_lt_right_of_lt, H0.
    + exists H1, H2; exact H3.
  - apply left_lt_middleRat_of_lt, H0.
Qed.
Next Obligation.
  exists (middleRat H x). split.
  - exists H. split.
    + apply left_lt_middleRat_of_lt, H0.
    + exact H1.
  - apply middleRat_lt_right_of_lt, H0.
Qed.
Next Obligation.
  apply Qnot_le_lt.
  intro yleqx.
  apply (@Covered_not_UnCovered (Icc a H0) H4 (fun i => qs (H5 i)) (fun i => rs (H5 i))).
  - apply (Covered_mono H6).
    apply Icc_mono_right.
    apply Qlt_le_weak.
    exact (Qlt_trans _ _ _ (Qlt_le_trans _ _ _ H1 yleqx) H3).
  - exact (H2 H4 H5). 
Qed.

Lemma outer_MaxCoveredEndCut (a : Q) (ι : Type) (qs rs : ι -> Q) :
  forall i, outer (Ioo (qs i) (rs i)) (MaxCoveredEndCut a ι qs rs).
Proof.
  intros i.
  split.
  - intros [q [hq1 [n [is [Hci Hco]]]]] q' hq'.
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
           ++ exact (lower _ _ (h1 hx1) _ (Qlt_le_weak _ _ hq1)).
           ++ exact (hx2 _ (middleRat_lt_right_of_lt hq')).
        -- simpl.
           intros [h1 h2].
           apply Hci.
           split.
           ++ exact hx1.
           ++ apply (le_q_mono (h2 (hx2 _ (middleRat_lt_right_of_lt hq')))).
              exact (Qlt_le_weak _ _ hq1).
      * simpl.
        intros x [hx1 [hx2 hx3]].
        destruct (Hco x hx1) as [h1 h2].
        split.
        -- intro h.
           refine (hx2 _ _ (middleRat_lt_right_of_lt hq')).
           exact (lower _ _ (h1 h) _ (Qlt_le_weak _ _ hq1)).
        -- intro h.
           apply h2.
           refine (le_q_mono (hx3 _) (Qlt_le_weak _ _ hq1)).
           exact (h _ (middleRat_lt_right_of_lt hq')).
  - intros [q [hq1 hq2]] q' hq'.
    exists (middleRat (qs i) q').
    split.
    + apply middleRat_lt_right_of_lt.
      exact hq'.
    + intros n is.
      apply (UnCovered_snoc (qs i) (rs i)).
      apply (UnCovered_mono (hq2 (S n) (fin_snoc is i))).
      split.
      * intros x [hx1 hx2].
        split.
        -- intros [h1 h2].
           split.
           ++ exact (lower _ _ (h1 hx1) _ (Qlt_le_weak _ _ (left_lt_middleRat_of_lt hq'))).
           ++ exact (hx2 _ hq1).
        -- intros [h1 h2].
           split.
           ++ exact hx1.
           ++ exact (le_q_mono (h2 (hx2 _ hq1)) (Qlt_le_weak _ _ (left_lt_middleRat_of_lt hq'))).
      * intros x [[hx1 hx2] [hx3 hx4]].
        split.
        -- intro h.
           refine (hx3 _ _ hq1).
           exact (lower _ _ (hx1 h) _ (Qlt_le_weak _ _ (left_lt_middleRat_of_lt hq'))).
        -- intro h.
           apply hx2.
           refine (le_q_mono (hx4 _) (Qlt_le_weak _ _ (left_lt_middleRat_of_lt hq'))).
           exact (h _ hq1).
Qed.

Lemma MaxCoveredEndCut_ge (a : Q) (ι : Type) (qs rs : ι -> Q) :
  ge_q (MaxCoveredEndCut a ι qs rs) a.
Proof.
  intros y hy.
  exists (middleRat y a).
  split.
  - exact (left_lt_middleRat_of_lt hy).
  - exists O, (Fin.case0 _).
    split.
    + intros x [hx1 hx2].
      exfalso.
      exact (not_gt_of_le_q _ _ hx2 (hx1 _ (middleRat_lt_right_of_lt hy))).
    + intros x hx.
      split.
      * intro h.
        exact (h _ (middleRat_lt_right_of_lt hy)).
      * intro h.
        exact (h _ (middleRat_lt_right_of_lt hy)).
Qed.

Theorem HeineBorel (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, outer (Ioo (qs i) (rs i)) r) -> outer (Icc a b) r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    Covered (Icc a b) n (fun i => qs (is i)) (fun i => rs (is i)).
Proof.
  set (c := MaxCoveredEndCut a ι qs rs).
  assert (Hc_in : outer (Icc a b) c).
  { apply h. intros i. apply outer_MaxCoveredEndCut. }
  destruct Hc_in as [H1 H2].
  destruct (H1 (MaxCoveredEndCut_ge a ι qs rs)) as [b' Hb'].
  destruct Hb' as [hb [n [is Hcov]]].
  exists n, is.
  eapply CSet_subset_trans; [exact (Icc_mono_right _ _ _ (Qlt_le_weak _ _ hb))|exact Hcov].
Qed.

Theorem HeineBorel_corollary (a b : Q) (ι : Type) (qs rs : ι -> Q)
  (h : (forall r, (forall i, outer (Ioo (qs i) (rs i)) r) -> outer (Icc a b) r)) :
  exists (n : nat) (is : Fin.t n -> ι),
    (forall r, (forall i, outer (Ioo (qs (is i)) (rs (is i))) r) -> outer (Icc a b) r).
Proof.
  destruct (HeineBorel a b ι qs rs h) as [n [is [Hcov1 Hcov2]]].
  exists n, is.
  intros r Hr.
  apply (Hcov2 r).
  exact ((proj2 (CSet_FinUnion_outer_iff _ _ _)) Hr).
Qed.

Print Assumptions HeineBorel_corollary.

