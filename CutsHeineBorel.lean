import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
universe u

instance : IsTrans (Set α) (· ⊆ ·) := {
  trans := fun _ _ _ h₁ h₂ _ ha ↦ h₂ (h₁ ha)
}

structure CSet (α : Type u) where
  inner : Set α
  outer : Set α
  disjoint : ∀ {x : α}, x ∈ inner → ¬ x ∈ outer

def CSet.subset {α : Type u} (s t : CSet α) : Prop :=
  s.inner ⊆ t.inner ∧ t.outer ⊆ s.outer

instance : HasSubset (CSet α) := ⟨CSet.subset⟩

def CSet.subset.trans {α : Type u} (s t u : CSet α) (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

instance : IsTrans (CSet α) (· ⊆ ·) := ⟨CSet.subset.trans⟩

def CSet.union {α : Type u} (s t : CSet α) : CSet α where
  inner := fun x ↦ (x ∈ s.outer → x ∈ t.inner) ∧ (x ∈ t.outer → x ∈ s.inner)
  outer := s.outer ∩ t.outer
  disjoint := by
    rintro x ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    exact t.disjoint (h₁ h₃) h₄

instance : Union (CSet α) := ⟨CSet.union⟩

lemma CSet.union_outer_eq {α : Type u} {s t : CSet α} :
  (s ∪ t).outer = s.outer ∩ t.outer := rfl

def CSet.union.mono {α : Type u} {s t u v: CSet α} (hst : s ⊆ t) (huv : u ⊆ v) : s ∪ u ⊆ t ∪ v := by
  obtain ⟨hst₁, hst₂⟩ := hst
  obtain ⟨huv₁, huv₂⟩ := huv
  constructor
  · intro x ⟨h₁, h₂⟩
    constructor
    · exact fun a => huv₁ (h₁ (hst₂ a))
    · exact fun a => hst₁ (h₂ (huv₂ a))
  · intro x ⟨h₁, h₂⟩
    constructor
    · exact hst₂ h₁
    · exact huv₂ h₂

def CSet.empty {α : Type u} : CSet α where
  inner := ∅
  outer := Set.univ
  disjoint := fun h₁ _ ↦ h₁

def CSet.FinUnion {α : Type u} : {n : Nat} → (Fin n → CSet α) → CSet α
| 0, _ => .empty
| n+1, s => .FinUnion (s ∘ Fin.castSucc) ∪ (s (Fin.last n))

lemma CSet.FinUnion.outer_eq_Inter {α : Type u} :
  ∀ {n : Nat} (s : Fin n → CSet α), (CSet.FinUnion s).outer = ⋂ i, (s i).outer
| 0, _ => by
  dsimp [CSet.FinUnion, CSet.empty]
  ext x
  constructor
  · intro _
    apply Set.mem_iInter.mpr
    intro ⟨i, hi⟩
    apply False.elim
    exact Nat.not_succ_le_zero i hi
  · exact fun _ ↦ trivial
| n+1, s => by
  dsimp [CSet.FinUnion, CSet.union_outer_eq]
  rw [CSet.FinUnion.outer_eq_Inter (s ∘ Fin.castSucc)]
  ext x
  constructor
  · intro ⟨hx₁, hx₂⟩
    apply Set.mem_iInter.mpr
    intro ⟨m, hm₂⟩
    if hm₁ : m < n then
      exact Set.mem_iInter.mp hx₁ ⟨m, hm₁⟩
    else
      rw [(Fin.eq_last_of_not_lt hm₁ : ⟨m, hm₂⟩ = Fin.last n)]
      exact hx₂
  · intro hx
    constructor
    · exact Set.mem_iInter.mpr fun _ ↦ Set.mem_iInter.mp hx _
    · exact Set.mem_iInter.mp hx (Fin.last n)

def CSet.empty_subset {α : Type u} (s : CSet α) : CSet.empty ⊆ s := by
  constructor
  · exact fun x hx ↦ False.elim hx
  · exact fun _ _ ↦ trivial

def CSet.antiSubset {α : Type u} (s t : CSet α) : Prop :=
  ∃ x, x ∈ s.inner ∧ x ∈ t.outer

lemma CSet.antiSubset.mono_left {α : Type u} {s t u : CSet α} (h₂ : s.antiSubset u) (h₁ : s ⊆ t) : t.antiSubset u := by
  obtain ⟨h₁₁, h₁₂⟩ := h₁
  obtain ⟨x, hx₁, hx₂⟩ := h₂
  use x
  constructor
  · exact h₁₁ hx₁
  · exact hx₂

lemma CSet.antiSubset.union_mono {α : Type u} {s t u v : CSet α} (h₂ : (s ∪ u).antiSubset (t ∪ v)) (h₁ : u ⊆ v) : s.antiSubset t := by
  obtain ⟨h₁₁, h₁₂⟩ := h₁
  obtain ⟨x, ⟨hx₁₁, hx₁₂⟩, ⟨hx₂₁, hx₂₂⟩⟩ := h₂
  use x
  constructor
  · exact hx₁₂ (h₁₂ hx₂₂)
  · exact hx₂₁

lemma CSet.subset.not_antiSubset {α : Type u} {s t : CSet α} (h : s ⊆ t) : ¬ s.antiSubset t := by
  obtain ⟨h₁, h₂⟩ := h
  intro h'
  obtain ⟨x, hx₁, hx₂⟩ := h'
  exact s.disjoint hx₁ (h₂ hx₂)

instance RatLE : LE ℚ := {
  le := fun x y ↦ x.num * y.den ≤ y.num * x.den
}

instance RatLT : LT ℚ := {
  lt := fun x y ↦ x.num * y.den < y.num * x.den
}

instance : Preorder ℚ := {
  le x y := x ≤ y,
  le_refl x := le_refl (x.num * ↑x.den)
  le_trans := fun x y z h₁ h₂ ↦ by
    apply (Int.mul_le_mul_iff_of_pos_right <| Int.ofNat_pos.mpr y.pos).mp
    calc
      _ = x.num * y.den * z.den := by
        rw [mul_assoc, mul_comm (z.den : ℤ) (y.den : ℤ), mul_assoc]
      _ ≤ y.num * x.den * z.den :=
        (Int.mul_le_mul_iff_of_pos_right <| Int.ofNat_pos.mpr z.pos).mpr h₁
      _ = y.num * z.den * x.den := by
        rw [mul_assoc, mul_comm (x.den : ℤ) (z.den : ℤ), mul_assoc]
      _ ≤ z.num * y.den * x.den :=
        (Int.mul_le_mul_iff_of_pos_right <| Int.ofNat_pos.mpr x.pos).mpr h₂
      _ = _ := by
        rw [mul_assoc, mul_comm (y.den : ℤ) (x.den : ℤ), mul_assoc]
  lt_iff_le_not_le x y := Int.lt_iff_le_not_le
}

structure Cuts where
  L : Set ℚ
  U : Set ℚ
  lower : ∀ x : ℚ, x ∈ L → ∀ y : ℚ, y ≤ x → y ∈ L
  upper : ∀ x : ℚ, x ∈ U → ∀ y : ℚ, x ≤ y → y ∈ U
  open_L : ∀ x : ℚ, x ∈ L → ∃ y : ℚ, y ∈ L ∧ x < y
  open_U : ∀ x : ℚ, x ∈ U → ∃ y : ℚ, y ∈ U ∧ y < x
  L_lt_U : ∀ x : ℚ, x ∈ L → ∀ y : ℚ, y ∈ U → x < y

namespace Cuts

def le (x y : Cuts) : Prop :=
  x.L ⊆ y.L ∧ y.U ⊆ x.U

def lt (x y : Cuts) : Prop :=
  ∃ q : ℚ, q ∈ x.U ∧ q ∈ y.L

def le_q (x : Cuts) (q : ℚ) : Prop :=
  ∀ y : ℚ, q < y → y ∈ x.U

def not_gt_of_le_q (x : Cuts) (q : ℚ) : le_q x q → q ∉ x.L := by
  intro h₁ h₂
  obtain ⟨y, hy₁, hy₂⟩ := x.open_L q h₂
  exact (lt_self_iff_false y).mp <| x.L_lt_U y hy₁ y <| h₁ y hy₂

lemma le_q_of_le {x : Cuts} {q r: ℚ} (hq : le_q x q) (hr : q ≤ r) : le_q x r := by
  intro y hy
  exact hq y (lt_of_le_of_lt hr hy)

lemma le_q_of_lt {x : Cuts} {q : ℚ} (h : q ∈ x.U) : le_q x q :=
  fun y hy ↦ x.upper q h y (le_of_lt hy)

def ge_q (x : Cuts) (q : ℚ) : Prop :=
  ∀ y : ℚ, y < q → y ∈ x.L

def not_lt_of_ge_q (x : Cuts) (q : ℚ) : ge_q x q → q ∉ x.U := by
  intro h₁ h₂
  obtain ⟨y, hy₁, hy₂⟩ := x.open_U q h₂
  exact (lt_self_iff_false y).mp <| x.L_lt_U y (h₁ y hy₂) y hy₁

lemma ge_q_of_gt {x : Cuts} {q : ℚ} (h : q ∈ x.L) : ge_q x q :=
  fun y hy ↦ x.lower q h y (le_of_lt hy)

def Icc (a b : ℚ) : CSet Cuts where
  inner r := r.ge_q a ∧ r.le_q b
  outer r := (r.ge_q a → b ∈ r.L) ∧ (r.le_q b → a ∈ r.U)
  disjoint {r} :=
    fun h₁ h₂ ↦ r.not_gt_of_le_q b h₁.2 <| h₂.1 h₁.1

def Ioo (a b : ℚ) : CSet Cuts where
  inner r := a ∈ r.L ∧ b ∈ r.U
  outer r := (a ∈ r.L → r.ge_q b) ∧ (b ∈ r.U → r.le_q a)
  disjoint {r} :=
    fun h₁ h₂ ↦ r.not_gt_of_le_q a (h₂.2 h₁.2) h₁.1

lemma Icc_mono_right (a b c : ℚ) (h : b ≤ c) : Icc a b ⊆ Icc a c := by
  constructor
  · intro r ⟨hr₁, hr₂⟩
    constructor
    · exact fun x hx ↦ hr₁ x hx
    · exact fun x hx ↦ hr₂ x (lt_of_le_of_lt h hx)
  · intro r ⟨hr₁, hr₂⟩
    constructor
    · exact fun h' ↦ r.lower c (hr₁ h') b h
    · exact fun h' ↦ hr₂ <| le_q_of_le h' h

lemma Icc_sub_Ioo (a b c d : ℚ) (hac : c < a) (hbd : b < d) : Icc a b ⊆ Ioo c d := by
  constructor
  · intro r ⟨hr₁, hr₂⟩
    constructor
    · exact hr₁ c hac
    · exact hr₂ d hbd
  · intro r ⟨hr₁, hr₂⟩
    constructor
    · exact fun a => hr₁ (a c hac) b hbd
    · exact fun a_1 => hr₂ (a_1 d hbd) a hac

lemma Icc_sub_Icc_union (a b c : ℚ) : Icc a c ⊆ Icc a b ∪ Icc b c := by
  constructor
  · intro r ⟨hr₁, hr₂⟩
    constructor
    · intro ⟨hr₃, hr₄⟩
      constructor
      · exact ge_q_of_gt <| hr₃ hr₁
      · exact hr₂
    · intro ⟨hr₃, hr₄⟩
      constructor
      · exact hr₁
      · exact le_q_of_lt <| hr₄ hr₂
  · intro r ⟨⟨hr₁, hr₂⟩, ⟨hr₃, hr₄⟩⟩
    constructor
    · exact fun h ↦ hr₃ <| ge_q_of_gt (hr₁ h)
    · exact fun h ↦ hr₂ <| le_q_of_lt (hr₄ h)

lemma Icc_empty {a b : ℚ} (hab : a > b) : Icc a b ⊆ CSet.empty := by
  constructor
  · intro r ⟨hr₁, hr₂⟩
    exact r.not_gt_of_le_q b hr₂ <| hr₁ b hab
  · intro r _
    constructor
    · exact fun a => a b hab
    · exact fun a_1 => a_1 a hab

def Covered (s : CSet Cuts) {n : ℕ} (qs rs : Fin n → ℚ) : Prop := s ⊆ CSet.FinUnion fun i ↦ (Ioo (qs i) (rs i))

lemma Covered.mono {s t : CSet Cuts} {n : ℕ} {qs rs : Fin n → ℚ} (hs : Covered s qs rs) (ht : t ⊆ s) :
  Covered t qs rs := ht.trans hs

lemma Covered.snoc {s t: CSet Cuts} {n : ℕ} {qs rs : Fin n → ℚ} (hs : Covered s qs rs) {qn rn : ℚ} (ht : t ⊆ Ioo qn rn) :
  Covered (s ∪ t) (Fin.snoc qs qn) (Fin.snoc rs rn) := by
  apply CSet.union.mono
  · dsimp [Covered] at hs
    convert hs
    rw [Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · convert ht
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_last]

def UnCovered (s : CSet Cuts) {n : ℕ} (qs rs : Fin n → ℚ) : Prop := s.antiSubset (CSet.FinUnion fun i ↦ (Ioo (qs i) (rs i)))

lemma UnCovered.mono {s t : CSet Cuts} {n : ℕ} {qs rs : Fin n → ℚ} (hs : UnCovered s qs rs) (ht : s ⊆ t):
  UnCovered t qs rs := hs.mono_left ht

lemma UnCovered.snoc {s t: CSet Cuts} {n : ℕ} {qs rs : Fin n → ℚ} {qn rn : ℚ} (hs : UnCovered (s ∪ t) (Fin.snoc qs qn) (Fin.snoc rs rn)) (ht : t ⊆ Ioo qn rn) :
  UnCovered s qs rs := by
  have : (s ∪ t).antiSubset ((CSet.FinUnion fun i ↦ (Ioo (qs i) (rs i))) ∪ Ioo qn rn) := by
    dsimp [UnCovered] at hs
    convert hs
    dsimp [CSet.FinUnion]
    rw [Fin.snoc_last, Fin.snoc_last]
    congr
    ext _
    rw [Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_castSucc]
  exact CSet.antiSubset.union_mono this ht

lemma Covered.not_UnCovered {s : CSet Cuts} {n : ℕ} {qs rs : Fin n → ℚ} (hs : Covered s qs rs) :
  ¬ UnCovered s qs rs := CSet.subset.not_antiSubset hs

def middleRat (x y : ℚ) : ℚ := by
  let g := (x.num + y.num).gcd (x.den + y.den)
  have den_nz' : x.den + y.den ≠ 0 := by
    intro h
    apply x.den_nz
    exact Nat.eq_zero_of_add_eq_zero_right h
  exact {
    num := (x.num + y.num) / g,
    den := (x.den + y.den).div g,
    den_nz := Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_right (x.num+y.num).natAbs (Nat.pos_of_ne_zero den_nz')),
    reduced := by
      convert Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz'))
      rw [Int.natAbs_ediv_of_dvd _ _ Int.gcd_dvd_left]
      rfl
}

lemma middleRat_lt_right_of_lt {x y : ℚ} (h : x < y) : middleRat x y < y := by
  dsimp [RatLT, middleRat]
  apply Int.lt_of_mul_lt_mul_right _ <| Int.ofNat_zero_le ((x.num + y.num).gcd (x.den + y.den))
  rw [mul_assoc, mul_comm (y.den : ℤ) _, ←mul_assoc]
  rw [Int.ediv_mul_cancel Int.gcd_dvd_left]
  rw [mul_assoc, ←Int.ofNat_mul]
  have : ((x.den + y.den).div ((x.num + y.num).gcd (↑x.den + ↑y.den)) * (x.num + y.num).gcd (↑x.den + ↑y.den)) = (x.den + y.den) :=
    Nat.div_mul_cancel <| Int.ofNat_dvd.mp Int.gcd_dvd_right
  rw [this, add_mul, Int.ofNat_add, mul_add]
  exact Int.add_lt_add_right h (y.num * ↑y.den)

lemma left_lt_middleRat_of_lt {x y : ℚ} (h : x < y) : x < middleRat x y := by
  dsimp [RatLT, middleRat]
  apply Int.lt_of_mul_lt_mul_right _ <| Int.ofNat_zero_le ((x.num + y.num).gcd (x.den + y.den))
  rw [mul_assoc, ←Int.ofNat_mul]
  have : ((x.den + y.den).div ((x.num + y.num).gcd (↑x.den + ↑y.den)) * (x.num + y.num).gcd (↑x.den + ↑y.den)) = (x.den + y.den) :=
    Nat.div_mul_cancel <| Int.ofNat_dvd.mp Int.gcd_dvd_right
  rw [this, mul_assoc, mul_comm (x.den : ℤ) _, ←mul_assoc]
  rw [Int.ediv_mul_cancel Int.gcd_dvd_left, Int.ofNat_add, mul_add, add_mul]
  exact Int.add_lt_add_left h (x.num * ↑x.den)

def MaxCoveredEndCut (a : ℚ) (ι : Type u) (qs rs : ι → ℚ) : Cuts :=
{
  L := fun q ↦ ∃ q' : ℚ, q < q' ∧ ∃ (n : ℕ) (is : Fin n → ι), Covered (Icc a q') (qs ∘ is) (rs ∘ is)
  U := fun q ↦ ∃ q' : ℚ, q' < q ∧ ∀ (n : ℕ) (is : Fin n → ι), UnCovered (Icc a q') (qs ∘ is) (rs ∘ is)
  lower := by
    rintro x ⟨q, hq, n, is, hx⟩ y hy
    use q, (gt_of_gt_of_ge hq hy), n, is
  upper := by
    rintro x ⟨q', hq', _⟩ y hy
    use q', gt_of_ge_of_gt hy hq'
  open_L := by
    rintro x ⟨q', hq', hx⟩
    use middleRat x q'
    constructor
    · use q'
      constructor
      · exact middleRat_lt_right_of_lt hq'
      · exact hx
    · exact left_lt_middleRat_of_lt hq'
  open_U := by
    rintro x ⟨q', hq', hx⟩
    use middleRat q' x
    constructor
    · use q'
      constructor
      · exact left_lt_middleRat_of_lt hq'
      · exact hx
    · exact middleRat_lt_right_of_lt hq'
  L_lt_U := by
    rintro x hx y hy
    obtain ⟨qx, hqx, n, is, hx⟩ := hx
    obtain ⟨qy, hqy, hy⟩ := hy
    apply Int.lt_of_not_ge
    intro h
    apply Covered.not_UnCovered _ (hy n is)
    apply hx.mono
    apply Icc_mono_right a qy qx
    exact le_of_lt <| gt_trans hqx <| gt_of_ge_of_gt h hqy
}

lemma outer_MaxCoveredEndCut (a : ℚ) (ι : Type u) (qs rs : ι → ℚ) :
  ∀ i, MaxCoveredEndCut a ι qs rs ∈ (Ioo (qs i) (rs i)).outer := by
  intro i
  constructor
  · rintro ⟨q, hq, n, is, hx⟩ q' hq'
    use middleRat q' (rs i)
    constructor
    · exact left_lt_middleRat_of_lt hq'
    · use n+1, Fin.snoc is i
      apply Covered.mono _ <| Icc_sub_Icc_union a q (middleRat q' (rs i))
      rw [Fin.comp_snoc qs is i, Fin.comp_snoc rs is i]
      apply Covered.snoc hx
      apply Icc_sub_Ioo q (middleRat q' (rs i)) (qs i) (rs i) hq
      exact middleRat_lt_right_of_lt hq'
  · rintro ⟨q, hq, hcov⟩ q' hq'
    use middleRat (qs i) q'
    constructor
    · exact middleRat_lt_right_of_lt hq'
    · rintro n is
      apply UnCovered.snoc _ <| Icc_sub_Ioo (middleRat (qs i) q') q (qs i) (rs i) (left_lt_middleRat_of_lt hq') hq
      apply UnCovered.mono _ <| Icc_sub_Icc_union a (middleRat (qs i) q') q
      convert hcov (n+1) (Fin.snoc is i)
      · exact Eq.symm (Fin.comp_snoc qs is i)
      · exact Eq.symm (Fin.comp_snoc rs is i)

lemma MaxCoveredEndCut_ge (a : ℚ) (ι : Type u) (qs rs : ι → ℚ) :
  (MaxCoveredEndCut a ι qs rs).ge_q a := by
  intro x hx
  use middleRat x a
  constructor
  · exact left_lt_middleRat_of_lt hx
  · use 0, Fin.elim0
    exact Covered.mono (CSet.empty_subset _) <| Icc_empty (middleRat_lt_right_of_lt hx)

theorem HeineBorel (a b : ℚ) {ι : Type u} (qs rs : ι → ℚ)
  (h : ⋂ i, (Ioo (qs i) (rs i)).outer ⊆ (Icc a b).outer)
  : ∃ (n : ℕ) (is : Fin n → ι),  Covered (Icc a b) (qs ∘ is) (rs ∘ is) := by
  let c := MaxCoveredEndCut a ι qs rs
  have h₁ : c ∈ (Icc a b).outer := h (Set.mem_iInter.mpr <| outer_MaxCoveredEndCut a ι qs rs)
  obtain ⟨b', hb', n, is, hcov⟩ := h₁.1 <| MaxCoveredEndCut_ge a ι qs rs
  use n, is
  exact hcov.mono (Icc_mono_right a b b' (le_of_lt hb'))

#print axioms HeineBorel

theorem HeineBorel_corollary (a b : ℚ) {ι : Type u} (qs rs : ι → ℚ)
  (h : ⋂ i, (Ioo (qs i) (rs i)).outer ⊆ (Icc a b).outer)
  : ∃ (n : ℕ) (is : Fin n → ι),  ⋂ i, (Ioo (qs (is i)) (rs (is i))).outer ⊆ (Icc a b).outer := by
  obtain ⟨n,is,_,h⟩ := HeineBorel a b qs rs h
  use n, is
  rw [CSet.FinUnion.outer_eq_Inter] at h
  exact h

#print axioms HeineBorel_corollary
