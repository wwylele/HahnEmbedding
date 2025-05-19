import HahnEmbedding.ArchimedeanSubgroup
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Order.WellFoundedSet

open Classical in
noncomputable
def HahnSeries.cut_fun (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R]
    (c : Γ) (x : HahnSeries Γ R) : HahnSeries Γ R where
  coeff (i) := if c ≤ i then 0 else x.coeff i
  isPWO_support' := by
    apply Set.IsPWO.mono x.isPWO_support
    simp

noncomputable
def HahnSeries.cut (Γ : Type*) (R : Type*) [PartialOrder Γ] [Semiring R]
    (c : Γ) : HahnSeries Γ R →ₗ[R] HahnSeries Γ R where
  toFun := HahnSeries.cut_fun Γ R c
  map_add' := by
    intro x y
    unfold cut_fun
    apply HahnSeries.ext
    ext i
    simp only [coeff_add', Pi.add_apply]
    split_ifs
    · simp
    · simp
  map_smul' := by
    intro m x
    unfold cut_fun
    apply HahnSeries.ext
    ext i
    simp


instance HahnSeries.instPartialOrder (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [Zero R] [PartialOrder R] : PartialOrder (HahnSeries Γ R) :=
  PartialOrder.lift (fun (x : HahnSeries Γ R) ↦ toLex x.coeff) (by
    intro x y
    simp
  )

noncomputable
instance HahnSeries.instLinearOrder (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [Zero R] [LinearOrder R] : LinearOrder (HahnSeries Γ R) := {

  le_total := by
    intro a b
    suffices a < b ∨ a = b ∨ b < a by
      obtain lt|eq|gt := this
      · exact Or.inl lt.le
      · exact Or.inl eq.le
      · exact Or.inr gt.le
    rcases eq_or_ne a b with hab | hab
    · exact Or.inr (Or.inl hab)
    · have hab := (HahnSeries.ext_iff.ne).mp hab
      rw [Function.ne_iff] at hab
      let u := {i : Γ | a.coeff i ≠ 0} ∪ {i : Γ | b.coeff i ≠ 0}
      obtain h := a.isPWO_support'.isWF.union b.isPWO_support'.isWF
      let v := {i : Γ | a.coeff i ≠ b.coeff i}
      have hvu : v ⊆ u := by
        unfold u v
        intro i h
        simp only [Set.mem_setOf_eq] at h
        simp only [Set.mem_union, Set.mem_setOf_eq]
        rw [or_iff_not_imp_left]
        intro h2
        simp only [ne_eq, Decidable.not_not] at h2
        rw [h2] at h
        exact h.symm
      have hv : v.IsWF := h.subset hvu
      let i := hv.min hab
      have hri : ∀ j, j < i → a.coeff j = b.coeff j := by
        intro j
        rw [← not_imp_not]
        exact fun h' => hv.not_lt_min hab h'
      have hne : a.coeff i ≠ b.coeff i := hv.min_mem hab
      rcases lt_trichotomy (a.coeff i) (b.coeff i) with hi | hi
      exacts [Or.inl ⟨i, hri, hi⟩,
        Or.inr <| Or.inr <| ⟨i, fun j hj => (hri j hj).symm, hi.resolve_left hne⟩]


  toDecidableLE := by apply Classical.decRel

}

theorem HahnSeries.lt_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [Zero R] [PartialOrder R] (a b : HahnSeries Γ R) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → a.coeff j = b.coeff j) ∧ a.coeff i < b.coeff i := by
  rfl

instance HahnSeries.instOrderedAddMonoid (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [PartialOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]:
    IsOrderedAddMonoid (HahnSeries Γ R) where
  add_le_add_left := by
    intro a b hab c
    obtain heq|hlt := eq_or_lt_of_le hab
    · rw [heq]
    · apply le_of_lt
      rw [HahnSeries.lt_iff] at hlt ⊢
      obtain ⟨i, hi⟩ := hlt
      use i
      aesop


theorem HahnSeries.archimedeanClass_eq_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    [Archimedean R]
    {x y : HahnSeries Γ R} :
    archimedeanClass.mk x = archimedeanClass.mk y ↔ x.orderTop = y.orderTop := by

  by_cases hyt : y.orderTop = ⊤
  · rw [hyt]
    have hy0 : y = 0 := orderTop_eq_top_iff.mp hyt
    have hy0' : archimedeanClass.mk y = 0 := archimedeanClass.eq_zero_iff.mpr hy0
    rw [hy0']
    rw [archimedeanClass.eq_zero_iff]
    exact Iff.symm orderTop_eq_top_iff
  · by_cases hxt : x.orderTop = ⊤
    · rw [hxt]
      have hx0 : x = 0 := orderTop_eq_top_iff.mp hxt
      have hx0' : archimedeanClass.mk x = 0 := archimedeanClass.eq_zero_iff.mpr hx0
      rw [hx0']
      rw [eq_comm]
      nth_rw 2 [eq_comm]
      rw [archimedeanClass.eq_zero_iff]
      exact Iff.symm orderTop_eq_top_iff
    · have hy0 : y ≠ 0 := by exact ne_zero_iff_orderTop.mpr hyt
      have hx0 : x ≠ 0 := by exact ne_zero_iff_orderTop.mpr hxt
      rw [archimedeanClass.eq]
      constructor
      · intro ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩
        by_contra!
        obtain hxy|hxy := lt_or_gt_of_ne this
        · sorry
        · sorry
      · sorry




variable {M: Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [DivisibleBy M ℕ]

variable (M) in
structure SubEmbedding where
  f : M →ₗ.[ℚ] HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ
  hdomain : ∀ A : archimedeanClass M, ∀ a ∈ archimedeanGrade A, a ∈ f.domain

  strictMono : StrictMono f
  anchor : ∀ A : archimedeanClass M, ∀ a : M, (ha : a ∈ archimedeanGrade A) →
    (f ⟨a, hdomain A a ha⟩).coeff =
    fun i ↦ if i.val = A then archimedeanGrade.embedReal_linear A ⟨a, ha⟩ else 0

  range_cut : ∀ x ∈ Set.range f, ∀ c : {A : archimedeanClass M // A ≠ 0},
    (HahnSeries.cut _ _ c) x ∈ Set.range f

noncomputable
def SubEmbedding.to_orderAddMonoidHom (e : SubEmbedding M) :
    e.f.domain →+o HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ where
  toFun := e.f
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [← LinearPMap.map_add]
  monotone' := e.strictMono.monotone

theorem SubEmbedding.eq_orderAddMonoidHom {e : SubEmbedding M} (x : e.f.domain) :
    e.f x = e.to_orderAddMonoidHom x := by rfl

theorem SubEmbedding.orderTop_eq_class (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    (hx0 : archimedeanClass.mk x ≠ 0) :
    (e.f ⟨x, hx⟩).orderTop = WithTop.some (⟨archimedeanClass.mk x, hx0⟩) := by

  have : Nontrivial (archimedeanGrade (archimedeanClass.mk x)) :=
      archimedeanGrade.nontrivial_of_nonzero hx0
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : archimedeanGrade (archimedeanClass.mk x))
  have hmkeq: archimedeanClass.mk x' = archimedeanClass.mk x := by
    refine archimedeanGrade.mem_class_of_nonzero hx0 hx'mem ?_
    simpa using hx'0
  have hclasseq : archimedeanClass.mk (⟨x', e.hdomain _ _ hx'mem⟩ : e.f.domain)
      = archimedeanClass.mk ⟨x, hx⟩ := by
    rw [archimedeanClass.eq] at hmkeq ⊢
    exact hmkeq

  obtain h := (archimedeanClass.map_mk_eq (to_orderAddMonoidHom e) hclasseq).symm
  rw [← eq_orderAddMonoidHom, ← eq_orderAddMonoidHom] at h

  have hfx0 : e.f ⟨x, hx⟩ ≠ 0 := by
    have : (0 : HahnSeries { A: archimedeanClass M // A ≠ 0 } ℝ) = e.f 0 := by simp
    rw [this]
    apply e.strictMono.injective.ne_iff.mpr
    simpa using hx0

  rw [HahnSeries.archimedeanClass_eq_iff] at h

  have : (e.f ⟨x', e.hdomain _ _ hx'mem⟩).orderTop = WithTop.some ⟨archimedeanClass.mk x',
      hmkeq.symm ▸ hx0⟩ := by
    apply HahnSeries.orderTop_eq_of_le
    · simp only [ne_eq, HahnSeries.mem_support]
      rw [e.anchor (archimedeanClass.mk x') x' (hmkeq.symm ▸ hx'mem)]
      simp only [↓reduceIte]
      apply (LinearMap.map_eq_zero_iff _ (Archimedean.embedReal_injective _)).ne.mpr
      simpa using hx'0
    · intro g' hg
      contrapose! hg
      simp only [ne_eq, HahnSeries.mem_support, Decidable.not_not]
      rw [e.anchor (archimedeanClass.mk x') x' (hmkeq.symm ▸ hx'mem)]
      simp only [ne_eq, ite_eq_right_iff]
      intro hg'
      obtain hg := Subtype.eq_iff.ne.mp hg.ne
      simp only [ne_eq] at hg
      rw [hg'] at hg
      simp at hg
  rw [this] at h
  rw [h]
  simpa using hmkeq

theorem SubEmbedding.coeff_nonzero_at_class (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    (hx0 : archimedeanClass.mk x ≠ 0) :
    (e.f ⟨x, hx⟩).coeff ⟨archimedeanClass.mk x, hx0⟩ ≠ 0 := by
  apply HahnSeries.coeff_orderTop_ne
  rw [SubEmbedding.orderTop_eq_class e hx hx0]


theorem SubEmbedding.coeff_zero_of_class_gt (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    {A : archimedeanClass M} (hA : A < archimedeanClass.mk x) :
    (e.f ⟨x, hx⟩).coeff ⟨A, archimedeanClass.ne_zero_of_lt hA⟩ = 0 := by
  by_cases hx0 : x = 0
  · have : (⟨x, hx⟩ : e.f.domain) = 0 := by
      simp [hx0]
    rw [this]
    simp
  · have hx0' : archimedeanClass.mk x ≠ 0 := archimedeanClass.eq_zero_iff.ne.mpr hx0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [SubEmbedding.orderTop_eq_class e hx hx0']
    simpa using hA

def SubEmbedding.nhds (e : SubEmbedding M) (x : M) (A : archimedeanClass M) : Set M :=
  {y : M | y ∈ e.f.domain ∧ A < archimedeanClass.mk (x - y)}

theorem SubEmbedding.nhds_anti (e : SubEmbedding M) (x : M) : Antitone (nhds e x) := by
  intro a b h
  unfold nhds
  simp only [Set.le_eq_subset, Set.setOf_subset_setOf, and_imp]
  intro u hu hv
  exact ⟨hu, lt_of_le_of_lt h hv⟩

theorem SubEmbedding.map_eq (e : SubEmbedding M) (x : M) {A B1 B2 : archimedeanClass M}
    (hA : A ≠ 0)
    (h1 : A ≤ B1) (h2 : A ≤ B2) {y1 y2 : M} (hy1 : y1 ∈ nhds e x B1) (hy2 : y2 ∈ nhds e x B2) :
    (e.f ⟨y1, hy1.1⟩).coeff ⟨A, hA⟩ =
    (e.f ⟨y2, hy2.1⟩).coeff ⟨A, hA⟩ := by

  apply eq_of_sub_eq_zero
  rw [← Pi.sub_apply, ← HahnSeries.coeff_sub', ← LinearPMap.map_sub]
  apply SubEmbedding.coeff_zero_of_class_gt
  simp only
  have : y1 - y2 = (x - y2) + (-(x - y1)) := by abel
  rw [this]
  refine lt_of_lt_of_le ?_ (archimedeanClass.min_le_mk_add _ _)
  rw [archimedeanClass.mk_neg]
  simp only [lt_inf_iff]
  constructor
  · apply lt_of_le_of_lt h2
    exact hy2.2
  · apply lt_of_le_of_lt h1
    exact hy1.2

open Classical in
noncomputable
def SubEmbedding.eval (e : SubEmbedding M) (x : M) : {A : archimedeanClass M // A ≠ 0} → ℝ :=
  fun A ↦
    if h : (SubEmbedding.nhds e x A).Nonempty then
      (e.f ⟨h.choose, h.choose_spec.1⟩).coeff A
    else
      0

theorem SubEmbedding.eval_eq (e : SubEmbedding M) (x : M) {A B : archimedeanClass M}
    (hA : A ≠ 0)
    (hAB : A ≤ B) {y : M} (hy : y ∈ nhds e x B) :
    eval e x ⟨A, hA⟩ =
    (e.f ⟨y, hy.1⟩).coeff ⟨A, hA⟩ := by

  have hnonempty : (nhds e x A).Nonempty := by
    refine Set.Nonempty.mono ?_ (Set.nonempty_of_mem hy)
    exact nhds_anti _ _ hAB

  unfold eval
  simp only [hnonempty, ↓reduceDIte]
  symm
  apply map_eq _ _ hA hAB (le_refl A) hy (Exists.choose_spec _)


theorem SubEmbedding.eval_isWF_support (e : SubEmbedding M) (x : M) :
    (eval e x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra!
  obtain ⟨seq, ⟨hanti, hmem⟩⟩ := this

  have hnonempty : (nhds e x (seq 0).val).Nonempty := by
    obtain hmem := hmem 0
    contrapose hmem with hempty
    simp only [ne_eq, Function.mem_support, Decidable.not_not]
    unfold eval
    simp [hempty]
  obtain ⟨y, hy⟩ := hnonempty

  have hmem' : ∀ n : ℕ , seq n ∈ Function.support ((e.f ⟨y, hy.1⟩).coeff) := by
    intro n
    obtain hmem := hmem n
    simp only [Function.mem_support] at hmem ⊢
    convert hmem using 1
    symm
    apply SubEmbedding.eval_eq e x _ (le_refl _)
    apply Set.mem_of_mem_of_subset hy
    apply SubEmbedding.nhds_anti
    simp only [Subtype.coe_le_coe]
    apply hanti.le_iff_le.mpr
    simp

  obtain hwf := (e.f ⟨y, hy.1⟩).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simp only [not_forall, ne_eq, Decidable.not_not, not_exists, exists_prop, Set.not_not_mem]
  use seq
  exact ⟨hanti, hmem'⟩

noncomputable
def SubEmbedding.eval_hahn (e : SubEmbedding M) (x : M) :
    HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ where
  coeff := SubEmbedding.eval e x
  isPWO_support' := (eval_isWF_support e x).isPWO

theorem SubEmbedding.eval_ne_of_not_mem (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain)
    (z : e.f.domain) :
    e.eval_hahn x ≠ e.f z := by

  by_contra! h

  have h1 (y : e.f.domain) (hxy : x ≠ y.val) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (z.val - y.val) := by

    have (A : {A : archimedeanClass M // A ≠ 0})
      (hA : A.val < archimedeanClass.mk (x - y.val))  :
      (e.eval_hahn x).coeff A = (e.f y).coeff A := by
      apply SubEmbedding.eval_eq e x _ (le_refl _)
      unfold nhds
      simpa using hA

    conv at this =>
      intro A hA
      rw [h]
      rw [← sub_eq_zero]
      rw [← HahnSeries.coeff_sub]
      rw [← LinearPMap.map_sub]

    have hxy' : archimedeanClass.mk (x - y.val) ≠ 0 := by
      apply archimedeanClass.eq_zero_iff.ne.mpr
      exact sub_ne_zero_of_ne hxy

    have : WithTop.some (⟨archimedeanClass.mk (x - y.val), hxy'⟩ : {A : archimedeanClass M // A ≠ 0}) ≤
        (e.f (z - y)).orderTop := by
      contrapose! this
      have hsome : (e.f (z - y)).orderTop ≠ ⊤ := LT.lt.ne_top this
      rw [WithTop.ne_top_iff_exists] at hsome
      obtain ⟨order, horder⟩ := hsome
      use order
      constructor
      · rw [← horder] at this
        simpa using this
      · apply HahnSeries.coeff_orderTop_ne
        exact horder.symm

    by_cases hyz0 : archimedeanClass.mk (z - y).val = 0
    · simp only [ne_eq, AddSubgroupClass.coe_sub] at hyz0
      rw [hyz0]
      apply archimedeanClass.nonpos
    · rw [SubEmbedding.orderTop_eq_class e _ hyz0] at this
      simpa using this

  have h2 (y : e.f.domain) (hxy : x ≠ y.val) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (x - z.val) := by
    have : x - z.val = x - y.val + -(z.val - y.val) := by abel
    rw [this]
    refine le_trans ?_ (archimedeanClass.min_le_mk_add _ _)
    rw [archimedeanClass.mk_neg]
    simpa using h1 y hxy

  have h3 (y : e.f.domain) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (x - z.val) := by
    apply h2
    contrapose! hx
    rw [hx]
    simp


  sorry

theorem SubEmbedding.eval_lt (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain)
    (y : e.f.domain) (h : x < y.val) :
    e.eval_hahn x < e.f y := by
  unfold eval_hahn
  rw [HahnSeries.lt_iff]
  simp only

  have h0 : archimedeanClass.mk (x - y.val) ≠ 0 :=
    archimedeanClass.eq_zero_iff.ne.mpr <| sub_ne_zero_of_ne h.ne

  use ⟨archimedeanClass.mk (x - y.val), h0⟩
  constructor
  · intro j hj
    have hy : y.val ∈ e.nhds x j.val := by
      unfold nhds
      simpa using hj
    rw [SubEmbedding.eval_eq e x j.prop (le_refl _) hy]
  · have hnonempty : (e.nhds x (archimedeanClass.mk (x - y.val))).Nonempty := by sorry
    obtain ⟨z, hz⟩ := hnonempty
    rw [SubEmbedding.eval_eq e x h0 (le_refl _) hz]

    unfold nhds at hz
    simp only [Set.mem_setOf_eq] at hz

    have hzyclass : archimedeanClass.mk (z - y.val) = archimedeanClass.mk (x - y.val) := by
      symm
      have : z - y.val = x - y.val + (z - x) := by abel
      rw [this]
      apply archimedeanClass.mk_eq_mk_self_add_of_mk_lt
      rw [← archimedeanClass.mk_neg (z - x), neg_sub]
      exact hz.2

    have hzy0 : archimedeanClass.mk (z - y.val) ≠ 0 := hzyclass.symm ▸ h0

    have hzy : ⟨z, hz.1⟩ < y := by
      show z < y.val
      apply (sub_lt_sub_iff_right x).mp
      refine archimedeanClass.lt_of_mk_lt_mk ?_ (sub_nonneg_of_le h.le)
      rw [← archimedeanClass.mk_neg (z - x), neg_sub]
      rw [← archimedeanClass.mk_neg (y.val - x), neg_sub]
      exact hz.2

    have hzy := e.strictMono.lt_iff_lt.mpr hzy


    rw [HahnSeries.lt_iff] at hzy
    obtain ⟨i, hj, hi⟩ := hzy
    have hieq : i = ⟨archimedeanClass.mk (x - y.val), h0⟩ := by
      apply le_antisymm
      · by_contra! hlt
        obtain hj := hj ⟨archimedeanClass.mk (x - y.val), h0⟩ hlt
        obtain hj := sub_eq_zero_of_eq hj
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub] at hj
        simp_rw [← hzyclass] at hj
        contrapose! hj
        apply SubEmbedding.coeff_nonzero_at_class
      · contrapose! hi
        apply le_of_eq
        simp_rw [← hzyclass] at hi
        apply eq_of_sub_eq_zero
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub]
        apply coeff_zero_of_class_gt
        rw [← archimedeanClass.mk_neg, neg_sub]
        exact hi
    rw [hieq] at hi
    exact hi

noncomputable
abbrev SubEmbedding.ext_fun (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) :
    M →ₗ.[ℚ] HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ :=
  LinearPMap.supSpanSingleton e.f x (SubEmbedding.eval_hahn e x) hx


/-- TODO: generalize this-/
instance (Γ : Type*) [LinearOrder Γ] : OrderedSMul ℚ (HahnSeries Γ ℝ) := OrderedSMul.mk' (by
  intro a b c hab hc
  apply le_of_lt
  rw [HahnSeries.lt_iff] at ⊢ hab
  obtain ⟨i, hj, hi⟩ := hab
  use i
  constructor
  · intro j hji
    obtain hj := hj j hji
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul]
    rw [hj]
  · rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul]
    exact smul_lt_smul_of_pos_left hi hc

)

instance : OrderedSMul ℚ M := OrderedSMul.mk' (by
  intro a b c hab hc
  rw [DivisibleBy.rat_smul_eq, DivisibleBy.rat_smul_eq]
  apply (nsmul_le_nsmul_iff_left' (show c.den ≠ 0 by simp)).mp
  rw [DivisibleBy.div_cancel _ (by simp), DivisibleBy.div_cancel _ (by simp)]
  apply zsmul_le_zsmul_right
  · apply le_of_lt
    exact Rat.num_pos.mpr hc
  · exact hab.le

)

theorem SubEmbedding.ext_fun_strictMono (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) :
    StrictMono (ext_fun e hx) := by

  intro z y hxy
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hxy := sub_pos.mpr hxy
  obtain hxymem := (y - z).prop
  nth_rw 1 [LinearPMap.domain_supSpanSingleton] at hxymem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxymem
  have : y - z = ⟨a + b, hab.symm ▸ (y - z).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hxy

  have habpos : 0 < a + b := by exact hxy

  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [← hc]
  rw [← hc] at habpos
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]

  rw [← sub_neg_eq_add, ← neg_smul, sub_pos] at habpos ⊢
  by_cases hc0 : c = 0
  · rw [hc0] at habpos ⊢
    simp only [zero_smul, ne_eq, neg_zero] at habpos ⊢
    sorry
  · have : a = (-c) • ((-c)⁻¹ • a) := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ (neg_ne_zero.mpr hc0)]
      simp
    rw [this] at habpos
    have : e.f ⟨a, ha⟩ = (-c) • ((-c)⁻¹ • e.f ⟨a, ha⟩) := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ (neg_ne_zero.mpr hc0)]
      simp
    rw [this, ← LinearPMap.map_smul]

    have : (-c)⁻¹ • (⟨a, ha⟩ : e.f.domain) = ⟨(-c)⁻¹ • a,
      Submodule.smul_mem e.f.domain (-c)⁻¹ ha⟩ := rfl
    rw [this]

    obtain hcneg|hcpos := lt_or_gt_of_ne hc0
    · have : 0 < -c := Left.neg_pos_iff.mpr hcneg
      refine smul_lt_smul_of_pos_left ?_ this
      obtain h := lt_of_smul_lt_smul_left habpos this.le
      apply SubEmbedding.eval_lt e hx
      exact h
    · have : -c < 0 := neg_neg_iff_pos.mpr hcpos
      refine smul_lt_smul_of_neg_left ?_ this
      obtain h := lt_of_smul_lt_smul_of_nonpos habpos this.le
      sorry


noncomputable
def SubEmbedding.ext (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) : SubEmbedding M where
  f := ext_fun e hx
  hdomain := sorry
  strictMono := ext_fun_strictMono e hx
  anchor :=

    sorry

  range_cut := sorry
