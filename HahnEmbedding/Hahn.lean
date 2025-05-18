import HahnEmbedding.ArchimedeanSubgroup
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.LinearAlgebra.Span.Defs

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
  domain : Submodule ℚ M
  hdomain : ∀ A : archimedeanClass M, ∀ a ∈ archimedeanGrade A, a ∈ domain

  f : domain →ₗ[ℚ] HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ
  strictMono : StrictMono f
  anchor : ∀ A : archimedeanClass M, ∀ a : M, (ha : a ∈ archimedeanGrade A) →
    (f ⟨a, hdomain A a ha⟩).coeff =
    fun i ↦ if i.val = A then archimedeanGrade.embedReal_linear A ⟨a, ha⟩ else 0

noncomputable
def SubEmbedding.to_orderAddMonoidHom (e : SubEmbedding M) :
    e.domain →+o HahnSeries {A : archimedeanClass M // A ≠ 0} ℝ where
  toFun := e.f
  map_zero' := by simp
  map_add' := by simp
  monotone' := e.strictMono.monotone

theorem SubEmbedding.eq_orderAddMonoidHom {e : SubEmbedding M} (x : e.domain) :
    e.f x = e.to_orderAddMonoidHom x := by rfl

theorem SubEmbedding.coeff_zero_of_class_gt (e : SubEmbedding M) {x : M} (hx : x ∈ e.domain)
    {A : archimedeanClass M} (hA : A < archimedeanClass.mk x) :
    (e.f ⟨x, hx⟩).coeff ⟨A, archimedeanClass.ne_zero_of_lt hA⟩ = 0 := by
  by_cases hx0 : x = 0
  · have : (⟨x, hx⟩ : e.domain) = 0 := by
      simp [hx0]
    rw [this]
    simp
  · have hx0' : archimedeanClass.mk x ≠ 0 := archimedeanClass.eq_zero_iff.ne.mpr hx0

    have : Nontrivial (archimedeanGrade (archimedeanClass.mk x)) :=
      archimedeanGrade.nontrivial_of_nonzero hx0'
    obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : archimedeanGrade (archimedeanClass.mk x))
    have hmkeq: archimedeanClass.mk x' = archimedeanClass.mk x := by
      refine archimedeanGrade.mem_class_of_nonzero hx0' hx'mem ?_
      simpa using hx'0
    have : archimedeanClass.mk (⟨x', e.hdomain _ _ hx'mem⟩ : e.domain)
        = archimedeanClass.mk ⟨x, hx⟩ := by
      rw [archimedeanClass.eq] at hmkeq ⊢
      exact hmkeq

    obtain h := (archimedeanClass.map_mk_eq (to_orderAddMonoidHom e) this).symm
    rw [← eq_orderAddMonoidHom, ← eq_orderAddMonoidHom] at h

    have hfx0 : e.f ⟨x, hx⟩ ≠ 0 := by
      have : (0 : HahnSeries { A: archimedeanClass M // A ≠ 0 } ℝ) = e.f 0 := by simp
      rw [this]
      apply e.strictMono.injective.ne_iff.mpr
      simpa using hx0

    rw [HahnSeries.archimedeanClass_eq_iff] at h

    have : (e.f ⟨x', e.hdomain _ _ hx'mem⟩).orderTop = WithTop.some ⟨archimedeanClass.mk x',
        hmkeq.symm ▸ hx0'⟩ := by
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
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [h]
    simp only [ne_eq, WithTop.coe_lt_coe, Subtype.mk_lt_mk]
    rw [hmkeq]
    exact hA

def SubEmbedding.nhds (e : SubEmbedding M) (x : M) (A : archimedeanClass M) : Set M :=
  {y : M | y ∈ e.domain ∧ A < archimedeanClass.mk (x - y)}

theorem SubEmbedding.map_eq (e : SubEmbedding M) (x : M) {A B1 B2 : archimedeanClass M}
    (h1 : A < B1) (h2 : A < B2) {y1 y2 : M} (hy1 : y1 ∈ nhds e x B1) (hy2 : y2 ∈ nhds e x B2) :
    (e.f ⟨y1, hy1.1⟩).coeff ⟨A, archimedeanClass.ne_zero_of_lt h1⟩ =
    (e.f ⟨y2, hy2.1⟩).coeff ⟨A, archimedeanClass.ne_zero_of_lt h1⟩ := by

  apply eq_of_sub_eq_zero
  rw [← Pi.sub_apply, ← HahnSeries.coeff_sub', ← map_sub]
  apply SubEmbedding.coeff_zero_of_class_gt
  simp only
  have : y1 - y2 = (x - y2) + (-(x - y1)) := by abel
  rw [this]
  refine lt_of_lt_of_le ?_ (archimedeanClass.min_le_mk_add _ _)
  rw [archimedeanClass.mk_neg]
  simp only [lt_inf_iff]
  constructor
  · apply lt_trans h2
    exact hy2.2
  · apply lt_trans h1
    exact hy1.2

open Classical in
noncomputable
def SubEmbedding.eval (e : SubEmbedding M) (x : M) : {A : archimedeanClass M // A ≠ 0} → ℝ :=
  fun A ↦
    if h : (SubEmbedding.nhds e x A).Nonempty then
      (e.f ⟨h.choose, h.choose_spec.1⟩).coeff A
    else
      0

theorem SubEmbedding.eval_IsWF (e : SubEmbedding M) (x : M) :
    (eval e x).support.IsWF := by


  sorry

noncomputable
def SubEmbedding_ext (e : SubEmbedding M) {x : M} (hx : x ∉ e.domain) : SubEmbedding M where
  domain := e.domain ⊔ ℚ ∙ x
  hdomain := by
    intro A a ha
    exact Submodule.mem_sup.mpr ⟨a, e.hdomain A a ha, 0, by simp⟩

  f := by
    let S := ((fun y ↦ archimedeanClass.mk (x - y)) '' e.domain) \ {0}
    have hS : ∀ s ∈ S, ∃ s' ∈ S, s < s' := by
      by_contra!
      obtain ⟨sz, hszmem, hsz⟩ := this
      obtain ⟨z, hzmem, hz⟩ := (Set.mem_image _ _ _).mp ((Set.mem_diff _).mp hszmem).1
      have hxz0 : archimedeanClass.mk (x - z) ≠ 0 := by
        contrapose! hx with h0
        obtain h0' := archimedeanClass.eq_zero_iff.mp h0
        have : x = z := sub_eq_zero.mp h0'
        rw [this]
        exact hzmem

      obtain ⟨⟨v, xz'⟩, ⟨hv, hxz', hvxz⟩, _⟩  := archimedeanGrade.exists_add hxz0 (
        show x - z ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ici (archimedeanClass.mk (x - z))) by
          rw [archimedeanSubgroup.mem_submodule_iff_mem]
          rw [archimedeanSubgroup.mem_iff]
          simp only [UpperSet.mem_Ici_iff, le_refl]
          -- For some reason the following below didn't get simp
          rw [UpperSet.carrier_eq_coe, UpperSet.coe_Ici]
          apply Set.nonempty_Ici
      )
      rw [archimedeanSubgroup.mem_submodule_iff_mem, archimedeanSubgroup.mem_iff (
        archimedeanClass.Ioi_nonempty hxz0)] at hv

      simp at hv hxz' hvxz
      have hxzmem : z + xz' ∈ e.domain := by
        apply Submodule.add_mem
        · exact hzmem
        · exact e.hdomain _ _ hxz'

      by_cases hv0 : archimedeanClass.mk v = 0
      · have hv0' : v = 0 := archimedeanClass.eq_zero_iff.mp hv0
        rw [hv0'] at hvxz
        simp only [zero_add] at hvxz
        obtain hvxz' := sub_eq_iff_eq_add'.mp hvxz.symm
        contrapose! hx
        rw [hvxz']
        exact hxzmem
      · have : Nontrivial (archimedeanGrade (archimedeanClass.mk v)) := by
          apply archimedeanGrade.nontrivial_of_nonzero
          exact hv0
        obtain ⟨⟨v', hvmem'⟩, hv'⟩ := exists_ne (0 : archimedeanGrade (archimedeanClass.mk v))
        have hv0' : v' ≠ 0 := Subtype.eq_iff.ne.mp hv'
        obtain hvmk' := archimedeanGrade.mem_class_of_nonzero hv0 hvmem' hv0'
        have : archimedeanClass.mk v' ∈ S := by
          unfold S
          simp only [Set.mem_diff, Set.mem_image, SetLike.mem_coe, Set.mem_singleton_iff,
            archimedeanClass.eq_zero_iff]
          constructor
          · use z + xz'
            constructor
            · exact hxzmem
            · rw [hvmk']
              congr 1
              rw [← sub_sub]
              rw [← hvxz]
              simp
          · exact hv0'
        obtain hwhat := hsz _ this
        rw [← hz, hvmk'] at hwhat
        obtain hwhat' := hwhat.trans_lt hv
        simp at hwhat'

    have : Nontrivial M := by
      use x, 0
      contrapose! hx
      rw [hx]
      simp

    have hSnonempty : S.Nonempty := by
      obtain ⟨A, hA⟩ := exists_ne (0 : archimedeanClass M)
      have : Nontrivial (archimedeanGrade A) := by
        apply archimedeanGrade.nontrivial_of_nonzero
        exact hA
      obtain ⟨a, ha⟩ := exists_ne (0 : archimedeanGrade A)
      use archimedeanClass.mk (x - a.val)
      unfold S
      simp only [Set.mem_diff, Set.mem_image, SetLike.mem_coe, Set.mem_singleton_iff,
        archimedeanClass.eq_zero_iff]
      constructor
      · use a.val
        constructor
        · apply e.hdomain A
          simp
        · simp
      · contrapose! hx
        obtain hx' := sub_eq_zero.mp hx
        rw [hx']
        apply e.hdomain A
        simp

    have hS' : ∀ s : S, ∃ s' : S, s < s' := by
      intro ⟨s, hs⟩
      obtain ⟨s', hs', hss⟩ := hS s hs
      use ⟨s', hs'⟩
      simpa using hss

    have hSnonempty' : Nonempty S := by
      obtain ⟨s, hs⟩ := hSnonempty
      use s

    /-let rec R (n : ℕ) : S := match n with
    | 0 => hSnonempty'.some
    | n + 1 => (hS' (R n)).choose

    have hRStrictMono : StrictMono R := by
      apply strictMono_nat_of_lt_succ
      intro n
      convert (hS' (R n)).choose_spec-/


    sorry
  strictMono := sorry
  anchor := sorry
