import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.UpperLower.Principal
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.Order.CauSeq.Basic
import Mathlib.GroupTheory.Divisible
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.PiLex
import Mathlib.Order.UpperLower.Closure
import Mathlib.GroupTheory.Complement

@[to_additive]
theorem pow_le_self {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {a : M} {n : ℕ} (ha : a ≤ 1) (hn : n ≠ 0) :
  a ^ n ≤ a := by
  simpa using pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.2 hn)

@[to_additive]
theorem pow_le_pow_iff_left' {M : Type*} [Monoid M] [LinearOrder M] [h : MulLeftStrictMono M] [MulRightStrictMono M] {a b : M} {n : ℕ} (hn : n ≠ 0) :
  a ^ n ≤ b ^ n ↔ a ≤ b := by
  constructor
  · apply le_of_pow_le_pow_left' hn
  · intro h
    have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    have : MulRightMono M := mulRightMono_of_mulRightStrictMono M
    apply pow_le_pow_left' h

@[to_additive]
theorem pow_lt_pow_iff_left' {M : Type*} [Monoid M] [LinearOrder M] [h : MulLeftStrictMono M] [MulRightStrictMono M] {a b : M} {n : ℕ} (hn : n ≠ 0) :
  a ^ n < b ^ n ↔ a < b := by
  constructor
  · have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    have : MulRightMono M := mulRightMono_of_mulRightStrictMono M
    apply lt_of_pow_lt_pow_left' n
  · apply pow_lt_pow_left' hn

theorem map_max {α β F: Type*} [LinearOrder α] [LinearOrder β] [FunLike F α β]
      [OrderHomClass F α β] (f : F) (a b : α):
    f (max a b) = max (f a) (f b) := by
  obtain hab|hab := le_total a b
  all_goals
  · obtain hf := OrderHomClass.monotone f hab
    simp [hf, hab]

@[to_additive]
theorem map_mabs {α β F : Type*} [Group α] [Group β] [LinearOrder α] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α):
    f |a|ₘ = |f a|ₘ := by
  unfold mabs
  rw [map_max]
  simp

/-theorem Submodule.exists_decomp {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) :
    ∃! y : M × M, y.1 ∈ U ∧ y.2 ∈ V ∧ y.1 + y.2 = a := by

  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp ha
  use (b, c)
  constructor
  · exact ⟨hb, hc, hbc⟩
  · intro ⟨b', c'⟩
    simp only [Prod.mk.injEq, and_imp]
    intro hb' hc' hbc'
    let p := b - b'
    have hpb : p ∈ U := Submodule.sub_mem U hb hb'
    have hpeq : p = c' - c := by
      unfold p
      apply sub_eq_sub_iff_add_eq_add.mpr
      rw [hbc, add_comm, hbc']
    have hpc : p ∈ V := hpeq ▸ (Submodule.sub_mem V hc' hc)
    obtain hp0 := (Submodule.disjoint_def.mp hdisj) p hpb hpc
    constructor
    · unfold p at hp0
      exact (sub_eq_zero.mp hp0).symm
    · rw [hpeq] at hp0
      exact sub_eq_zero.mp hp0

noncomputable
def Submodule.decomp1 {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) : M :=
  (Submodule.exists_decomp hdisj ha).choose.1

noncomputable
def Submodule.decomp2 {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) : M :=
  (Submodule.exists_decomp hdisj ha).choose.2

theorem Submodule.decomp1_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) :
    Submodule.decomp1 hdisj ha ∈ U :=
  (Submodule.exists_decomp hdisj ha).choose_spec.1.1

theorem Submodule.decomp2_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) :
    Submodule.decomp2 hdisj ha ∈ V :=
  (Submodule.exists_decomp hdisj ha).choose_spec.1.2.1

theorem Submodule.decomp_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V) :
    Submodule.decomp1 hdisj ha + Submodule.decomp2 hdisj ha = a :=
  (Submodule.exists_decomp hdisj ha).choose_spec.1.2.2

theorem Submodule.decomp_unique {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a : M} (ha : a ∈ U ⊔ V)
    {u v : M} (hu : u ∈ U) (hv : v ∈ V) (h : u + v = a) :
    u = Submodule.decomp1 hdisj ha ∧ v = Submodule.decomp2 hdisj ha :=
  Prod.ext_iff.mp ((Submodule.exists_decomp hdisj ha).choose_spec.2 (u, v) ⟨hu, hv, h⟩)

theorem Submodule.decomp1_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a b : M}
    (ha : a ∈ U ⊔ V) (hb : a ∈ U ⊔ V) (hab : a + b ∈ U ⊔ V) :
    Submodule.decomp1 hdisj hab =
    Submodule.decomp1 hdisj ha + Submodule.decomp1 hdisj hb := by


  sorry

theorem Submodule.decomp2_add {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {U V : Submodule R M} (hdisj : Disjoint U V) {a b : M}
    (ha : a ∈ U ⊔ V) (hb : a ∈ U ⊔ V) (hab : a + b ∈ U ⊔ V) :
    Submodule.decomp2 hdisj hab =
    Submodule.decomp2 hdisj ha + Submodule.decomp2 hdisj hb := by


  sorry

/- Returns a larger linear map F such that F v = fv, and F x = f x for x ∈ m  -/
noncomputable
def LinearMap.extend {R M N : Type*} [Field R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    {m : Submodule R M} (f : ↥m →ₗ[R] N) {v : M} (hv : v ∉ m) (fv : N):
    ↥(m ⊔ R ∙ v : Submodule R M) →ₗ[R] N where
  toFun (x) :=
    have hdisj : Disjoint m (R ∙ v) := by
      refine Submodule.disjoint_def.mpr ?_
      intro x hx hxv
      rw [Submodule.mem_span_singleton] at hxv
      obtain ⟨a, ha⟩ := hxv
      by_cases ha0 : a = 0
      · rw [ha0] at ha
        simp only [zero_smul] at ha
        rw [ha]
      · contrapose! hv
        have: v = a⁻¹ • x := (eq_inv_smul_iff₀ ha0).mpr ha
        rw [this]
        exact Submodule.smul_mem m a⁻¹ hx
    have hz := Submodule.mem_span_singleton.mp (Submodule.decomp2_mem hdisj x.prop)
    f ⟨Submodule.decomp1 hdisj x.prop, Submodule.decomp1_mem hdisj x.prop⟩ + (hz.choose) • fv
  map_add' (x1 x2) := by
    simp only [Submodule.coe_add]
    rw [← add_assoc, add_right_comm (f _)]
    rw [← map_add, add_assoc, ← add_smul]
    congr 2
    · simp only [AddMemClass.mk_add_mk, Subtype.mk.injEq]
      convert Submodule.decomp1_add _ _ _ _ using 1


    · have hv0 : v ≠ 0 := by
        contrapose! hv
        rw [hv]
        simp
      apply smul_left_injective _ hv0
      simp only
      rw [add_smul]
      have {x : M} (hx : x ∈ R ∙ v) : (Submodule.mem_span_singleton.mp hx).choose • v = x :=
        (Submodule.mem_span_singleton.mp hx).choose_spec
      rw [this (Submodule.decomp2_mem _ _), this (Submodule.decomp2_mem _ _), this (Submodule.decomp2_mem _ _)]
      --rw [Exists.choose_spec]
      sorry
  map_smul' := sorry
-/
