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
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Qify


section Patch

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


end Patch


variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

variable (M) in
@[to_additive archimedeanEquiv]
def mulArchimedeanEquiv : Setoid M where
  r (a b) := (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n)
  iseqv := {
    refl (a) := ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩
    symm (h) := h.symm
    trans := by
      intro a b c ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩
      refine ⟨⟨m' * m, by simp [hm0, hm0'], ?_⟩, ⟨n * n', by simp [hn0, hn0'], ?_⟩⟩
      · refine le_trans hm ?_
        rw [pow_mul]
        exact pow_le_pow_left' hm' m
      · refine le_trans hn' ?_
        rw [pow_mul]
        exact pow_le_pow_left' hn n'
  }

variable (M) in
@[to_additive archimedeanClass]
def mulArchimedeanClass := Quotient (mulArchimedeanEquiv M)


namespace mulArchimedeanClass

@[to_additive]
def mk (a : M) : mulArchimedeanClass M := Quotient.mk'' a

@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk''_surjective

@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr mk_surjective

@[to_additive]
noncomputable
def out (A : mulArchimedeanClass M) : M := Quotient.out A

@[to_additive (attr := simp)]
theorem out_eq (A : mulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive]
theorem eq {a b : M} :
    mk a = mk b ↔ (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n) := Quotient.eq''

@[to_additive (attr := simp)]
theorem mk_out (a : M) :
    (∃ m, m ≠ 0 ∧ |(mk a).out|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |a|ₘ ≤ |(mk a).out|ₘ ^ n) := eq.mp (by simp)

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = mk a := by
  rw [eq]
  exact ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩

@[to_additive (attr := simp)]
theorem mk_mabs (a : M) : mk |a|ₘ = mk a := by
  rw [eq]
  exact ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩


variable (M) in
@[to_additive]
instance instOne : One (mulArchimedeanClass M) := ⟨mk 1⟩

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one : mk (1 : M) = 1 := rfl

@[to_additive (attr := simp)]
theorem eq_one_iff {a : M} : mk a = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← mk_one, eq] at h
    obtain ⟨⟨_, _, hm⟩, _⟩ := h
    simpa using hm
  · intro h
    rw [h, mk_one]

variable (M) in
@[to_additive (attr := simp)]
theorem one_out : (1 : mulArchimedeanClass M).out = 1 := by
  rw [← eq_one_iff, out_eq]

variable (M) in
@[to_additive]
noncomputable
instance instLinearOrder : LinearOrder (mulArchimedeanClass M) :=
  LinearOrder.lift' (fun A ↦ OrderDual.toDual |A.out|ₘ) (by
    intro A B
    simp only [EmbeddingLike.apply_eq_iff_eq]
    intro h
    simpa using congr_arg mk h
  )

@[to_additive]
theorem le (A B : mulArchimedeanClass M) : A ≤ B ↔ |B.out|ₘ ≤ |A.out|ₘ := by rfl

@[to_additive]
theorem lt (A B : mulArchimedeanClass M) : A < B ↔ |B.out|ₘ < |A.out|ₘ := by rfl

@[to_additive]
theorem le_one (A : mulArchimedeanClass M) : A ≤ 1 := by
  rw [le]
  simp

variable (M) in
@[to_additive]
noncomputable
instance instOrderTop : OrderTop (mulArchimedeanClass M) where
  top := 1
  le_top := le_one

@[to_additive]
theorem mk_lt_mk {a b : M} : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := by
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := mk_out a
  obtain ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩ := mk_out b
  constructor
  · intro h k
    by_cases hk0 : k = 0
    · rw [hk0]
      simp only [pow_zero, one_lt_mabs, ne_eq]
      contrapose! h
      rw [h]
      simpa using le_one (mk b)
    · have hne : ¬ mk a = mk b := ne_of_lt h
      rw [eq] at hne
      simp only [not_and, not_exists, not_le, forall_exists_index] at hne
      by_contra!
      obtain hne' := hne k ⟨hk0, this⟩ (m * n') (by simp [hn0', hm0])
      rw [lt] at h
      contrapose! hne'
      apply le_of_lt
      apply lt_of_le_of_lt hn'
      rw [pow_mul]
      rw [pow_lt_pow_iff_left' hn0']
      apply lt_of_lt_of_le h
      exact hm
  · intro h
    rw [lt]
    rw [← pow_lt_pow_iff_left' hn0]
    rw [← pow_le_pow_iff_left' hn0] at hm'
    apply lt_of_le_of_lt hm'
    rw [← pow_mul]
    exact lt_of_lt_of_le (h (m' * n)) hn


variable (M) in
@[to_additive]
theorem mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr hb] at h
  simpa using h

variable (M) in
@[to_additive]
theorem mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]
theorem mk_le_mk_self_mul_of_mk_eq {a b : M} (hab : mk a = mk b) : mk a ≤ mk (a * b) := by
  by_contra! h
  obtain h2 := hab ▸ h
  obtain h1 := mk_lt_mk.mp h  2
  obtain h2 := mk_lt_mk.mp h2  2
  rw [pow_two] at h1 h2
  have h1 := lt_of_lt_of_le h1 (mabs_mul _ _)
  have h2 := lt_of_lt_of_le h2 (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right] at h1 h2
  have := h1.trans h2
  simp at this

@[to_additive]
theorem mk_eq_mk_self_mul_of_mk_lt {a b : M} (h : mk a < mk b) : mk a = mk (a * b) := by
  obtain h := mk_lt_mk.mp h
  apply eq.mpr
  constructor
  · use 2
    constructor
    · simp
    · apply (mabs_mul' _ b).trans
      rw [mul_comm b a, pow_two]
      simp only [mul_le_mul_iff_right]
      apply le_of_mul_le_mul_left' (a := |b|ₘ)
      rw [mul_comm a b]
      refine le_trans ?_ (mabs_mul' a b)
      obtain h := (h 2).le
      rw [pow_two] at h
      exact h
  · use 2
    constructor
    · simp
    · apply (mabs_mul _ _).trans
      rw [pow_two]
      simp only [mul_le_mul_iff_left]
      simpa using (h 1).le

@[to_additive]
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  obtain hab|hab|hab := lt_trichotomy (mk a) (mk b)
  · simp only [inf_le_iff]
    left
    exact (mk_eq_mk_self_mul_of_mk_lt hab).le
  · rw [← hab]
    simpa using mk_le_mk_self_mul_of_mk_eq hab
  · simp only [inf_le_iff]
    right
    rw [mul_comm]
    exact (mk_eq_mk_self_mul_of_mk_lt hab).le

@[to_additive]
theorem Ioi_nonempty {A : mulArchimedeanClass M} (hA : A ≠ 1):
    (UpperSet.Ioi A).carrier.Nonempty := by
  use 1
  simpa using lt_of_le_of_ne (le_one _) hA

@[to_additive]
theorem archimedean_of_mk_eq_mk (h : ∀ (a b : M), a ≠ 1 → b ≠ 1 → mk a = mk b) :
    MulArchimedean M where
  arch := by
    intro x y hy
    by_cases hx : x ≤ 1
    · use 0
      simpa using hx
    · have hx : 1 < x := lt_of_not_ge hx
      have hxy : mk x = mk y := by
        apply h x y hx.ne.symm hy.ne.symm
      obtain ⟨⟨m, _, hm⟩, _⟩ := (mulArchimedeanClass.eq).mp hxy
      use m
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact hm


end mulArchimedeanClass
