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

import HahnEmbedding.Misc

theorem Rat.mul_den' (q₁ q₂ : ℚ) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [Rat.mul_den]
  symm
  apply (Nat.dvd_iff_div_mul_eq _ _).mp
  apply Nat.gcd_dvd_right

theorem Rat.mul_num' (q₁ q₂ : ℚ) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [Rat.mul_num]
  refine Eq.symm (Int.ediv_mul_cancel ?_)
  rw [← Int.dvd_natAbs]
  refine Int.ofNat_dvd.mpr ?_
  apply Nat.gcd_dvd_left

namespace RootableBy

@[to_additive div_one]
theorem root_one {M : Type*} [Monoid M] [RootableBy M ℕ] (a : M) :
    root a 1 = a := by
  rw [← pow_one (root a 1)]
  rw [root_cancel _ (by simp)]

@[to_additive zero_div]
theorem one_root (M : Type*) [Monoid M] [RootableBy M ℕ] [IsMulTorsionFree M] (n : ℕ) :
    root (1 : M) n = 1 := by
  by_cases h : n = 0
  · rw [h]
    rw [root_zero]
  · apply (pow_left_inj h).mp
    rw [root_cancel _ h]
    simp

@[to_additive div_neg]
theorem root_inv (M : Type*) [Group M] [RootableBy M ℕ] [IsMulTorsionFree M] (a : M) (n : ℕ):
    root a⁻¹ n = (root a n)⁻¹ := by
  by_cases h : n = 0
  · rw [h]
    rw [root_zero, root_zero]
    simp
  · apply pow_left_injective h
    simp only
    rw [root_cancel _ h, inv_pow, root_cancel _ h]

end RootableBy

namespace DivisibleBy

instance instSMul (M : Type*) [AddGroup M] [h : DivisibleBy M ℕ] : SMul ℚ M where
  smul (s : ℚ) (a : M) := div (s.num • a) s.den

theorem rat_smul_eq {M : Type*} [AddGroup M] [h : DivisibleBy M ℕ] (s : ℚ) (a : M) :
  s • a = div (s.num • a) s.den := rfl

instance instModule (M : Type*) [AddCommGroup M] [h : DivisibleBy M ℕ] [IsAddTorsionFree M] :
    Module ℚ M where
  one_smul := by
    intro a
    rw [rat_smul_eq]
    simp only [Rat.num_ofNat, one_smul, Rat.den_ofNat]
    rw [div_one]
  mul_smul := by
    intro x y a
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : (x.den * y.den) ≠ 0)).mp
    nth_rw 1 [Rat.mul_den']
    rw [mul_comm (x * y).den, ← smul_smul, div_cancel _ (by simp)]
    rw [mul_comm x.den, ← smul_smul, div_cancel _ (by simp),
      smul_comm y.den x.num, div_cancel _ (by simp)]
    have : (x.num * y.num).natAbs.gcd (y.den * x.den) • (x * y).num • a =
      ((x.num * y.num).natAbs.gcd (y.den * x.den) : ℤ) • (x * y).num • a := by symm; apply natCast_zsmul
    rw [this, smul_smul, smul_smul, mul_comm y.den, mul_comm _ (x * y).num]
    congr 1
    symm
    apply Rat.mul_num'
  smul_zero := by
    intro a
    rw [rat_smul_eq]
    simp only [smul_zero]
    rw [zero_div]
  smul_add := by
    intro a x y
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : a.den ≠ 0)).mp
    rw [smul_add a.den]
    rw [div_cancel _ (by simp), div_cancel _ (by simp), div_cancel _ (by simp)]
    rw [smul_add]
  add_smul := by
    intro x y a
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : (x.den * y.den * (x + y).den) ≠ 0)).mp
    rw [← smul_smul, div_cancel _ (by simp)]
    rw [mul_comm (x.den * y.den), smul_add]
    nth_rw 2 [mul_comm x.den y.den]
    rw [← mul_assoc, ← mul_assoc, ← smul_smul ((x + y).den * y.den) x.den, ← smul_smul ((x + y).den * x.den) y.den]
    rw [div_cancel _ (by simp), div_cancel _ (by simp)]
    have : (x.den * y.den) • (x + y).num • a = ((x.den * y.den) : ℤ) • (x + y).num • a := by symm; apply natCast_zsmul
    rw [this]
    have : ((x + y).den * y.den) • x.num • a = ((x + y).den * y.den : ℤ) • x.num • a := by symm; apply natCast_zsmul
    rw [this]
    have : ((x + y).den * x.den) • y.num • a = ((x + y).den * x.den : ℤ) • y.num • a := by symm; apply natCast_zsmul
    rw [this]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [mul_assoc ((x + y).den : ℤ), mul_assoc ((x + y).den : ℤ), ← mul_add]
    rw [mul_comm _ (x + y).num, mul_comm ((x + y).den : ℤ), ← mul_assoc]
    rw [mul_comm _ x.num, mul_comm _ y.num]
    apply Rat.add_num_den'
  zero_smul := by
    intro a
    rw [rat_smul_eq]
    simp only [Rat.num_ofNat, zero_smul, Rat.den_ofNat]
    rw [div_one]

end DivisibleBy


section Order

namespace RootableBy

@[to_additive nonneg_div_of_nonneg]
theorem one_le_root_of_one_le {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M]
    [RootableBy M ℕ] {a : M} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ root a n := by
  by_cases hn : n = 0
  · rw [hn, root_zero]
  · apply le_of_pow_le_pow_left' hn
    rw [root_cancel _ hn]
    simpa using ha

@[to_additive nonpos_div_of_nonpos]
theorem le_one_root_of_le_one {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M]
    [RootableBy M ℕ] {a : M} (ha : a ≤ 1) (n : ℕ) : root a n ≤ 1 := by
  by_cases hn : n = 0
  · rw [hn, root_zero]
  · apply le_of_pow_le_pow_left' hn
    rw [root_cancel _ hn]
    simpa using ha

@[to_additive div_le_self]
theorem root_le_self {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M] [RootableBy M ℕ]
    {a : M} {n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) :
    root a n ≤ a := by
  nth_rw 2 [← root_cancel a hn]
  exact le_self_pow (one_le_root_of_one_le ha _) hn

@[to_additive abs_div]
theorem mabs_root {M : Type*} [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] [RootableBy M ℕ]
    (a : M) (n : ℕ) : |root a n|ₘ = root |a|ₘ n := by
  by_cases hn : n = 0
  · rw [hn, root_zero, root_zero]
    simp
  · obtain ha|ha := le_total 1 a
    · obtain h := one_le_root_of_one_le ha n
      rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr h]
    · obtain h := le_one_root_of_le_one ha n
      rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr h]
      rw [root_inv]

end RootableBy

end Order
