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


theorem pow_le_self {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {a : M} {n : ℕ} (ha : a ≤ 1) (hn : n ≠ 0) :
  a ^ n ≤ a := by
  simpa using pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.2 hn)


theorem pow_le_pow_iff_left' {M : Type*} [Monoid M] [LinearOrder M] [h : MulLeftStrictMono M] [MulRightStrictMono M] {a b : M} {n : ℕ} (hn : n ≠ 0) :
  a ^ n ≤ b ^ n ↔ a ≤ b := by
  constructor
  · apply le_of_pow_le_pow_left' hn
  · intro h
    have : MulLeftMono M := mulLeftMono_of_mulLeftStrictMono M
    have : MulRightMono M := mulRightMono_of_mulRightStrictMono M
    apply pow_le_pow_left' h
