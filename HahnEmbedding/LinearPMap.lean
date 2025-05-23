import HahnEmbedding.ArchimedeanSubgroup
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Order.WellFoundedSet

abbrev combine {ι : Type*} {R : Type*} {N : Type*}
    [Semiring R] [AddCommMonoid N] [Module R N] [DecidableEq ι] (p : ι → Submodule R N) :
    (Π₀ (i : ι), ↥(p i)) →ₗ[R] ((⨆ i : ι, p i) : Submodule R N) where

  toFun (f) := ⟨((DFinsupp.lsum ℕ) fun (i : ι) => (p i).subtype) f, by
    simp only [DFinsupp.lsum_apply_apply]
    apply Submodule.dfinsuppSumAddHom_mem
    intro i h0
    apply Submodule.mem_iSup_of_mem i
    simp
  ⟩
  map_add' := by
    intro a b
    simp
  map_smul' := by
    intro s a
    simp

theorem combine_surjective
    {ι : Type*} {R : Type*} {N : Type*}
    [Semiring R] [AddCommMonoid N] [Module R N] [DecidableEq ι] (p : ι → Submodule R N) :
    Function.Surjective (combine p) := by

  intro x
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp p x.val).mp x.prop
  use f
  rw [Subtype.eq_iff]
  exact hf

theorem combine_injective
    {ι : Type*} {R : Type*} {N : Type*}
    [Ring R] [AddCommGroup N] [Module R N] [DecidableEq ι] {p : ι → Submodule R N}
    (h : iSupIndep p) :
    Function.Injective (combine p) := by

  intro a b hab
  rw [Subtype.eq_iff] at hab
  exact iSupIndep.dfinsupp_lsum_injective h hab

noncomputable
abbrev decomp {ι : Type*} {R : Type*} {N : Type*}
    [Ring R] [AddCommGroup N] [Module R N] [DecidableEq ι] {p : ι → Submodule R N}
    (h : iSupIndep p) :
    ((⨆ i : ι, p i) : Submodule R N) →ₗ[R] (Π₀ (i : ι), ↥(p i)) :=

  (combine p).inverse
    (Function.surjInv (combine_surjective p))
    (Function.leftInverse_surjInv ⟨combine_injective h, combine_surjective p⟩)
    (Function.rightInverse_surjInv (combine_surjective p))

open Classical in
noncomputable def LinearPMap.iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) :
    E →ₗ.[R] F where
  domain := ⨆ i : ι, (p i).domain
  toFun := LinearMap.comp (DFinsupp.lsum ℕ (fun i ↦ (p i).toFun)) (decomp h)

theorem LinearPMap.domain_iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) :
    (LinearPMap.iSup h).domain = ⨆ i : ι, (p i).domain := by rfl

nonrec
theorem LinearPMap.le_iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) (i : ι):
    (p i).domain ≤ (LinearPMap.iSup h).domain := by
  rw [LinearPMap.domain_iSup]
  apply le_iSup _ i
