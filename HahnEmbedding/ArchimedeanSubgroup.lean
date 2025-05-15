import HahnEmbedding.ArchimedeanClass
import HahnEmbedding.Divisible


variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

@[to_additive archimedeanSubgroup]
def mulArchimedeanSubgroup {s : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) : Subgroup M where
  carrier := mulArchimedeanClass.mk ⁻¹' s.carrier
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage] at ha hb ⊢
    obtain h|h := min_le_iff.mp (mulArchimedeanClass.min_le_mk_mul a b)
    · apply s.upper' h ha
    · apply s.upper' h hb
  one_mem' := by
    simp only [Set.mem_preimage]
    obtain ⟨u, hu⟩ := hs
    simpa using s.upper' (mulArchimedeanClass.le_one u) hu
  inv_mem' := by
    intro a h
    simpa using h

namespace mulArchimedeanSubgroup

@[to_additive]
theorem mem_iff {s : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) (a : M):
    a ∈ mulArchimedeanSubgroup hs ↔ mulArchimedeanClass.mk a ∈ s :=
  Set.mem_preimage

@[to_additive]
theorem anti {s t : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) (ht : t.carrier.Nonempty)
    (hst : s < t) : mulArchimedeanSubgroup ht < mulArchimedeanSubgroup hs := by
  apply lt_of_le_of_ne
  · rw [Subgroup.mk_le_mk]
    refine (Set.preimage_subset_preimage_iff (by simp)).mpr ?_
    simpa using hst.le
  · contrapose! hst with heq
    apply le_of_eq
    unfold mulArchimedeanSubgroup at heq
    simpa [mulArchimedeanClass.mk_surjective] using heq

end mulArchimedeanSubgroup

namespace archimedeanSubgroup

variable {M: Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [DivisibleBy M ℕ]

def toSubmodule {s : UpperSet (archimedeanClass M)} (hs : s.carrier.Nonempty) : Submodule ℚ M := {
  archimedeanSubgroup hs with
  smul_mem' := by
    intro q a ha
    rw [AddSubgroup.mem_carrier, mem_iff] at ha ⊢
    by_cases hq : q.num = 0
    · have : q = 0 := Rat.zero_of_num_zero hq
      rw [this]
      obtain ⟨b, hb⟩ := hs
      simpa using s.upper (archimedeanClass.nonpos b) hb
    · refine Set.mem_of_eq_of_mem ?_ ha
      rw [DivisibleBy.rat_smul_eq]
      rw [archimedeanClass.eq]
      refine ⟨⟨Int.natAbs q.num, by simpa using hq, ?_⟩, ⟨Int.natAbs q.den, by simp, ?_⟩⟩
      · rw [DivisibleBy.abs_div]
        apply le_trans (DivisibleBy.div_le_self (by simp) (by simp))
        rw [abs_zsmul, ← natCast_zsmul]
        exact smul_le_smul_of_nonneg_right (by simp) (by simp)
      · rw [DivisibleBy.abs_div, Int.natAbs_natCast, DivisibleBy.div_cancel _ (by simp), abs_zsmul]
        nth_rw 1 [← one_smul ℤ |a|]
        refine smul_le_smul_of_nonneg_right ?_ (by simp)
        exact Int.one_le_abs hq

}


end archimedeanSubgroup
