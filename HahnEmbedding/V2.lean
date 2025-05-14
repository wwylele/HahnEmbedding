import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Disjoint
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Order.Zorn
import Mathlib.Order.UpperLower.Closure
import Mathlib.LinearAlgebra.Span.Basic

variable {R : Type*} {M : Type*} [Field R] [AddCommGroup M] [Module R M]
    {ι : Type*} [LinearOrder ι] (f : ι → Submodule R M)

structure PartialTower where
  domain : Set ι
  g : ι → Submodule R M
  antitone : AntitoneOn g domain
  is_compl : ∀ i ∈ domain, IsCompl (f i) (g i)
  garbage : ∀ i ∉ domain, g i = ⊥

instance : LE (PartialTower f) where
  le (a b) := a.domain ⊆ b.domain ∧ ∀ i ∈ a.domain, a.g i = b.g i

instance : IsRefl (PartialTower f) (· ≤ ·) where
  refl (a) := by
    constructor
    · rfl
    · intro x hx
      rfl

theorem PartialTowerTrans {a b c : PartialTower f} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  constructor
  · exact Set.Subset.trans hab.1 hbc.1
  · intro i hi
    obtain hab' := hab.2 i hi
    obtain hbc' := hbc.2 i (Set.mem_of_mem_of_subset hi hab.1)
    exact hab'.trans hbc'

theorem PartialTowerChain (towers : Set (PartialTower f)) (hchain : IsChain (· ≤ ·) towers) :
    ∃ (ub : PartialTower f), ∀ a ∈ towers, a ≤ ub := by
  classical
  use {
    domain := ⋃ tower ∈ towers, tower.domain
    g (i) :=
      if h : i ∈ ⋃ tower ∈ towers, tower.domain then
        (Set.mem_iUnion.mp h).choose.g i
      else
        ⊥
    antitone := by
      intro i hi j hj hij
      simp only [↓reduceDIte, hi, hj]
      obtain hi2 := (Set.mem_iUnion.mp hi).choose_spec
      simp only [Set.mem_iUnion, exists_prop] at hi2
      obtain hj2 := (Set.mem_iUnion.mp hj).choose_spec
      simp only [Set.mem_iUnion, exists_prop] at hj2
      have hi' : (Set.mem_iUnion.mp hi).choose ∈ towers := by
        simpa using hi2.1
      have hj' : (Set.mem_iUnion.mp hj).choose ∈ towers := by
        simpa using hj2.1
      obtain hle|hle := hchain.total hi' hj'
      · simp only [Set.mem_iUnion, exists_prop] at hle
        have : (Set.mem_iUnion.mp hi).choose.g i = (Set.mem_iUnion.mp hj).choose.g i := by
          simpa using hle.2 i hi2.2
        rw [this]
        refine (Set.mem_iUnion.mp hj).choose.antitone ?_ ?_ hij
        · obtain hmem := Set.mem_of_mem_of_subset hi2.2 hle.1
          simpa using hmem
        · simpa using hj2.2
      · simp only [Set.mem_iUnion, exists_prop] at hle
        have : (Set.mem_iUnion.mp hj).choose.g j = (Set.mem_iUnion.mp hi).choose.g j := by
          simpa using hle.2 j hj2.2
        rw [this]
        refine (Set.mem_iUnion.mp hi).choose.antitone ?_ ?_ hij
        · simpa using hi2.2
        · obtain hmem := Set.mem_of_mem_of_subset hj2.2 hle.1
          simpa using hmem
    is_compl := by
      intro i hi
      simp only [hi, ↓reduceDIte]
      apply (Set.mem_iUnion.mp hi).choose.is_compl
      obtain hmem := (Set.mem_iUnion.mp hi).choose_spec
      simp only [Set.mem_iUnion, exists_prop] at hmem
      simpa using hmem.2
    garbage := by
      intro i hi
      simp [hi]
  }

  intro tower htower
  constructor
  · exact Set.subset_biUnion_of_mem htower
  · intro i hi
    simp only
    split_ifs with h1
    · obtain hi2 := (Set.mem_iUnion.mp h1).choose_spec
      simp only [Set.mem_iUnion, exists_prop] at hi2
      have hi' : (Set.mem_iUnion.mp h1).choose ∈ towers := by
        simpa using hi2.1
      obtain hle|hle := hchain.total htower hi'
      · simpa using hle.2 i hi
      · symm
        apply hle.2 i
        simpa using hi2.2
    · apply tower.garbage
      contrapose! h1
      exact Set.mem_biUnion htower hi


theorem ComplTower (hf : Monotone f):
    ∃ g : ι → Submodule R M, Antitone g ∧ ∀ i : ι, IsCompl (f i) (g i) := by
  obtain ⟨top, h⟩ := exists_maximal_of_chains_bounded (PartialTowerChain f) (PartialTowerTrans f)
  use top.g

  have univ : Set.univ = top.domain := by

    sorry

  constructor
  · apply antitoneOn_univ.mp
    convert top.antitone
  · intro i
    apply top.is_compl i
    rw [← univ]
    simp


/-

theorem union_of_chain_compl_intersection_of_antichain
    {f : ι → Submodule R M} (hf : Monotone f)
    {g : ι → Submodule R M} (hg : Antitone g)
    (h_compl : ∀ i, IsCompl (f i) (g i)) :
    IsCompl (⨆ i, f i) (⨅ i, g i) := by
  by_cases hNonempty : Nonempty ι
  · constructor
    · intro x hxf hxg
      intro v hv
      have hvf : v ∈ ⨆ i, f i := hxf hv
      have hvg : v ∈ ⨅ i, g i := hxg hv
      rw [Submodule.mem_iSup_of_directed _ (Monotone.directed_le hf)] at hvf
      obtain ⟨i, hfi⟩ := hvf
      rw [Submodule.mem_iInf] at hvg
      obtain hgi := hvg i
      obtain hfg := h_compl i
      simpa using Submodule.disjoint_def.mp hfg.disjoint v hfi hgi
    · intro x hfx hgx
      intro v _
      simp only [iSup_le_iff] at hfx
      sorry
  · have : IsEmpty ι := by exact not_nonempty_iff.mp hNonempty
    rw [iSup_of_empty]
    rw [iInf_of_empty]
    exact isCompl_bot_top
-/
