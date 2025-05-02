import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Order.Hom.Bounded

section Patch
theorem pow_le_self {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {a : M} {n : ℕ} (ha : a ≤ 1) (hn : n ≠ 0) :
  a ^ n ≤ a := by
  simpa using pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.2 hn)
end Patch

variable {M : Type*}
variable [CommMonoid M] [LinearOrder M]

def PseudoArchimedeanEquiv (x y : M) :=
  ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ (y ≤ x ^ n ∨ y ^ n ≤ x)) ∨
  (y ≤ x ∧ (x ≤ y ^ n ∨ x ^ n ≤ y)))


theorem PseudoArchimedeanEquiv.refl (x : M) : PseudoArchimedeanEquiv x x := by
  unfold PseudoArchimedeanEquiv
  use 1
  simp

theorem PseudoArchimedeanEquiv.symm {x y : M} (h : PseudoArchimedeanEquiv x y) :
    PseudoArchimedeanEquiv y x := by
  unfold PseudoArchimedeanEquiv at h ⊢
  aesop

theorem PseudoArchimedeanEquiv.dual {x y : M} (h : PseudoArchimedeanEquiv x y) : PseudoArchimedeanEquiv (M := Mᵒᵈ) x y := by
  unfold PseudoArchimedeanEquiv at h ⊢
  aesop

variable [IsOrderedMonoid M]

theorem PseudoArchimedeanEquiv.iff_of_one_lt_right (x y : M) (hlt : 1 < y) :
    PseudoArchimedeanEquiv x y ↔
    ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ y ≤ x ^ n) ∨ (y ≤ x ∧ x ≤ y ^ n)) := by
  unfold PseudoArchimedeanEquiv
  constructor
  · intro ⟨n, ⟨hn0, h⟩⟩
    use n
    match n with
    | 0 => exact False.elim (hn0 rfl)
    | m + 1 =>
      obtain h|h := h
      · have h' := and_or_left.mp h
        obtain h'|h' := h'
        · exact ⟨hn0, Or.inl h'⟩
        · by_cases hym : y = y ^ (m + 1)
          · rw [← hym] at h' ⊢
            obtain heq : x = y := le_antisymm h'.1 h'.2
            rw [heq]
            simp
          · absurd h'
            contrapose! hlt with hxy
            obtain hy := le_trans hxy.2 hxy.1
            contrapose! hy
            obtain hpow := Left.one_le_pow_of_le hy.le m
            obtain h := mul_left_mono (a := y) hpow
            simp only [mul_one] at h
            rw [← pow_succ' y m] at h
            exact lt_of_le_of_ne h hym
      · have h' := and_or_left.mp h
        obtain h'|h' := h'
        · exact ⟨hn0, Or.inr h'⟩
        · by_cases hxm : x = x ^ (m + 1)
          · rw [← hxm] at h' ⊢
            obtain heq : x = y := le_antisymm h'.2 h'.1
            rw [heq]
            simp
          · absurd h'
            contrapose! hlt with hxy
            refine le_trans h'.left ?_
            obtain hx := le_trans hxy.2 hxy.1
            contrapose! hx
            obtain hpow := Left.one_le_pow_of_le hx.le m
            obtain h := mul_left_mono (a := x) hpow
            simp only [mul_one] at h
            rw [← pow_succ' x m] at h
            exact lt_of_le_of_ne h hxm
  · aesop

theorem PseudoArchimedeanEquiv.iff_of_right_lt_one (x y : M) (hlt : y < 1) :
    PseudoArchimedeanEquiv x y ↔
    ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ y ^ n ≤ x) ∨ (y ≤ x ∧ (x ^ n ≤ y))) := by
  unfold PseudoArchimedeanEquiv
  constructor
  · obtain h := (PseudoArchimedeanEquiv.iff_of_one_lt_right (M := Mᵒᵈ) x y hlt).mp
    unfold PseudoArchimedeanEquiv at h
    intro ⟨n, ⟨hn0, hn⟩⟩
    obtain ⟨n, ⟨hn0', hn'⟩⟩ := h (by
      use n
      constructor
      · exact hn0
      · symm
        convert hn using 2
        · rw [Or.comm]
          rfl
        · rw [Or.comm]
          rfl
    )
    use n
    constructor
    · exact hn0'
    · exact hn'.symm
  · aesop

theorem PseudoArchimedeanEquiv.one_iff (x : M) : PseudoArchimedeanEquiv x 1 ↔ x = 1 := by
  unfold PseudoArchimedeanEquiv
  constructor
  · intro ⟨n, ⟨h0, h⟩⟩
    rw [one_le_pow_iff h0, pow_le_one_iff h0] at h
    simp only [one_pow, or_self] at h
    obtain h|h := h
    · exact le_antisymm h.1 h.2
    · exact le_antisymm h.2 h.1
  · intro hx
    use 1
    rw [hx]
    simp

theorem PseudoArchimedeanEquiv.le_one {x y : M} (h : PseudoArchimedeanEquiv x y) (hle : y ≤ 1) :
    x ≤ 1 := by
  by_contra! hlt
  unfold PseudoArchimedeanEquiv at h
  obtain ⟨n, ⟨hn0, hn⟩⟩ := h
  have hyx : y < x := lt_of_le_of_lt hle hlt
  have hxy : ¬ x ≤ y := not_le_of_lt hyx
  simp only [hxy, false_and, false_or] at hn
  obtain hn|hn := hn.2
  · obtain hyy := lt_of_lt_of_le hyx hn
    obtain hy := pow_le_self hle hn0
    obtain h := lt_of_lt_of_le hyy hy
    simp at h
  · obtain hxx := lt_of_le_of_lt hn hyx
    obtain hx := le_self_pow (hlt.le) hn0
    obtain h := lt_of_le_of_lt hx hxx
    simp at h

theorem PseudoArchimedeanEquiv.lt_one {x y : M} (h : PseudoArchimedeanEquiv x y) (hlt : y < 1) :
    x < 1 := by
  obtain hle := PseudoArchimedeanEquiv.le_one h hlt.le
  apply lt_of_le_of_ne hle
  contrapose! h
  rw [h]
  obtain hy1 := (not_iff_not.mpr (PseudoArchimedeanEquiv.one_iff y)).mpr (ne_of_lt hlt)
  contrapose! hy1
  exact PseudoArchimedeanEquiv.symm hy1

theorem PseudoArchimedeanEquiv.one_le {x y : M} (h : PseudoArchimedeanEquiv x y) (hle : 1 ≤ y) :
    1 ≤ x :=
  PseudoArchimedeanEquiv.le_one (M := Mᵒᵈ) ((PseudoArchimedeanEquiv.dual) h) hle

theorem PseudoArchimedeanEquiv.one_lt {x y : M} (h : PseudoArchimedeanEquiv x y) (hle : 1 < y) :
    1 < x :=
  PseudoArchimedeanEquiv.lt_one (M := Mᵒᵈ) ((PseudoArchimedeanEquiv.dual) h) hle

theorem PseudoArchimedeanEquiv.trans_of_lt_one {x y z : M} (hy1 : y < 1)
    (hxy : PseudoArchimedeanEquiv x y) (hyz : PseudoArchimedeanEquiv y z) :
    PseudoArchimedeanEquiv x z := by
  obtain hzy := PseudoArchimedeanEquiv.symm hyz
  obtain ⟨m, ⟨hm0, hm⟩⟩ := (PseudoArchimedeanEquiv.iff_of_right_lt_one x y hy1).mp hxy
  obtain ⟨n, ⟨hn0, hn⟩⟩ := (PseudoArchimedeanEquiv.iff_of_right_lt_one z y hy1).mp hzy
  obtain hz1 : z < 1 := PseudoArchimedeanEquiv.lt_one hzy hy1
  apply (PseudoArchimedeanEquiv.iff_of_right_lt_one x z hz1).mpr
  obtain ⟨hzy, hn⟩|⟨hyz, hn⟩ := hn
  · obtain ⟨hxy, hm⟩|⟨hyx, hm⟩ := hm
    · obtain hxz|hxz := le_total x z
      · use m
        constructor
        · exact hm0
        · left
          constructor
          · exact hxz
          · exact (pow_le_pow_left' hzy m).trans hm
      · use n
        constructor
        · exact hn0
        · right
          constructor
          · exact hxz
          · exact (pow_le_pow_left' hxy n).trans hn
    · use m * n
      constructor
      · exact Nat.mul_ne_zero hm0 hn0
      · right
        constructor
        · exact hzy.trans hyx
        · rw [pow_mul]
          exact (pow_le_pow_left' hm n).trans hn
  · obtain ⟨hxy, hm⟩|⟨hyx, hm⟩ := hm
    · use n * m
      constructor
      · exact Nat.mul_ne_zero hn0 hm0
      · left
        constructor
        · exact hxy.trans hyz
        · rw [pow_mul]
          exact (pow_le_pow_left' hn m).trans hm
    · obtain hxz|hxz := le_total x z
      · use n
        constructor
        · exact hn0
        · left
          constructor
          · exact hxz
          · exact hn.trans hyx
      · use m
        constructor
        · exact hm0
        · right
          constructor
          · exact hxz
          · exact hm.trans hyz

theorem PseudoArchimedeanEquiv.trans {x y z : M}
    (hxy : PseudoArchimedeanEquiv x y) (hyz : PseudoArchimedeanEquiv y z) :
    PseudoArchimedeanEquiv x z := by
  obtain hzy := PseudoArchimedeanEquiv.symm hyz
  obtain hy1|hy1|hy1 := lt_trichotomy y 1
  · exact PseudoArchimedeanEquiv.trans_of_lt_one hy1 hxy hyz
  · rw [hy1] at hxy hzy
    obtain hx := (PseudoArchimedeanEquiv.one_iff x).mp hxy
    obtain hz := (PseudoArchimedeanEquiv.one_iff z).mp hzy
    rw [hx, hz]
    exact PseudoArchimedeanEquiv.refl 1
  · exact (PseudoArchimedeanEquiv.dual (M := Mᵒᵈ)) <|
      PseudoArchimedeanEquiv.trans_of_lt_one (M := Mᵒᵈ) hy1
      ((PseudoArchimedeanEquiv.dual) hxy)
      ((PseudoArchimedeanEquiv.dual) hyz)

def PseudoArchimedeanEquiv.equiv : Equivalence (PseudoArchimedeanEquiv (M := M)) where
  refl := PseudoArchimedeanEquiv.refl
  symm := PseudoArchimedeanEquiv.symm
  trans := PseudoArchimedeanEquiv.trans

def PseudoArchimedeanEquiv.setoid : Setoid M where
  r := PseudoArchimedeanEquiv
  iseqv := PseudoArchimedeanEquiv.equiv

def PseudoArchimedeanClass (M : Type*) [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] :=
    Quotient (PseudoArchimedeanEquiv.setoid (M := M))

def PseudoArchimedeanClass.mk (a : M) : PseudoArchimedeanClass M := ⟦a⟧

noncomputable
instance PseudoArchimedeanClass.instLinearOrder : LinearOrder (PseudoArchimedeanClass M) :=
  LinearOrder.lift' Quotient.out (Quotient.out_injective)

theorem PseudoArchimedeanClass.le_def : ∀ (a b : PseudoArchimedeanClass M), a ≤ b ↔ a.out ≤ b.out := by
  intro a b
  rfl

theorem PseudoArchimedeanClass.lt_def : ∀ (a b : PseudoArchimedeanClass M), a < b ↔ a.out < b.out := by
  intro a b
  rfl

theorem PseudoArchimedeanClass.lt_of_lt_of_one_lt_right {a b : M} (h : PseudoArchimedeanClass.mk a < PseudoArchimedeanClass.mk b)
    (hb : 1 < b) : a < b := by
  rw [lt_def] at h
  set a' := Quotient.out (mk a)
  set b' := Quotient.out (mk b)
  have haeq : PseudoArchimedeanEquiv a' a := Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) a
  have hbeq : PseudoArchimedeanEquiv b' b := Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) b
  obtain ⟨n, hn0, hn⟩ := (PseudoArchimedeanEquiv.iff_of_one_lt_right b' b hb).mp hbeq
  obtain ha|ha := le_or_gt a 1
  · exact lt_of_le_of_lt ha hb
  · obtain ⟨m, hm0, hm⟩ := (PseudoArchimedeanEquiv.iff_of_one_lt_right a' a ha).mp haeq
    obtain ⟨hn1, hn2⟩|⟨hn1, hn2⟩ := hn
    · obtain ⟨hm1, hm2⟩|⟨hm1, hm2⟩ := hm
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use m
          constructor
          · exact hm0
          · left
            constructor
            · exact h
            · obtain habpow := pow_le_pow_left' ha'leb' m
              obtain hbb := pow_le_pow_left' hn1 m
              left
              apply hm2.trans habpow |>.trans hbb
        · exact le_of_lt hb'lta'
      · exact lt_of_lt_of_le (lt_of_le_of_lt hm1 h) hn1
    · obtain ⟨hm1, hm2⟩|⟨hm1, hm2⟩ := hm
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use n * m
          constructor
          · exact Nat.mul_ne_zero hn0 hm0
          · left
            constructor
            · exact h
            · left
              obtain habpow := pow_le_pow_left' ha'leb' m
              obtain hbb := pow_le_pow_left' hn2 m
              rw [pow_mul]
              exact hm2.trans <| habpow.trans hbb
        · exact le_of_lt hb'lta'
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use n
          constructor
          · exact hn0
          · left
            constructor
            · exact h
            · left
              exact hm1.trans ha'leb' |>.trans hn2
        · exact le_of_lt hb'lta'

theorem PseudoArchimedeanClass.lt_of_lt_of_right_lt_one {a b : M} (h : PseudoArchimedeanClass.mk a < PseudoArchimedeanClass.mk b)
    (hb : b < 1) : a < b := by
  rw [lt_def] at h
  set a' := Quotient.out (mk a)
  set b' := Quotient.out (mk b)
  have haeq : PseudoArchimedeanEquiv a' a := Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) a
  have hbeq : PseudoArchimedeanEquiv b' b := Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) b
  obtain ⟨n, hn0, hn⟩ := (PseudoArchimedeanEquiv.iff_of_right_lt_one b' b hb).mp hbeq
  obtain ha|ha := le_or_gt 1 a
  · obtain hb' := PseudoArchimedeanEquiv.lt_one hbeq hb
    obtain ha' := PseudoArchimedeanEquiv.one_le haeq ha
    obtain h' := (lt_of_lt_of_le hb' ha').trans h
    simp at h'
  · obtain ⟨m, hm0, hm⟩ := (PseudoArchimedeanEquiv.iff_of_right_lt_one a' a ha).mp haeq
    obtain ⟨hn1, hn2⟩|⟨hn1, hn2⟩ := hn
    · obtain ⟨hm1, hm2⟩|⟨hm1, hm2⟩ := hm
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use m
          constructor
          · exact hm0
          · left
            constructor
            · exact h
            · right
              exact hm2.trans ha'leb' |>.trans hn1
        · exact le_of_lt hb'lta'
      · exact lt_of_lt_of_le (lt_of_le_of_lt hm1 h) hn1
    · obtain ⟨hm1, hm2⟩|⟨hm1, hm2⟩ := hm
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use m * n
          constructor
          · exact Nat.mul_ne_zero hm0 hn0
          · left
            constructor
            · exact h
            · right
              obtain habpow := pow_le_pow_left' ha'leb' n
              obtain haa := pow_le_pow_left' hm2 n
              rw [pow_mul]
              exact haa.trans <| habpow.trans hn2
        · exact le_of_lt hb'lta'
      · contrapose! h
        obtain ha'leb' | hb'lta' := le_or_gt a' b'
        · apply le_of_eq
          unfold a' b' mk
          simp only [Quotient.out_inj, Quotient.eq]
          use n
          constructor
          · exact hn0
          · left
            constructor
            · exact h
            · right
              obtain habpow := pow_le_pow_left' ha'leb' n
              obtain haa := pow_le_pow_left' hm1 n
              exact haa.trans habpow |>.trans hn2
        · exact le_of_lt hb'lta'

theorem PseudoArchimedeanClass.one_mk_out : (PseudoArchimedeanClass.mk (M := M) 1).out = 1 :=
  (PseudoArchimedeanEquiv.one_iff _).mp <| Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) 1


theorem PseudoArchimedeanClass.lt_of_lt {a b : M} (h : PseudoArchimedeanClass.mk a < PseudoArchimedeanClass.mk b) :
    a < b := by
  obtain hb|hb|hb := lt_trichotomy b 1
  · exact PseudoArchimedeanClass.lt_of_lt_of_right_lt_one h hb
  · rw [hb] at h ⊢
    have h : (mk a).out < (mk 1).out := h
    rw [PseudoArchimedeanClass.one_mk_out] at h
    set a' := Quotient.out (mk a)
    have haeq : PseudoArchimedeanEquiv a' a := Quotient.mk_out (s := PseudoArchimedeanEquiv.setoid) a
    exact PseudoArchimedeanEquiv.lt_one haeq.symm h
  · exact PseudoArchimedeanClass.lt_of_lt_of_one_lt_right h hb

theorem PseudoArchimedeanClass.mk_monotone : Monotone (PseudoArchimedeanClass.mk (M := M)) := by
  intro a b h
  contrapose! h
  exact PseudoArchimedeanClass.lt_of_lt h

instance PseudoArchimedeanClass.instOne : One (PseudoArchimedeanClass M) where
  one := PseudoArchimedeanClass.mk 1

theorem PseudoArchimedeanClass.mk_one : PseudoArchimedeanClass.mk (M := M) 1 = 1 := by
  rfl

theorem PseudoArchimedeanClass.one_out : (1 : PseudoArchimedeanClass (M := M)).out = 1 := by
  apply PseudoArchimedeanClass.one_mk_out

theorem PseudoArchimedeanClass.mk_eq_one (a : M) : a = 1 ↔ mk a = 1 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [← PseudoArchimedeanClass.mk_one] at h
    unfold mk at h
    rw [Quotient.eq] at h
    apply (PseudoArchimedeanEquiv.one_iff _).mp h

theorem PseudoArchimedeanClass.mk_lt_one (a : M) : a < 1 ↔ mk a < 1 := by
  rw [← PseudoArchimedeanClass.mk_one]
  constructor
  · intro h
    apply lt_of_le_of_ne
    · exact PseudoArchimedeanClass.mk_monotone h.le
    · contrapose! h
      apply le_of_eq
      exact ((PseudoArchimedeanClass.mk_eq_one _).mpr h).symm
  · exact PseudoArchimedeanClass.mk_monotone.reflect_lt

theorem PseudoArchimedeanClass.mk_one_le (a : M) : 1 ≤ a ↔ 1 ≤ mk a := by
  simpa using (PseudoArchimedeanClass.mk_lt_one a).not

theorem PseudoArchimedeanClass.mk_one_lt (a : M) : 1 < a ↔ 1 < mk a := by
  have eq := PseudoArchimedeanClass.mk_eq_one a
  have le := PseudoArchimedeanClass.mk_one_le a
  constructor
  · intro h
    exact lt_of_le_of_ne' (le.mp h.le) (eq.not.mp h.ne.symm)
  · intro h
    exact lt_of_le_of_ne' (le.mpr h.le) (eq.not.mpr h.ne.symm)

theorem PseudoArchimedeanClass.mk_le_one (a : M) : a ≤ 1 ↔ mk a ≤ 1 := by
  have eq := PseudoArchimedeanClass.mk_eq_one a
  have lt := PseudoArchimedeanClass.mk_lt_one a
  constructor
  · intro h
    obtain h|h := h.lt_or_eq
    · exact (lt.mp h).le
    · exact (eq.mp h).le
  · intro h
    obtain h|h := h.lt_or_eq
    · exact (lt.mpr h).le
    · exact (eq.mpr h).le

-- Group


variable {M N: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]
variable [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

theorem PseudoArchimedeanEquiv.inv {a b : M} (h : PseudoArchimedeanEquiv a b) : PseudoArchimedeanEquiv a⁻¹ b⁻¹ := by
  unfold PseudoArchimedeanEquiv at h ⊢
  obtain ⟨n, h⟩ := h
  use n
  aesop


private instance instSetoid : Setoid M := PseudoArchimedeanEquiv.setoid
theorem PseudoArchimedeanClass.inv_stable (a b : M) (h : a ≈ b) : PseudoArchimedeanClass.mk a⁻¹ = PseudoArchimedeanClass.mk b⁻¹ := by
  obtain h: PseudoArchimedeanEquiv a b := h
  unfold PseudoArchimedeanClass.mk
  apply Quotient.eq.mpr
  exact h.inv

def PseudoArchimedeanClass.inv : PseudoArchimedeanClass M → PseudoArchimedeanClass M :=
  Quotient.lift (PseudoArchimedeanClass.mk ·⁻¹) PseudoArchimedeanClass.inv_stable

theorem PseudoArchimedeanClass.inv_inv (a : PseudoArchimedeanClass M) : a.inv.inv = a := by
  unfold PseudoArchimedeanClass.inv
  unfold PseudoArchimedeanClass.mk
  rw [← Quotient.out_eq a, Quotient.lift_mk, Quotient.lift_mk]
  simp

instance PseudoArchimedeanClass.instInv : InvolutiveInv (PseudoArchimedeanClass M) where
  inv := PseudoArchimedeanClass.inv
  inv_inv := PseudoArchimedeanClass.inv_inv

def PseudoArchimedeanClass.inv_def : ∀ (a : PseudoArchimedeanClass M), a⁻¹ = PseudoArchimedeanClass.inv (M := M) a := by
  intro a
  rfl

def ArchimedeanClass (M : Type*) [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] :=
  {a : PseudoArchimedeanClass M // a ≤ 1}

def ArchimedeanClass.mk (a : M) : ArchimedeanClass M :=
  ⟨PseudoArchimedeanClass.mk (|a|ₘ⁻¹), by
    apply (PseudoArchimedeanClass.mk_monotone (M := M))
    simp
  ⟩

theorem ArchimedeanClass.mk_inv (a : M) : ArchimedeanClass.mk (a⁻¹) = ArchimedeanClass.mk a := by
  unfold ArchimedeanClass.mk
  simp

theorem ArchimedeanClass.mk_mabs (a : M) : ArchimedeanClass.mk |a|ₘ = ArchimedeanClass.mk a := by
  unfold ArchimedeanClass.mk
  simp

instance ArchimedeanClass.instOne : One (ArchimedeanClass M) where
  one := ArchimedeanClass.mk 1

theorem ArchimedeanClass.one_def (M : Type*) [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] :
  (1 : ArchimedeanClass M) = ArchimedeanClass.mk 1 := by rfl

theorem ArchimedeanClass.one_eq : (1 : ArchimedeanClass M).val = 1 := by
  have : (1 : ArchimedeanClass M).val = (PseudoArchimedeanClass.mk |1|ₘ⁻¹) := by rfl
  rw [this]
  have : (1 : PseudoArchimedeanClass M) = (PseudoArchimedeanClass.mk 1) := by rfl
  rw [this]
  simp

theorem ArchimedeanClass.mk_eq_one (a : M) : a = 1 ↔ mk a = 1 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    unfold ArchimedeanClass.mk at h
    obtain h := Subtype.ext_iff_val.mp h
    simp only at h
    rw [ArchimedeanClass.one_eq] at h
    obtain h := (PseudoArchimedeanClass.mk_eq_one _).mpr h
    simpa using h

noncomputable
instance ArchimedeanClass.instLinearOrder : LinearOrder (ArchimedeanClass M) := by
  unfold ArchimedeanClass
  infer_instance

theorem ArchimedeanClass.le_one (u : ArchimedeanClass M) : u ≤ 1 := by
  apply Subtype.coe_le_coe.mp
  rw [ArchimedeanClass.one_eq]
  exact u.prop

theorem ArchimedeanClass.eq_iff (a b : M) :
    ArchimedeanClass.mk a = ArchimedeanClass.mk b ↔
    (∃ n, n ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ n) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n) := by
  unfold ArchimedeanClass.mk PseudoArchimedeanClass.mk
  rw [Subtype.mk_eq_mk, Quotient.eq]
  constructor
  · intro ⟨n, ⟨hn0, hn⟩⟩
    simp only [inv_le_inv_iff, inv_pow] at hn
    obtain ⟨hn1, hn2⟩|⟨hn1, hn2⟩ := hn
    · obtain hn2|hn2 := hn2
      · constructor
        · use 1
          constructor
          · simp
          · simp only [pow_one]
            exact (le_self_pow (by simp) hn0).trans hn2
        · use 1
          aesop
      · constructor
        · use n
        · use 1
          aesop
    · obtain hn2|hn2 := hn2
      · constructor
        · use 1
          aesop
        · use 1
          constructor
          · simp
          · simp only [pow_one]
            exact (le_self_pow (by simp) hn0).trans hn2
      · constructor
        · use 1
          aesop
        · use n
  · intro ⟨⟨m, ⟨hm0, hm⟩⟩, ⟨n, ⟨hn0, hn⟩⟩⟩
    obtain hb0|hb0 := eq_or_lt_of_le (one_le_mabs b)
    · rw [← hb0] at ⊢ hm
      simp only [one_pow, mabs_le_one] at hm
      rw [hm]
      simpa using PseudoArchimedeanEquiv.refl 1
    · have : (mabs b)⁻¹ < 1 := by exact Left.inv_lt_one_iff.mpr hb0
      apply (PseudoArchimedeanEquiv.iff_of_right_lt_one _ _ this).mpr
      use max m n
      constructor
      · aesop
      · simp only [inv_le_inv_iff, inv_pow]
        obtain hab|hab := le_total |a|ₘ |b|ₘ
        · right
          constructor
          · exact hab
          · exact hn.trans <| pow_le_pow_right' (by simp) (by simp)
        · left
          constructor
          · exact hab
          · exact hm.trans <| pow_le_pow_right' (by simp) (by simp)

theorem ArchimedeanClass.lt_iff (a b : M) :
    ArchimedeanClass.mk a < ArchimedeanClass.mk b ↔
    ∀n, |b|ₘ ^ n < |a|ₘ := by
  constructor
  · intro h
    obtain hb0|hb0 := eq_or_lt_of_le (one_le_mabs b)
    · intro n
      rw [← hb0]
      simp only [one_pow, one_lt_mabs, ne_eq]
      contrapose! h
      obtain hb0' := mabs_eq_one.mp hb0.symm
      rw [h, hb0']
    · unfold ArchimedeanClass.mk PseudoArchimedeanClass.mk at h
      rw [Subtype.mk_lt_mk] at h
      obtain h' := PseudoArchimedeanClass.mk_monotone.reflect_lt h
      simp only [inv_lt_inv_iff] at h'
      obtain h'' := ne_of_lt h
      simp only [ne_eq] at h''
      rw [Quotient.eq] at h''
      obtain h'' := (not_iff_not.mpr (PseudoArchimedeanEquiv.iff_of_right_lt_one _ _ (inv_lt_one'.mpr hb0))).mp h''
      simp only [ne_eq, inv_le_inv_iff, inv_pow, not_exists, not_and, not_le, not_or] at h''
      intro n
      by_cases hn0 : n = 0
      · rw [hn0]
        simp only [pow_zero]
        exact hb0.trans h'
      · exact (h'' n hn0).1 h'.le
  · intro h
    apply lt_of_le_of_ne
    · unfold ArchimedeanClass.mk PseudoArchimedeanClass.mk
      rw [Subtype.mk_le_mk]
      apply PseudoArchimedeanClass.mk_monotone
      obtain h := h 1
      simp only [pow_one] at h
      simp only [inv_le_inv_iff]
      exact le_of_lt h
    · contrapose! h
      rw [ArchimedeanClass.eq_iff] at h
      aesop

theorem ArchimedeanClass.mk_mul_self {a b : M} (hab : mk a = mk b) : mk a ≤ mk (a * b) := by
  by_contra! h
  obtain h2 := hab ▸ h
  obtain h1 := (ArchimedeanClass.lt_iff _ _).mp h  2
  obtain h2 := (ArchimedeanClass.lt_iff _ _).mp h2  2
  rw [pow_two] at h1 h2
  have h1 := lt_of_lt_of_le h1 (mabs_mul _ _)
  have h2 := lt_of_lt_of_le h2 (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right] at h1 h2
  have := h1.trans h2
  simp at this

theorem ArchimedeanClass.mk_mul_of_lt {a b : M} (h : mk a < mk b) : mk a = mk (a * b) := by
  obtain h := (ArchimedeanClass.lt_iff _ _).mp h
  apply (ArchimedeanClass.eq_iff _ _).mpr
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

theorem ArchimedeanClass.mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  obtain hab|hab|hab := lt_trichotomy (mk a) (mk b)
  · simp only [inf_le_iff]
    left
    exact (ArchimedeanClass.mk_mul_of_lt hab).le
  · rw [← hab]
    simpa using ArchimedeanClass.mk_mul_self hab
  · simp only [inf_le_iff]
    right
    rw [mul_comm]
    exact (ArchimedeanClass.mk_mul_of_lt hab).le

theorem ArchimedeanClass.mk_mul_of_one_le {a b : M} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  min (mk a) (mk b) = mk (a * b) := by
  obtain lt|eq|gt := lt_trichotomy (mk a) (mk b)
  · rw [← ArchimedeanClass.mk_mul_of_lt lt]
    exact min_eq_left_of_lt lt
  · rw [eq]
    simp only [min_self]
    rw [ArchimedeanClass.eq_iff] at eq
    rw [ArchimedeanClass.eq_iff]
    rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr hb] at eq
    have hab : 1 ≤ a * b := by exact one_le_mul ha hb
    rw [mabs_eq_self.mpr hb, mabs_eq_self.mpr hab]
    obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := eq
    constructor
    · use n
      constructor
      · exact hn0
      · rw [mul_pow]
        refine le_mul_of_le_of_one_le hn ?_
        exact one_le_pow_of_one_le' hb n
    · use m + 1
      constructor
      · exact Ne.symm (Nat.zero_ne_add_one m)
      · rw [pow_add]
        simp only [pow_one, mul_le_mul_iff_right]
        exact hm
  · rw [mul_comm]
    rw [← ArchimedeanClass.mk_mul_of_lt gt]
    exact min_eq_right_of_lt gt

theorem ArchimedeanClass.lt_of_mk_lt_mk {a b : M} (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := (ArchimedeanClass.lt_iff _ _).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

noncomputable
abbrev ArchimedeanClass.out (a : ArchimedeanClass M) : M := a.val.out

theorem ArchimedeanClass.out_injective : Function.Injective (ArchimedeanClass.out (M := M)) := by
  unfold ArchimedeanClass.out
  exact Quotient.out_injective.comp Subtype.val_injective

theorem ArchimedeanClass.one_out : (1 : ArchimedeanClass M).out = 1 := by
  unfold ArchimedeanClass.out
  rw [ArchimedeanClass.one_eq]
  apply PseudoArchimedeanClass.one_out


theorem ArchimedeanClass.out_le_one (a : ArchimedeanClass M) : a.out ≤ 1 := by
  unfold ArchimedeanClass.out
  apply (PseudoArchimedeanClass.mk_le_one _).mpr
  unfold PseudoArchimedeanClass.mk
  rw [Quotient.out_eq]
  exact a.prop

theorem ArchimedeanClass.out_eq_one (a : ArchimedeanClass M) : a.out = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← ArchimedeanClass.one_out] at h
    exact ArchimedeanClass.out_injective h
  · intro h
    rw [h]
    apply ArchimedeanClass.one_out

theorem ArchimedeanClass.out_eq (a : ArchimedeanClass M) : mk a.out = a := by
  unfold ArchimedeanClass.mk PseudoArchimedeanClass.mk
  apply Subtype.eq
  simp only
  rw [Quotient.mk_eq_iff_out]
  use 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_pow, true_and]
  rw [mabs_eq_inv_self.mpr (ArchimedeanClass.out_le_one _)]
  simp

noncomputable
instance ArchimedeanClass.instOrderTop : OrderTop (ArchimedeanClass M) where
  top := 1
  le_top := ArchimedeanClass.le_one

theorem OrderHom.map_max {α β F: Type*} [LinearOrder α] [LinearOrder β] [FunLike F α β]
      [OrderHomClass F α β] (f : F) (a b : α):
    max (f a) (f b) = f (max a b) := by
  obtain hab|hab := le_total a b
  all_goals
  · obtain hf := OrderHomClass.monotone f hab
    simp [hf, hab]

theorem OrderMonoidHom.map_mabs {α β F : Type*} [Group α] [Group β] [LinearOrder α] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α):
    |f a|ₘ = f |a|ₘ := by
  unfold mabs
  rw [← OrderHom.map_max]
  simp

noncomputable
abbrev ArchimedeanClass.orderHomFun {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (a : ArchimedeanClass M) : ArchimedeanClass N :=
  ArchimedeanClass.mk (f a.out)

noncomputable
def ArchimedeanClass.orderHom {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) : ArchimedeanClass M →o ArchimedeanClass N where

  toFun := ArchimedeanClass.orderHomFun f
  monotone' := by
    intro a b h
    contrapose! h
    unfold ArchimedeanClass.orderHomFun at h
    rw [ArchimedeanClass.lt_iff] at h
    rw [← ArchimedeanClass.out_eq a, ← ArchimedeanClass.out_eq b]
    rw [ArchimedeanClass.lt_iff]
    intro n
    obtain h := h n
    contrapose! h
    obtain h := OrderHomClass.monotone f h
    simp only [OrderMonoidHom.toOrderHom_eq_coe, OrderHomClass.coe_coe, map_pow] at h
    rw [← OrderMonoidHom.map_mabs, ← OrderMonoidHom.map_mabs] at h
    exact h

theorem ArchimedeanClass.orderHom_comm_mk {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (a : M):
    ArchimedeanClass.mk (f a) = (ArchimedeanClass.orderHom f) (ArchimedeanClass.mk a) := by
  unfold ArchimedeanClass.orderHom ArchimedeanClass.orderHomFun
  simp
  apply (ArchimedeanClass.eq_iff _ _).mpr
  have a_eq : ArchimedeanClass.mk a = ArchimedeanClass.mk (ArchimedeanClass.mk a).out := by
    rw [ArchimedeanClass.out_eq]
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := (ArchimedeanClass.eq_iff _ _).mp a_eq
  constructor <;> [use m; use n]
  <;> [refine ⟨hm0, ?_⟩; refine ⟨hn0, ?_⟩]
  all_goals
    rw [OrderMonoidHom.map_mabs, OrderMonoidHom.map_mabs]
    rw [← map_pow]
    apply OrderHomClass.monotone
    try exact hm
    try exact hn

theorem ArchimedeanClass.orderHom_one {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) :
    (ArchimedeanClass.orderHom f) 1 = 1 := by
  rw [ArchimedeanClass.one_def]
  rw [← ArchimedeanClass.orderHom_comm_mk]
  simp only [map_one]
  rw [ArchimedeanClass.one_def]

/-def ArchimedeanClass.orderHom_topHom
    {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N] (f : F) :
    TopHom (ArchimedeanClass M) (ArchimedeanClass N) := by sorry-/

theorem ArchimedeanClass.orderHom_surjective {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (h : Function.Surjective f) :
    Function.Surjective (ArchimedeanClass.orderHom f) := by
  intro a
  obtain ⟨b, hb⟩ := h a.out
  use ArchimedeanClass.mk b
  rw [← ArchimedeanClass.orderHom_comm_mk, hb]
  rw [ArchimedeanClass.out_eq]

/-theorem ArchimedeanClass.orderHom_injOn {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (s : Set M)
    (h : ∀ a ∈ s, ∀ b ∈ s, (ArchimedeanClass.mk (f a) = ArchimedeanClass.mk (f b) → ArchimedeanClass.mk a = ArchimedeanClass.mk b)) :
    Set.InjOn (ArchimedeanClass.orderHom f) -/

--------------------------------------------------------------------------

noncomputable
def ArchimedeanClass.classOrderEmbeddingFun (s : Subgroup M) (a : ArchimedeanClass s) :
    ArchimedeanClass M := ArchimedeanClass.mk a.out.val

noncomputable
def ArchimedeanClass.classOrderEmbedding (s : Subgroup M) :
    (ArchimedeanClass s) ↪o (ArchimedeanClass M) where
  toFun := ArchimedeanClass.classOrderEmbeddingFun s
  inj' := by
    intro a b
    unfold ArchimedeanClass.classOrderEmbeddingFun
    nth_rw 2 [← ArchimedeanClass.out_eq a]
    nth_rw 2 [← ArchimedeanClass.out_eq b]
    rw [ArchimedeanClass.eq_iff, ArchimedeanClass.eq_iff]
    intro ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩
    refine ⟨⟨m, hm0, ?_⟩, ⟨n, hn0, ?_⟩⟩
    · simpa using hm
    · simpa using hn
  map_rel_iff' := by
    intro a b
    unfold ArchimedeanClass.classOrderEmbeddingFun
    apply not_iff_not.mp
    simp only [Function.Embedding.coeFn_mk, not_le]
    nth_rw 2 [← ArchimedeanClass.out_eq a]
    nth_rw 2 [← ArchimedeanClass.out_eq b]
    rw [ArchimedeanClass.lt_iff, ArchimedeanClass.lt_iff]
    constructor
    all_goals
    · intro h n
      simpa using h n

theorem ArchimedeanClass.classOrderEmbedding_one (s : Subgroup M) :
    (ArchimedeanClass.classOrderEmbedding s) 1 = 1 := by
  unfold ArchimedeanClass.classOrderEmbedding ArchimedeanClass.classOrderEmbeddingFun
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  rw [ArchimedeanClass.one_out]
  simp only [OneMemClass.coe_one]
  apply ArchimedeanClass.one_def

theorem ArchimedeanClass.classOrderEmbedding_comm_mk (s : Subgroup M) (a : s):
    ArchimedeanClass.mk (a.val) = (ArchimedeanClass.classOrderEmbedding s) (ArchimedeanClass.mk a) := by
  unfold ArchimedeanClass.classOrderEmbedding ArchimedeanClass.classOrderEmbeddingFun
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
  have h : mk a = mk ((mk a).out) := by
    rw [ArchimedeanClass.out_eq]
  rw [ArchimedeanClass.eq_iff] at ⊢ h
  exact h

--------------------------------------------------------------------------------------------------------


def ArchimedeanSubgroup (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] : Subgroup M where
  carrier := ArchimedeanClass.mk ⁻¹' s.carrier
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage] at ha hb ⊢
    obtain h|h := min_le_iff.mp (ArchimedeanClass.mk_mul a b)
    · apply s.upper' h ha
    · apply s.upper' h hb
  one_mem' := by
    simp only [Set.mem_preimage]
    obtain ⟨u, hu⟩ := hempty
    simpa using s.upper' (ArchimedeanClass.le_one u) hu
  inv_mem' := by
    intro a h
    simp [Set.mem_preimage] at h ⊢
    rw [ArchimedeanClass.mk_inv]
    exact h


instance ArchimedeanSubgroup.instLinearOrder
    (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
  LinearOrder (ArchimedeanSubgroup s) := by infer_instance

instance ArchimedeanSubgroup.instIsOrderedMonoid
    (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
  IsOrderedMonoid (ArchimedeanSubgroup s) := by infer_instance

theorem ArchimedeanSubgroup.le (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] (hst : s.carrier ⊆ t.carrier) :
    ArchimedeanSubgroup s ≤ ArchimedeanSubgroup t := by
  unfold ArchimedeanSubgroup
  simp only [Subgroup.mk_le_mk]
  refine (Set.preimage_subset_preimage_iff ?_).mpr ?_
  · intro a h
    use a.val.out
    unfold ArchimedeanClass.mk PseudoArchimedeanClass.mk
    apply Subtype.eq_iff.mpr
    simp only
    rw [mabs_eq_inv_self.mpr (by
      rw [← PseudoArchimedeanClass.one_mk_out]
      exact (PseudoArchimedeanClass.le_def a.val 1).mp a.prop
    )]
    simp only [inv_inv, Quotient.out_eq]
  · exact hst

noncomputable
def ArchimedeanSubgroup.classOrderEmbedding
    (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
  ArchimedeanClass (ArchimedeanSubgroup s) ↪o s.carrier where
  toFun := fun a ↦ ⟨ArchimedeanClass.classOrderEmbedding (ArchimedeanSubgroup s) a, by
    exact Set.mem_preimage.mp a.out.prop
  ⟩
  inj' := by
    intro a b h
    simpa using h
  map_rel_iff' := by simp

noncomputable
def ArchimedeanSubgroup.classOrderIso
    (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    ArchimedeanClass (ArchimedeanSubgroup s) ≃o s.carrier :=
  RelIso.ofSurjective (ArchimedeanSubgroup.classOrderEmbedding s) (by
    intro a
    use ArchimedeanClass.mk ⟨a.val.out, by
      unfold ArchimedeanSubgroup
      simp only [Subgroup.mem_mk, Set.mem_preimage]
      rw [ArchimedeanClass.out_eq]
      exact a.prop
    ⟩
    unfold ArchimedeanSubgroup.classOrderEmbedding
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
    simp_rw [← ArchimedeanClass.classOrderEmbedding_comm_mk]
    apply Subtype.eq
    simp only
    rw [ArchimedeanClass.out_eq]
  )


----------------------------------------------------------------------

abbrev ArchimedeanQuotient (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :=
  M ⧸ ArchimedeanSubgroup s

abbrev ArchimedeanQuotient.mk (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    ArchimedeanQuotient s :=
  a

theorem ArchimedeanQuotient.eq_iff (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] (a b : M) :
    ArchimedeanQuotient.mk s a = ArchimedeanQuotient.mk s b ↔ (ArchimedeanClass.mk (a⁻¹ * b)) ∈ s.carrier := by
  rw [QuotientGroup.eq]
  unfold ArchimedeanSubgroup
  simp

theorem ArchimedeanQuotient.mk_out (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    (ArchimedeanClass.mk (a⁻¹ * (ArchimedeanQuotient.mk s a).out)) ∈ s.carrier := by
  rw [← ArchimedeanQuotient.eq_iff]
  simp

theorem ArchimedeanQuotient.mk_out' (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    (ArchimedeanClass.mk ((ArchimedeanQuotient.mk s a).out⁻¹ * a)) ∈ s.carrier := by
  rw [← ArchimedeanQuotient.eq_iff]
  simp

noncomputable
instance ArchimedeanQuotient.instLinearOrder (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    LinearOrder (ArchimedeanQuotient s) :=
  LinearOrder.lift' (·.out) Quotient.out_injective

theorem ArchimedeanQuotient.le_def (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    ∀ (x y : ArchimedeanQuotient s), x ≤ y ↔ x.out ≤ y.out := by
  intro x y
  rfl

theorem ArchimedeanQuotient.lt_def (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    ∀ (x y : ArchimedeanQuotient s), x < y ↔ x.out < y.out := by
  intro x y
  rfl

noncomputable
def ArchimedeanQuotient.orderMonoidHom (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    (M →*o ArchimedeanQuotient s) := {
  (QuotientGroup.mk' (ArchimedeanSubgroup s) : M →* ArchimedeanQuotient s) with
  monotone' := by
    intro a b hab
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, QuotientGroup.mk'_apply]
    rw [ArchimedeanQuotient.le_def]
    by_cases heq : ArchimedeanQuotient.mk s a = ArchimedeanQuotient.mk s b
    · apply le_of_eq
      congr
    · have hne : a ≠ b := by aesop
      have hpos : 1 ≤ a⁻¹ * b := by aesop
      have hnotmem : ArchimedeanClass.mk (a⁻¹ * b) ∉ s.carrier :=
        (not_iff_not.mpr (ArchimedeanQuotient.eq_iff _ _ _)).mp heq
      apply le_of_lt
      suffices 1 < (ArchimedeanQuotient.mk s a).out⁻¹ * (ArchimedeanQuotient.mk s b).out by
        aesop
      suffices 1 < a⁻¹ * b * ((a * ((ArchimedeanQuotient.mk s a).out⁻¹)) * (((ArchimedeanQuotient.mk s b).out) * b⁻¹)) by
        convert this using 1
        -- I'd like to have a (m)abel tactic here
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_right_comm _ _ a,
          mul_right_comm _ _ b⁻¹, mul_right_comm _ _ b⁻¹]
        simp
      suffices ((a⁻¹ * (ArchimedeanQuotient.mk s a).out) * ((ArchimedeanQuotient.mk s b).out⁻¹ * b)) < a⁻¹ * b by
        apply inv_lt_iff_one_lt_mul.mp
        rw [mul_inv, mul_inv, mul_inv]
        simpa using this
      refine ArchimedeanClass.lt_of_mk_lt_mk ?_ hpos
      refine lt_of_lt_of_le ?_ (ArchimedeanClass.mk_mul _ _)
      apply lt_min
      · contrapose! hnotmem with hclassle
        apply s.upper' hclassle
        apply ArchimedeanQuotient.mk_out
      · contrapose! hnotmem with hclassle
        apply s.upper' hclassle
        apply ArchimedeanQuotient.mk_out'
}

theorem ArchimedeanQuotient.surjective_OrderMonoidHom (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.orderMonoidHom s) := by
  apply Quotient.mk_surjective

-- TODO: extract a theorem: a surjective OrderMonidHom implies IsOrderedMonoid domain
instance ArchimedeanQuotient.instIsOrderedMonoid (s : UpperSet (ArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    IsOrderedMonoid (ArchimedeanQuotient s) where
  mul_le_mul_left (a b) := by
    intro h c
    by_cases heq : a = b
    · rw [heq]
    · have hlt : a < b := by exact lt_of_le_of_ne h heq
      obtain ⟨a', ha⟩ := ArchimedeanQuotient.surjective_OrderMonoidHom s a
      obtain ⟨b', hb⟩ := ArchimedeanQuotient.surjective_OrderMonoidHom s b
      obtain ⟨c', hc⟩ := ArchimedeanQuotient.surjective_OrderMonoidHom s c
      have : a' < b' := by
        contrapose! hlt
        rw [← ha, ← hb]
        exact (ArchimedeanQuotient.orderMonoidHom s).toOrderHom.monotone hlt
      rw [← ha, ← hb, ← hc, ← map_mul, ← map_mul]
      apply (ArchimedeanQuotient.orderMonoidHom s).toOrderHom.monotone
      exact le_of_lt <| mul_lt_mul_left' this c'

theorem ArchimedeanQuotient.class_one (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier]
    (a : M) :
  ArchimedeanClass.mk (ArchimedeanQuotient.mk s a) = 1 ↔ ArchimedeanClass.mk a ∈ s.carrier := by
  rw [← ArchimedeanClass.mk_eq_one]
  rw [QuotientGroup.eq_one_iff]
  unfold ArchimedeanSubgroup
  simp

noncomputable
def ArchimedeanQuotient.classOrderHom (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    (s.carrierᶜ ∪ {1} : Set (ArchimedeanClass M)) →o (ArchimedeanClass (ArchimedeanQuotient s)) :=
  (ArchimedeanClass.orderHom (ArchimedeanQuotient.orderMonoidHom s)).comp (OrderHom.Subtype.val _)

theorem ArchimedeanQuotient.classOrderHom_surjective (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.classOrderHom s) := by
  intro a
  unfold ArchimedeanQuotient.classOrderHom
  simp only [OrderHom.comp_coe, OrderHom.Subtype.val_coe, Function.comp_apply, Subtype.exists,
    Set.union_singleton, Set.mem_insert_iff, Set.mem_compl_iff, exists_prop, exists_eq_or_imp]
  by_cases ha : a = 1
  · left
    rw [ha]
    rw [ArchimedeanClass.orderHom_one]
  · right
    obtain ⟨b, h⟩ := ArchimedeanClass.orderHom_surjective (ArchimedeanQuotient.orderMonoidHom s)
      (ArchimedeanQuotient.surjective_OrderMonoidHom s) a
    use b
    constructor
    · contrapose! ha
      rw [← h]
      unfold ArchimedeanClass.orderHom ArchimedeanClass.orderHomFun
      simp only [OrderHom.coe_mk]
      apply (ArchimedeanClass.mk_eq_one _).mp
      unfold ArchimedeanQuotient.orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      unfold ArchimedeanSubgroup
      simp only [Subgroup.mem_mk, Set.mem_preimage]
      rw [ArchimedeanClass.out_eq]
      exact ha
    · exact h

theorem ArchimedeanQuotient.classOrderHom_injective (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    Function.Injective (ArchimedeanQuotient.classOrderHom s) := by

  intro a b
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ha := Set.mem_or_mem_of_mem_union ha
  obtain hb := Set.mem_or_mem_of_mem_union hb
  unfold classOrderHom
  simp only [OrderHom.comp_coe, OrderHom.Subtype.val_coe, Function.comp_apply, Subtype.mk.injEq]
  by_cases h1 : a = 1 ∨ b = 1
  · obtain h1|h1 := h1
    ---- TODO: optimize this
    · rw [h1]
      rw [ArchimedeanClass.orderHom_one]
      unfold ArchimedeanClass.orderHom ArchimedeanClass.orderHomFun orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, OrderHom.coe_mk]
      intro h
      obtain h := (QuotientGroup.eq_one_iff _).mp ((ArchimedeanClass.mk_eq_one _).mpr h.symm)
      unfold ArchimedeanSubgroup at h
      simp only [Subgroup.mem_mk, Set.mem_preimage] at h
      rw [ArchimedeanClass.out_eq] at h
      obtain h := Set.not_mem_compl_iff.mpr h
      exact (Set.mem_singleton_iff.mp ((or_iff_right h).mp hb)).symm
    · rw [h1]
      rw [ArchimedeanClass.orderHom_one]
      unfold ArchimedeanClass.orderHom ArchimedeanClass.orderHomFun orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, OrderHom.coe_mk]
      intro h
      obtain h := (QuotientGroup.eq_one_iff _).mp ((ArchimedeanClass.mk_eq_one _).mpr h) --
      unfold ArchimedeanSubgroup at h
      simp only [Subgroup.mem_mk, Set.mem_preimage] at h
      rw [ArchimedeanClass.out_eq] at h
      obtain h := Set.not_mem_compl_iff.mpr h
      exact (Set.mem_singleton_iff.mp ((or_iff_right h).mp ha)) --
  · simp only [not_or] at h1
    have ha : a ∉ s.carrier := by
      apply Set.not_mem_of_mem_compl
      refine (or_iff_left ?_).mp ha
      simpa using h1.left
    have hb : b ∉ s.carrier := by
      apply Set.not_mem_of_mem_compl
      refine (or_iff_left ?_).mp hb
      simpa using h1.right

    rw [← ArchimedeanClass.out_eq a, ← ArchimedeanClass.out_eq b]
    rw [← ArchimedeanClass.orderHom_comm_mk, ← ArchimedeanClass.orderHom_comm_mk]

    rw [ArchimedeanClass.eq_iff, ArchimedeanClass.eq_iff]
    intro h
    obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := h
    rw [OrderMonoidHom.map_mabs, OrderMonoidHom.map_mabs, ← map_pow] at hm hn
    rw [ArchimedeanQuotient.le_def] at hm hn
    set A := mabs a.out
    set B := mabs b.out
    set An := A ^ n
    set Bm := B ^ m
    set A' := ((orderMonoidHom s) A).out
    set B' := ((orderMonoidHom s) B).out
    set An' := ((orderMonoidHom s) An).out
    set Bm' := ((orderMonoidHom s) Bm).out

    have hApos : 1 ≤ A := one_le_mabs a.out
    have hBpos : 1 ≤ B := one_le_mabs b.out
    have hABmpos : 1 ≤ A'⁻¹ * Bm' := le_inv_mul_iff_le.mpr hm
    have hBAnpos : 1 ≤ B'⁻¹ * An' := le_inv_mul_iff_le.mpr hn

    have hAA : ArchimedeanClass.mk (A'⁻¹ * A) ∈ s.carrier := by
      apply (ArchimedeanQuotient.eq_iff _ _ _).mp
      unfold A'
      unfold ArchimedeanQuotient.mk orderMonoidHom
      simp
    have hBB : ArchimedeanClass.mk (B'⁻¹ * B) ∈ s.carrier := by
      apply (ArchimedeanQuotient.eq_iff _ _ _).mp
      unfold B'
      unfold ArchimedeanQuotient.mk orderMonoidHom
      simp
    have hAAn : ArchimedeanClass.mk (An⁻¹ * An') ∈ s.carrier := by
      apply (ArchimedeanQuotient.eq_iff _ _ _).mp
      unfold An'
      unfold ArchimedeanQuotient.mk orderMonoidHom
      simp
    have hBBm : ArchimedeanClass.mk (Bm⁻¹ * Bm') ∈ s.carrier := by
      apply (ArchimedeanQuotient.eq_iff _ _ _).mp
      unfold Bm'
      unfold ArchimedeanQuotient.mk orderMonoidHom
      simp

    refine ⟨⟨m + 1, by simp, ?_⟩, ⟨n + 1, by simp, ?_⟩⟩
    · have : B ^ (m + 1) = Bm * B := by exact pow_succ B m
      rw [this]
      suffices (A'⁻¹ * A) * (Bm⁻¹ * Bm') ≤ (A'⁻¹ * Bm') * B by
        rw [mul_assoc A'⁻¹, mul_assoc A'⁻¹] at this
        obtain h := le_of_mul_le_mul_left' this
        rw [mul_comm A] at h
        obtain h := le_inv_mul_of_mul_le h
        rw [mul_inv, ← mul_assoc] at h
        simpa using h
      have hpos : 1 ≤ A'⁻¹ * Bm' * B := one_le_mul hABmpos hBpos
      have hpos' : ArchimedeanClass.mk (A'⁻¹ * Bm' * B) ∉ s.carrier := by
        rw [← ArchimedeanClass.mk_mul_of_one_le hABmpos hBpos]
        suffices ArchimedeanClass.mk B ∉ s.carrier by
          contrapose! this with h
          exact s.upper' (min_le_right _ _) h
        unfold B
        rw [ArchimedeanClass.mk_mabs, ArchimedeanClass.out_eq]
        exact hb
      apply le_of_lt
      apply ArchimedeanClass.lt_of_mk_lt_mk _ hpos
      refine lt_of_lt_of_le ?_ (ArchimedeanClass.mk_mul _ _)
      apply lt_min
      · contrapose! hpos' with h
        exact s.upper' h hAA
      · contrapose! hpos' with h
        exact s.upper' h hBBm
    · have : A ^ (n + 1) = An * A := by exact pow_succ A n
      rw [this]
      suffices (B'⁻¹ * B) * (An⁻¹ *An') ≤ B'⁻¹ * An' * A by
        rw [mul_assoc B'⁻¹, mul_assoc B'⁻¹] at this
        obtain h := le_of_mul_le_mul_left' this
        rw [mul_comm B] at h
        obtain h := le_inv_mul_of_mul_le h
        rw [mul_inv, ← mul_assoc] at h
        simpa using h
      have hpos : 1 ≤ B'⁻¹ * An' * A := one_le_mul hBAnpos hApos
      have hpos' : ArchimedeanClass.mk (B'⁻¹ * An' * A) ∉ s.carrier := by
        rw [← ArchimedeanClass.mk_mul_of_one_le hBAnpos hApos]
        suffices ArchimedeanClass.mk A ∉ s.carrier by
          contrapose! this with h
          exact s.upper' (min_le_right _ _) h
        unfold A
        rw [ArchimedeanClass.mk_mabs, ArchimedeanClass.out_eq]
        exact ha
      apply le_of_lt
      apply ArchimedeanClass.lt_of_mk_lt_mk _ hpos
      refine lt_of_lt_of_le ?_ (ArchimedeanClass.mk_mul _ _)
      apply lt_min
      · contrapose! hpos' with h
        exact s.upper' h hBB
      · contrapose! hpos' with h
        exact s.upper' h hAAn

noncomputable
def ArchimedeanQuotient.classOrderIso (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    (s.carrierᶜ ∪ {1} : Set (ArchimedeanClass M)) ≃o (ArchimedeanClass (ArchimedeanQuotient s)) where
  toFun := ArchimedeanQuotient.classOrderHom s
  invFun := Function.surjInv (ArchimedeanQuotient.classOrderHom_surjective s)
  left_inv := by
    apply Function.leftInverse_surjInv
    constructor
    · apply ArchimedeanQuotient.classOrderHom_injective
    · apply ArchimedeanQuotient.classOrderHom_surjective
  right_inv := Function.rightInverse_surjInv (ArchimedeanQuotient.classOrderHom_surjective s)
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      exact ((OrderHomClass.monotone (classOrderHom s)).strictMono_of_injective
        (ArchimedeanQuotient.classOrderHom_injective s)).le_iff_le.mp h
    · intro h
      exact OrderHomClass.monotone _ h

/-theorem ArchimedeanQuotient.same_class (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier]
    (a b : ArchimedeanQuotient s) :
    ArchimedeanClass.mk a = ArchimedeanClass.mk b ↔ ArchimedeanClass.mk a.out = ArchimedeanClass.mk b.out := by
  rw [ArchimedeanClass.eq_iff, ArchimedeanClass.eq_iff]
  simp_rw [← mabs_pow]
  simp_rw [ArchimedeanQuotient.le_def]
  sorry

theorem ArchimedeanQuotient.class_transfer (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier]
    (a b : M) (hs : ArchimedeanClass.mk a ∉ s.carrier) :
    ArchimedeanClass.mk (ArchimedeanQuotient.mk s a) = ArchimedeanClass.mk (ArchimedeanQuotient.mk s b) ↔
    ArchimedeanClass.mk a = ArchimedeanClass.mk b := by
  rw [ArchimedeanClass.eq_iff, ArchimedeanClass.eq_iff]
  simp_rw [← mabs_pow, ← QuotientGroup.mk_pow]
  constructor
  · simp_rw [ArchimedeanQuotient.le_def]
    /-intro h
    obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := h
    rw [ArchimedeanQuotient.le_def] at hm hn
    sorry -/
    intro h
    sorry
  · sorry

noncomputable
def ArchimedeanQuotient.class_map (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier]
    (a : ArchimedeanClass (ArchimedeanQuotient s)) : (s.carrierᶜ ∪ {1} : Set (ArchimedeanClass M)) :=
  ⟨if a = 1 then 1 else ArchimedeanClass.mk a.out.out, by
    by_cases ha : a = 1
    · simp [ha]
    · apply Set.mem_union_left
      simp only [ha, ↓reduceIte, Set.mem_compl_iff]
      obtain ha := (ArchimedeanClass.out_eq_one _).not.mpr ha
      rw [← QuotientGroup.out_eq' a.out] at ha
      obtain ha := (QuotientGroup.eq_one_iff _).not.mp ha
      unfold ArchimedeanSubgroup at ha
      simpa using ha
  ⟩

theorem ArchimedeanQuotient.class_map_injective (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.class_map s) := by
  intro a
  obtain hmem|hmem := (Set.mem_union _ _ _).mp a.prop
  · use ArchimedeanClass.mk (ArchimedeanQuotient.mk s a.val.out)
    unfold class_map
    have : ¬ ArchimedeanClass.mk (mk s a.val.out) = 1 := by
      apply (ArchimedeanQuotient.class_one _ _).not.mpr
      rw [ArchimedeanClass.out_eq]
      simpa using hmem
    simp only [this, ↓reduceIte]

    sorry
  · use 1
    unfold class_map
    simp only [↓reduceIte]
    refine (Subtype.coe_eq_of_eq_mk ?_).symm
    simpa using hmem

noncomputable
def ArchimedeanQuotient.class_map_iso (s : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] :
    ArchimedeanClass (ArchimedeanQuotient s) ≃o (s.carrierᶜ ∪ {1} : Set (ArchimedeanClass M)) where
  toFun := ArchimedeanQuotient.class_map s
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry-/

noncomputable
abbrev ArchimedeanLayer (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] :=
  Subgroup.map (ArchimedeanQuotient.orderMonoidHom t).toMonoidHom (ArchimedeanSubgroup s)

noncomputable
instance ArchimedeanLayer.instLinearOrder (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : LinearOrder (ArchimedeanLayer s t) := by infer_instance

theorem ArchimedeanLayer.le_def (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : ∀ (x y : ArchimedeanLayer s t), x ≤ y ↔ x.val.out ≤ y.val.out := by
  intro x y
  rfl

instance ArchimedeanLayer.instIsOrderedMonoid (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : IsOrderedMonoid (ArchimedeanLayer s t) := by infer_instance


noncomputable
def ArchimedeanLayer.class_map (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] (a : ArchimedeanClass (ArchimedeanLayer s t)) :
    (s.carrier ∩ (t.carrierᶜ ∪ {1}) : Set (ArchimedeanClass M)) :=
  ⟨ArchimedeanClass.mk a.out.val.out, sorry⟩
/-
def ArchimedeanLayer.class_orderIso (s t : UpperSet (ArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] :
    ArchimedeanClass (ArchimedeanLayer s t) ≃o (s.carrier \ t.carrier ∪ {1} : Set (ArchimedeanClass M)) := by sorry
-/

--def ArchimedeanLayer.orderIso
--def ArchimedeanLayer.classOrderIsoFun (s t : UpperSet (ArchimedeanClass M))
--    [Nonempty s.carrier] [Nonempty t.carrier] :

/-
noncomputable
def phi1 (t : UpperSet (ArchimedeanClass M))
    [Nonempty t.carrier] :=
    ArchimedeanClass.orderHom (ArchimedeanQuotient.orderMonoidHom t)

noncomputable
def phi2 (s t : UpperSet (ArchimedeanClass M)) [Nonempty s.carrier] [Nonempty t.carrier]:
    ArchimedeanClass (ArchimedeanSubgroup s) →o ArchimedeanClass (ArchimedeanQuotient (M := ArchimedeanSubgroup s) t) := by

    sorry-/
