import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

section Patch
theorem pow_le_self {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {a : M} {n : ℕ} (ha : a ≤ 1) (hn : n ≠ 0) :
  a ^ n ≤ a := by
  simpa using pow_le_pow_right_of_le_one' ha (Nat.one_le_iff_ne_zero.2 hn)
end Patch

variable {M : Type*}
variable [CommMonoid M] [LinearOrder M]

def ArchimedeanEquiv (x y : M) :=
  ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ (y ≤ x ^ n ∨ y ^ n ≤ x)) ∨
  (y ≤ x ∧ (x ≤ y ^ n ∨ x ^ n ≤ y)))


theorem ArchimedeanEquiv.refl (x : M) : ArchimedeanEquiv x x := by
  unfold ArchimedeanEquiv
  use 1
  simp

theorem ArchimedeanEquiv.symm {x y : M} (h : ArchimedeanEquiv x y) :
    ArchimedeanEquiv y x := by
  unfold ArchimedeanEquiv at h ⊢
  aesop

theorem ArchimedeanEquiv.dual {x y : M} (h : ArchimedeanEquiv x y) : ArchimedeanEquiv (M := Mᵒᵈ) x y := by
  unfold ArchimedeanEquiv at h ⊢
  aesop

variable [IsOrderedMonoid M]

theorem archimedeanEquiv_iff_of_one_lt_right (x y : M) (hlt : 1 < y) :
    ArchimedeanEquiv x y ↔
    ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ y ≤ x ^ n) ∨ (y ≤ x ∧ x ≤ y ^ n)) := by
  unfold ArchimedeanEquiv
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

theorem archimedeanEquiv_iff_of_right_lt_one (x y : M) (hlt : y < 1) :
    ArchimedeanEquiv x y ↔
    ∃ (n : ℕ), (n ≠ 0) ∧ ((x ≤ y ∧ y ^ n ≤ x) ∨ (y ≤ x ∧ (x ^ n ≤ y))) := by
  unfold ArchimedeanEquiv
  constructor
  · obtain h := (archimedeanEquiv_iff_of_one_lt_right (M := Mᵒᵈ) x y hlt).mp
    unfold ArchimedeanEquiv at h
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

theorem archimedeanEquiv_one_iff (x : M) : ArchimedeanEquiv x 1 ↔ x = 1 := by
  unfold ArchimedeanEquiv
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

theorem ArchimedeanEquiv.le_one {x y : M} (h : ArchimedeanEquiv x y) (hle : y ≤ 1) :
    x ≤ 1 := by
  by_contra! hlt
  unfold ArchimedeanEquiv at h
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

theorem ArchimedeanEquiv.lt_one {x y : M} (h : ArchimedeanEquiv x y) (hlt : y < 1) :
    x < 1 := by
  obtain hle := ArchimedeanEquiv.le_one h hlt.le
  apply lt_of_le_of_ne hle
  contrapose! h
  rw [h]
  obtain hy1 := (not_iff_not.mpr (archimedeanEquiv_one_iff y)).mpr (ne_of_lt hlt)
  contrapose! hy1
  exact ArchimedeanEquiv.symm hy1

theorem ArchimedeanEquiv.one_le {x y : M} (h : ArchimedeanEquiv x y) (hle : 1 ≤ y) :
    1 ≤ x :=
  ArchimedeanEquiv.le_one (M := Mᵒᵈ) ((ArchimedeanEquiv.dual) h) hle

theorem ArchimedeanEquiv.one_lt {x y : M} (h : ArchimedeanEquiv x y) (hle : 1 < y) :
    1 < x :=
  ArchimedeanEquiv.lt_one (M := Mᵒᵈ) ((ArchimedeanEquiv.dual) h) hle

theorem ArchimedeanEquiv.trans_of_lt_one {x y z : M} (hy1 : y < 1)
    (hxy : ArchimedeanEquiv x y) (hyz : ArchimedeanEquiv y z) :
    ArchimedeanEquiv x z := by
  obtain hzy := ArchimedeanEquiv.symm hyz
  obtain ⟨m, ⟨hm0, hm⟩⟩ := (archimedeanEquiv_iff_of_right_lt_one x y hy1).mp hxy
  obtain ⟨n, ⟨hn0, hn⟩⟩ := (archimedeanEquiv_iff_of_right_lt_one z y hy1).mp hzy
  obtain hz1 : z < 1 := ArchimedeanEquiv.lt_one hzy hy1
  apply (archimedeanEquiv_iff_of_right_lt_one x z hz1).mpr
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

theorem ArchimedeanEquiv.trans {x y z : M}
    (hxy : ArchimedeanEquiv x y) (hyz : ArchimedeanEquiv y z) :
    ArchimedeanEquiv x z := by
  obtain hzy := ArchimedeanEquiv.symm hyz
  obtain hy1|hy1|hy1 := lt_trichotomy y 1
  · exact ArchimedeanEquiv.trans_of_lt_one hy1 hxy hyz
  · rw [hy1] at hxy hzy
    obtain hx := (archimedeanEquiv_one_iff x).mp hxy
    obtain hz := (archimedeanEquiv_one_iff z).mp hzy
    rw [hx, hz]
    exact ArchimedeanEquiv.refl 1
  · exact (ArchimedeanEquiv.dual (M := Mᵒᵈ)) <|
      ArchimedeanEquiv.trans_of_lt_one (M := Mᵒᵈ) hy1
      ((ArchimedeanEquiv.dual) hxy)
      ((ArchimedeanEquiv.dual) hyz)

def ArchimedeanEquiv.equiv : Equivalence (ArchimedeanEquiv (M := M)) where
  refl := ArchimedeanEquiv.refl
  symm := ArchimedeanEquiv.symm
  trans := ArchimedeanEquiv.trans

def ArchimedeanEquiv.setoid : Setoid M where
  r := ArchimedeanEquiv
  iseqv := ArchimedeanEquiv.equiv

def ArchimedeanClass (M : Type*) [CommMonoid M] [LinearOrder M] [IsOrderedMonoid M] :=
    Quotient (ArchimedeanEquiv.setoid (M := M))

def ArchimedeanClass.mk (a : M) : ArchimedeanClass M := ⟦a⟧

noncomputable
instance ArchimedeanClass.instLinearOrder : LinearOrder (ArchimedeanClass M) :=
  LinearOrder.lift' Quotient.out (Quotient.out_injective)

theorem ArchimedeanClass.le_def : ∀ (a b : ArchimedeanClass M), a ≤ b ↔ a.out ≤ b.out := by
  intro a b
  rfl

theorem ArchimedeanClass.lt_def : ∀ (a b : ArchimedeanClass M), a < b ↔ a.out < b.out := by
  intro a b
  rfl

theorem ArchimedeanClass.lt_of_lt_of_one_lt_right {a b : M} (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b)
    (hb : 1 < b) : a < b := by
  rw [lt_def] at h
  set a' := Quotient.out (mk a)
  set b' := Quotient.out (mk b)
  have haeq : ArchimedeanEquiv a' a := Quotient.mk_out (s := ArchimedeanEquiv.setoid) a
  have hbeq : ArchimedeanEquiv b' b := Quotient.mk_out (s := ArchimedeanEquiv.setoid) b
  obtain ⟨n, hn0, hn⟩ := (archimedeanEquiv_iff_of_one_lt_right b' b hb).mp hbeq
  obtain ha|ha := le_or_gt a 1
  · exact lt_of_le_of_lt ha hb
  · obtain ⟨m, hm0, hm⟩ := (archimedeanEquiv_iff_of_one_lt_right a' a ha).mp haeq
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

theorem ArchimedeanClass.lt_of_lt_of_right_lt_one {a b : M} (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b)
    (hb : b < 1) : a < b := by
  rw [lt_def] at h
  set a' := Quotient.out (mk a)
  set b' := Quotient.out (mk b)
  have haeq : ArchimedeanEquiv a' a := Quotient.mk_out (s := ArchimedeanEquiv.setoid) a
  have hbeq : ArchimedeanEquiv b' b := Quotient.mk_out (s := ArchimedeanEquiv.setoid) b
  obtain ⟨n, hn0, hn⟩ := (archimedeanEquiv_iff_of_right_lt_one b' b hb).mp hbeq
  obtain ha|ha := le_or_gt 1 a
  · obtain hb' := ArchimedeanEquiv.lt_one hbeq hb
    obtain ha' := ArchimedeanEquiv.one_le haeq ha
    obtain h' := (lt_of_lt_of_le hb' ha').trans h
    simp at h'
  · obtain ⟨m, hm0, hm⟩ := (archimedeanEquiv_iff_of_right_lt_one a' a ha).mp haeq
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

theorem ArchimedeanClass.one_mk_out : (ArchimedeanClass.mk (M := M) 1).out = 1 :=
  (archimedeanEquiv_one_iff _).mp <| Quotient.mk_out (s := ArchimedeanEquiv.setoid) 1


theorem ArchimedeanClass.lt_of_lt {a b : M} (h : ArchimedeanClass.mk a < ArchimedeanClass.mk b) :
    a < b := by
  obtain hb|hb|hb := lt_trichotomy b 1
  · exact ArchimedeanClass.lt_of_lt_of_right_lt_one h hb
  · rw [hb] at h ⊢
    have h : (mk a).out < (mk 1).out := h
    rw [ArchimedeanClass.one_mk_out] at h
    set a' := Quotient.out (mk a)
    have haeq : ArchimedeanEquiv a' a := Quotient.mk_out (s := ArchimedeanEquiv.setoid) a
    exact ArchimedeanEquiv.lt_one haeq.symm h
  · exact ArchimedeanClass.lt_of_lt_of_one_lt_right h hb

theorem ArchimedeanClass.mk_monotone : Monotone (ArchimedeanClass.mk (M := M)) := by
  intro a b h
  contrapose! h
  exact ArchimedeanClass.lt_of_lt h

instance ArchimedeanClass.instOne : One (ArchimedeanClass M) where
  one := ArchimedeanClass.mk 1


-- Group


variable {M : Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

theorem ArchimedeanEquiv.inv {a b : M} (h : ArchimedeanEquiv a b) : ArchimedeanEquiv a⁻¹ b⁻¹ := by
  unfold ArchimedeanEquiv at h ⊢
  obtain ⟨n, h⟩ := h
  use n
  aesop


private instance instSetoid : Setoid M := ArchimedeanEquiv.setoid
theorem ArchimedeanClass.inv_stable (a b : M) (h : a ≈ b) : ArchimedeanClass.mk a⁻¹ = ArchimedeanClass.mk b⁻¹ := by
  obtain h: ArchimedeanEquiv a b := h
  unfold ArchimedeanClass.mk
  apply Quotient.eq.mpr
  exact h.inv

def ArchimedeanClass.inv : ArchimedeanClass M → ArchimedeanClass M :=
  Quotient.lift (ArchimedeanClass.mk ·⁻¹) ArchimedeanClass.inv_stable

theorem ArchimedeanClass.inv_inv (a : ArchimedeanClass M) : a.inv.inv = a := by
  unfold ArchimedeanClass.inv
  unfold ArchimedeanClass.mk
  rw [← Quotient.out_eq a, Quotient.lift_mk, Quotient.lift_mk]
  simp

instance ArchimedeanClass.instInv : InvolutiveInv (ArchimedeanClass M) where
  inv := ArchimedeanClass.inv
  inv_inv := ArchimedeanClass.inv_inv

def ArchimedeanClass.inv_def : ∀ (a : ArchimedeanClass M), a⁻¹ = ArchimedeanClass.inv (M := M) a := by
  intro a
  rfl

def AbsArchimedeanClass (M : Type*) [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] :=
  {a : ArchimedeanClass M // a ≤ 1}

def AbsArchimedeanClass.mk (a : M) : AbsArchimedeanClass M :=
  ⟨ArchimedeanClass.mk (|a|ₘ⁻¹), by
    apply (ArchimedeanClass.mk_monotone (M := M))
    simp
  ⟩

theorem AbsArchimedeanClass.mk_inv (a : M) : AbsArchimedeanClass.mk (a⁻¹) = AbsArchimedeanClass.mk a := by
  unfold AbsArchimedeanClass.mk
  simp

instance AbsArchimedeanClass.instOne : One (AbsArchimedeanClass M) where
  one := AbsArchimedeanClass.mk 1

theorem AbsArchimedeanClass.one_eq : (1 : AbsArchimedeanClass M).val = 1 := by
  have : (1 : AbsArchimedeanClass M).val = (ArchimedeanClass.mk |1|ₘ⁻¹) := by rfl
  rw [this]
  have : (1 : ArchimedeanClass M) = (ArchimedeanClass.mk 1) := by rfl
  rw [this]
  simp

noncomputable
instance AbsArchimedeanClass.instLinearOrder : LinearOrder (AbsArchimedeanClass M) := by
  unfold AbsArchimedeanClass
  infer_instance

theorem AbsArchimedeanClass.le_one (a : AbsArchimedeanClass M) : a ≤ 1 := by
  apply Subtype.coe_le_coe.mp
  rw [AbsArchimedeanClass.one_eq]
  exact a.prop

theorem AbsArchimedeanClass.eq_iff (a b : M) :
    AbsArchimedeanClass.mk a = AbsArchimedeanClass.mk b ↔
    (∃ n, n ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ n) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n) := by
  unfold AbsArchimedeanClass.mk ArchimedeanClass.mk
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
      simpa using ArchimedeanEquiv.refl 1
    · have : (mabs b)⁻¹ < 1 := by exact Left.inv_lt_one_iff.mpr hb0
      apply (archimedeanEquiv_iff_of_right_lt_one _ _ this).mpr
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

theorem AbsArchimedeanClass.lt_iff (a b : M) :
    AbsArchimedeanClass.mk a < AbsArchimedeanClass.mk b ↔
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
    · unfold AbsArchimedeanClass.mk ArchimedeanClass.mk at h
      rw [Subtype.mk_lt_mk] at h
      obtain h' := ArchimedeanClass.mk_monotone.reflect_lt h
      simp only [inv_lt_inv_iff] at h'
      obtain h'' := ne_of_lt h
      simp only [ne_eq] at h''
      rw [Quotient.eq] at h''
      obtain h'' := (not_iff_not.mpr (archimedeanEquiv_iff_of_right_lt_one _ _ (inv_lt_one'.mpr hb0))).mp h''
      simp only [ne_eq, inv_le_inv_iff, inv_pow, not_exists, not_and, not_le, not_or] at h''
      intro n
      by_cases hn0 : n = 0
      · rw [hn0]
        simp only [pow_zero]
        exact hb0.trans h'
      · exact (h'' n hn0).1 h'.le
  · intro h
    apply lt_of_le_of_ne
    · unfold AbsArchimedeanClass.mk ArchimedeanClass.mk
      rw [Subtype.mk_le_mk]
      apply ArchimedeanClass.mk_monotone
      obtain h := h 1
      simp only [pow_one] at h
      simp only [inv_le_inv_iff]
      exact le_of_lt h
    · contrapose! h
      rw [AbsArchimedeanClass.eq_iff] at h
      aesop

theorem AbsArchimedeanClass.mk_mul_self {a b : M} (hab : mk a = mk b) : mk a ≤ mk (a * b) := by
  by_contra! h
  obtain h2 := hab ▸ h
  obtain h1 := (AbsArchimedeanClass.lt_iff _ _).mp h  2
  obtain h2 := (AbsArchimedeanClass.lt_iff _ _).mp h2  2
  rw [pow_two] at h1 h2
  have h1 := lt_of_lt_of_le h1 (mabs_mul _ _)
  have h2 := lt_of_lt_of_le h2 (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right] at h1 h2
  have := h1.trans h2
  simp at this

theorem AbsArchimedeanClass.mk_mul_of_lt {a b : M} (h : mk a < mk b) : mk a = mk (a * b) := by
  obtain h := (AbsArchimedeanClass.lt_iff _ _).mp h
  apply (AbsArchimedeanClass.eq_iff _ _).mpr
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

theorem AbsArchimedeanClass.mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  obtain hab|hab|hab := lt_trichotomy (mk a) (mk b)
  · simp only [inf_le_iff]
    left
    exact (AbsArchimedeanClass.mk_mul_of_lt hab).le
  · rw [← hab]
    simpa using AbsArchimedeanClass.mk_mul_self hab
  · simp only [inf_le_iff]
    right
    rw [mul_comm]
    exact (AbsArchimedeanClass.mk_mul_of_lt hab).le

instance AbsArchimedeanClass.instOrderTop : OrderTop (AbsArchimedeanClass M) where
  top := 1
  le_top := AbsArchimedeanClass.le_one

def AbsArchimedeanClass.subgroup (minClass : AbsArchimedeanClass M) : Subgroup M where
  carrier := AbsArchimedeanClass.mk ⁻¹' (Set.Ici minClass)
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage, Set.mem_Ici] at ha hb ⊢
    exact (le_min ha hb).trans (AbsArchimedeanClass.mk_mul _ _)
  one_mem' := by simpa using AbsArchimedeanClass.le_one minClass
  inv_mem' := by
    intro a h
    simp [Set.mem_preimage,
      Set.mem_Ici] at h ⊢
    rw [AbsArchimedeanClass.mk_inv]
    exact h
