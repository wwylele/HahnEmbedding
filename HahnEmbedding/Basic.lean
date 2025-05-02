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

theorem ArchimedeanClass.mk_one : ArchimedeanClass.mk (M := M) 1 = 1 := by
  rfl

theorem ArchimedeanClass.one_out : (1 : ArchimedeanClass (M := M)).out = 1 := by
  apply ArchimedeanClass.one_mk_out

theorem ArchimedeanClass.mk_eq_one (a : M) : a = 1 ↔ mk a = 1 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [← ArchimedeanClass.mk_one] at h
    unfold mk at h
    rw [Quotient.eq] at h
    apply (archimedeanEquiv_one_iff _).mp h

theorem ArchimedeanClass.mk_lt_one (a : M) : a < 1 ↔ mk a < 1 := by
  rw [← ArchimedeanClass.mk_one]
  constructor
  · intro h
    apply lt_of_le_of_ne
    · exact ArchimedeanClass.mk_monotone h.le
    · contrapose! h
      apply le_of_eq
      exact ((ArchimedeanClass.mk_eq_one _).mpr h).symm
  · exact ArchimedeanClass.mk_monotone.reflect_lt

theorem ArchimedeanClass.mk_one_le (a : M) : 1 ≤ a ↔ 1 ≤ mk a := by
  simpa using (ArchimedeanClass.mk_lt_one a).not

theorem ArchimedeanClass.mk_one_lt (a : M) : 1 < a ↔ 1 < mk a := by
  have eq := ArchimedeanClass.mk_eq_one a
  have le := ArchimedeanClass.mk_one_le a
  constructor
  · intro h
    exact lt_of_le_of_ne' (le.mp h.le) (eq.not.mp h.ne.symm)
  · intro h
    exact lt_of_le_of_ne' (le.mpr h.le) (eq.not.mpr h.ne.symm)

theorem ArchimedeanClass.mk_le_one (a : M) : a ≤ 1 ↔ mk a ≤ 1 := by
  have eq := ArchimedeanClass.mk_eq_one a
  have lt := ArchimedeanClass.mk_lt_one a
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

theorem AbsArchimedeanClass.mk_mabs (a : M) : AbsArchimedeanClass.mk |a|ₘ = AbsArchimedeanClass.mk a := by
  unfold AbsArchimedeanClass.mk
  simp

instance AbsArchimedeanClass.instOne : One (AbsArchimedeanClass M) where
  one := AbsArchimedeanClass.mk 1

theorem AbsArchimedeanClass.one_def (M : Type*) [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] :
  (1 : AbsArchimedeanClass M) = AbsArchimedeanClass.mk 1 := by rfl

theorem AbsArchimedeanClass.one_eq : (1 : AbsArchimedeanClass M).val = 1 := by
  have : (1 : AbsArchimedeanClass M).val = (ArchimedeanClass.mk |1|ₘ⁻¹) := by rfl
  rw [this]
  have : (1 : ArchimedeanClass M) = (ArchimedeanClass.mk 1) := by rfl
  rw [this]
  simp

theorem AbsArchimedeanClass.mk_eq_one (a : M) : a = 1 ↔ mk a = 1 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    unfold AbsArchimedeanClass.mk at h
    obtain h := Subtype.ext_iff_val.mp h
    simp only at h
    rw [AbsArchimedeanClass.one_eq] at h
    obtain h := (ArchimedeanClass.mk_eq_one _).mpr h
    simpa using h

noncomputable
instance AbsArchimedeanClass.instLinearOrder : LinearOrder (AbsArchimedeanClass M) := by
  unfold AbsArchimedeanClass
  infer_instance

theorem AbsArchimedeanClass.le_one (u : AbsArchimedeanClass M) : u ≤ 1 := by
  apply Subtype.coe_le_coe.mp
  rw [AbsArchimedeanClass.one_eq]
  exact u.prop

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

theorem AbsArchimedeanClass.mk_mul_of_one_le {a b : M} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  min (mk a) (mk b) = mk (a * b) := by
  obtain lt|eq|gt := lt_trichotomy (mk a) (mk b)
  · rw [← AbsArchimedeanClass.mk_mul_of_lt lt]
    exact min_eq_left_of_lt lt
  · rw [eq]
    simp only [min_self]
    rw [AbsArchimedeanClass.eq_iff] at eq
    rw [AbsArchimedeanClass.eq_iff]
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
    rw [← AbsArchimedeanClass.mk_mul_of_lt gt]
    exact min_eq_right_of_lt gt

theorem AbsArchimedeanClass.lt_of_mk_lt_mk {a b : M} (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := (AbsArchimedeanClass.lt_iff _ _).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

noncomputable
abbrev AbsArchimedeanClass.out (a : AbsArchimedeanClass M) : M := a.val.out

theorem AbsArchimedeanClass.out_injective : Function.Injective (AbsArchimedeanClass.out (M := M)) := by
  unfold AbsArchimedeanClass.out
  exact Quotient.out_injective.comp Subtype.val_injective

theorem AbsArchimedeanClass.one_out : (1 : AbsArchimedeanClass M).out = 1 := by
  unfold AbsArchimedeanClass.out
  rw [AbsArchimedeanClass.one_eq]
  apply ArchimedeanClass.one_out


theorem AbsArchimedeanClass.out_le_one (a : AbsArchimedeanClass M) : a.out ≤ 1 := by
  unfold AbsArchimedeanClass.out
  apply (ArchimedeanClass.mk_le_one _).mpr
  unfold ArchimedeanClass.mk
  rw [Quotient.out_eq]
  exact a.prop

theorem AbsArchimedeanClass.out_eq_one (a : AbsArchimedeanClass M) : a.out = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← AbsArchimedeanClass.one_out] at h
    exact AbsArchimedeanClass.out_injective h
  · intro h
    rw [h]
    apply AbsArchimedeanClass.one_out

theorem AbsArchimedeanClass.out_eq (a : AbsArchimedeanClass M) : mk a.out = a := by
  unfold AbsArchimedeanClass.mk ArchimedeanClass.mk
  apply Subtype.eq
  simp only
  rw [Quotient.mk_eq_iff_out]
  use 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_pow, true_and]
  rw [mabs_eq_inv_self.mpr (AbsArchimedeanClass.out_le_one _)]
  simp

instance AbsArchimedeanClass.instOrderTop : OrderTop (AbsArchimedeanClass M) where
  top := 1
  le_top := AbsArchimedeanClass.le_one

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

/-theorem MonoidHom.map_pow' {α β F : Type*} [Monoid α] [Monoid β] [FunLike F α β]
    [MonoidHomClass F α β] (f : F) (a : α) (n : ℕ):
    f (a ^ n) = f a ^ n := by
  have : f (a ^ n) = (MonoidHomClass.toMonoidHom f) (a ^ n) := by rfl
  rw [this, MonoidHom.map_pow]
  simp-/

noncomputable
abbrev AbsArchimedeanClass.orderHomFun {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (a : AbsArchimedeanClass M) : AbsArchimedeanClass N :=
  AbsArchimedeanClass.mk (f a.out)

noncomputable
def AbsArchimedeanClass.orderHom {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) : AbsArchimedeanClass M →o AbsArchimedeanClass N where

  toFun := AbsArchimedeanClass.orderHomFun f
  monotone' := by
    intro a b h
    contrapose! h
    unfold AbsArchimedeanClass.orderHomFun at h
    rw [AbsArchimedeanClass.lt_iff] at h
    rw [← AbsArchimedeanClass.out_eq a, ← AbsArchimedeanClass.out_eq b]
    rw [AbsArchimedeanClass.lt_iff]
    intro n
    obtain h := h n
    contrapose! h
    obtain h := OrderHomClass.monotone f h
    simp only [OrderMonoidHom.toOrderHom_eq_coe, OrderHomClass.coe_coe, map_pow] at h
    rw [← OrderMonoidHom.map_mabs, ← OrderMonoidHom.map_mabs] at h
    exact h

theorem AbsArchimedeanClass.orderHom_comm_mk {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (a : M):
    AbsArchimedeanClass.mk (f a) = (AbsArchimedeanClass.orderHom f) (AbsArchimedeanClass.mk a) := by
  unfold AbsArchimedeanClass.orderHom AbsArchimedeanClass.orderHomFun
  simp
  apply (AbsArchimedeanClass.eq_iff _ _).mpr
  have a_eq : AbsArchimedeanClass.mk a = AbsArchimedeanClass.mk (AbsArchimedeanClass.mk a).out := by
    rw [AbsArchimedeanClass.out_eq]
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := (AbsArchimedeanClass.eq_iff _ _).mp a_eq
  constructor <;> [use m; use n]
  <;> [refine ⟨hm0, ?_⟩; refine ⟨hn0, ?_⟩]
  all_goals
    rw [OrderMonoidHom.map_mabs, OrderMonoidHom.map_mabs]
    rw [← map_pow]
    apply OrderHomClass.monotone
    try exact hm
    try exact hn

theorem AbsArchimedeanClass.orderHom_one {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) :
    (AbsArchimedeanClass.orderHom f) 1 = 1 := by
  rw [AbsArchimedeanClass.one_def]
  rw [← AbsArchimedeanClass.orderHom_comm_mk]
  simp only [map_one]
  rw [AbsArchimedeanClass.one_def]

/-def AbsArchimedeanClass.orderHom_topHom
    {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N] (f : F) :
    TopHom (AbsArchimedeanClass M) (AbsArchimedeanClass N) := by sorry-/

theorem AbsArchimedeanClass.orderHom_surjective {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (h : Function.Surjective f) :
    Function.Surjective (AbsArchimedeanClass.orderHom f) := by
  intro a
  obtain ⟨b, hb⟩ := h a.out
  use AbsArchimedeanClass.mk b
  rw [← AbsArchimedeanClass.orderHom_comm_mk, hb]
  rw [AbsArchimedeanClass.out_eq]

/-theorem AbsArchimedeanClass.orderHom_injOn {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (s : Set M)
    (h : ∀ a ∈ s, ∀ b ∈ s, (AbsArchimedeanClass.mk (f a) = AbsArchimedeanClass.mk (f b) → AbsArchimedeanClass.mk a = AbsArchimedeanClass.mk b)) :
    Set.InjOn (AbsArchimedeanClass.orderHom f) -/

--------------------------------------------------------------------------------------------------------


def ArchimedeanSubgroup (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] : Subgroup M where
  carrier := AbsArchimedeanClass.mk ⁻¹' s.carrier
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage] at ha hb ⊢
    obtain h|h := min_le_iff.mp (AbsArchimedeanClass.mk_mul a b)
    · apply s.upper' h ha
    · apply s.upper' h hb
  one_mem' := by
    simp only [Set.mem_preimage]
    obtain ⟨u, hu⟩ := hempty
    simpa using s.upper' (AbsArchimedeanClass.le_one u) hu
  inv_mem' := by
    intro a h
    simp [Set.mem_preimage] at h ⊢
    rw [AbsArchimedeanClass.mk_inv]
    exact h


instance ArchimedeanSubgroup.instLinearOrder
    (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
  LinearOrder (ArchimedeanSubgroup s) := by infer_instance

instance ArchimedeanSubgroup.instIsOrderedMonoid
    (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
  IsOrderedMonoid (ArchimedeanSubgroup s) := by infer_instance

theorem ArchimedeanSubgroup.le (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] (hst : s.carrier ⊆ t.carrier) :
    ArchimedeanSubgroup s ≤ ArchimedeanSubgroup t := by
  unfold ArchimedeanSubgroup
  simp only [Subgroup.mk_le_mk]
  refine (Set.preimage_subset_preimage_iff ?_).mpr ?_
  · intro a h
    use a.val.out
    unfold AbsArchimedeanClass.mk ArchimedeanClass.mk
    apply Subtype.eq_iff.mpr
    simp only
    rw [mabs_eq_inv_self.mpr (by
      rw [← ArchimedeanClass.one_mk_out]
      exact (ArchimedeanClass.le_def a.val 1).mp a.prop
    )]
    simp only [inv_inv, Quotient.out_eq]
  · exact hst

abbrev ArchimedeanQuotient (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :=
  M ⧸ ArchimedeanSubgroup s

abbrev ArchimedeanQuotient.mk (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    ArchimedeanQuotient s :=
  a

theorem ArchimedeanQuotient.eq_iff (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] (a b : M) :
    ArchimedeanQuotient.mk s a = ArchimedeanQuotient.mk s b ↔ (AbsArchimedeanClass.mk (a⁻¹ * b)) ∈ s.carrier := by
  rw [QuotientGroup.eq]
  unfold ArchimedeanSubgroup
  simp

theorem ArchimedeanQuotient.mk_out (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    (AbsArchimedeanClass.mk (a⁻¹ * (ArchimedeanQuotient.mk s a).out)) ∈ s.carrier := by
  rw [← ArchimedeanQuotient.eq_iff]
  simp

theorem ArchimedeanQuotient.mk_out' (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] (a : M) :
    (AbsArchimedeanClass.mk ((ArchimedeanQuotient.mk s a).out⁻¹ * a)) ∈ s.carrier := by
  rw [← ArchimedeanQuotient.eq_iff]
  simp

noncomputable
instance ArchimedeanQuotient.instLinearOrder (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    LinearOrder (ArchimedeanQuotient s) :=
  LinearOrder.lift' (·.out) Quotient.out_injective

theorem ArchimedeanQuotient.le_def (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    ∀ (x y : ArchimedeanQuotient s), x ≤ y ↔ x.out ≤ y.out := by
  intro x y
  rfl

theorem ArchimedeanQuotient.lt_def (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    ∀ (x y : ArchimedeanQuotient s), x < y ↔ x.out < y.out := by
  intro x y
  rfl

def ArchimedeanQuotient.orderMonoidHom (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
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
      have hnotmem : AbsArchimedeanClass.mk (a⁻¹ * b) ∉ s.carrier :=
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
      refine AbsArchimedeanClass.lt_of_mk_lt_mk ?_ hpos
      refine lt_of_lt_of_le ?_ (AbsArchimedeanClass.mk_mul _ _)
      apply lt_min
      · contrapose! hnotmem with hclassle
        apply s.upper' hclassle
        apply ArchimedeanQuotient.mk_out
      · contrapose! hnotmem with hclassle
        apply s.upper' hclassle
        apply ArchimedeanQuotient.mk_out'
}

theorem ArchimedeanQuotient.surjective_OrderMonoidHom (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.orderMonoidHom s) := by
  apply Quotient.mk_surjective

-- TODO: extract a theorem: a surjective OrderMonidHom implies IsOrderedMonoid domain
instance ArchimedeanQuotient.instIsOrderedMonoid (s : UpperSet (AbsArchimedeanClass M)) [hempty: Nonempty s.carrier] :
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

theorem ArchimedeanQuotient.class_one (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier]
    (a : M) :
  AbsArchimedeanClass.mk (ArchimedeanQuotient.mk s a) = 1 ↔ AbsArchimedeanClass.mk a ∈ s.carrier := by
  rw [← AbsArchimedeanClass.mk_eq_one]
  rw [QuotientGroup.eq_one_iff]
  unfold ArchimedeanSubgroup
  simp

noncomputable
def ArchimedeanQuotient.classOrderHom (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
    (s.carrierᶜ ∪ {1} : Set (AbsArchimedeanClass M)) →o (AbsArchimedeanClass (ArchimedeanQuotient s)) :=
  (AbsArchimedeanClass.orderHom (ArchimedeanQuotient.orderMonoidHom s)).comp (OrderHom.Subtype.val _)

theorem ArchimedeanQuotient.classOrderHom_surjective (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.classOrderHom s) := by
  intro a
  unfold ArchimedeanQuotient.classOrderHom
  simp only [OrderHom.comp_coe, OrderHom.Subtype.val_coe, Function.comp_apply, Subtype.exists,
    Set.union_singleton, Set.mem_insert_iff, Set.mem_compl_iff, exists_prop, exists_eq_or_imp]
  by_cases ha : a = 1
  · left
    rw [ha]
    rw [AbsArchimedeanClass.orderHom_one]
  · right
    obtain ⟨b, h⟩ := AbsArchimedeanClass.orderHom_surjective (ArchimedeanQuotient.orderMonoidHom s)
      (ArchimedeanQuotient.surjective_OrderMonoidHom s) a
    use b
    constructor
    · contrapose! ha
      rw [← h]
      unfold AbsArchimedeanClass.orderHom AbsArchimedeanClass.orderHomFun
      simp only [OrderHom.coe_mk]
      apply (AbsArchimedeanClass.mk_eq_one _).mp
      unfold ArchimedeanQuotient.orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      unfold ArchimedeanSubgroup
      simp only [Subgroup.mem_mk, Set.mem_preimage]
      rw [AbsArchimedeanClass.out_eq]
      exact ha
    · exact h

theorem ArchimedeanQuotient.classOrderHom_injective (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
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
      rw [AbsArchimedeanClass.orderHom_one]
      unfold AbsArchimedeanClass.orderHom AbsArchimedeanClass.orderHomFun orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, OrderHom.coe_mk]
      intro h
      obtain h := (QuotientGroup.eq_one_iff _).mp ((AbsArchimedeanClass.mk_eq_one _).mpr h.symm)
      unfold ArchimedeanSubgroup at h
      simp only [Subgroup.mem_mk, Set.mem_preimage] at h
      rw [AbsArchimedeanClass.out_eq] at h
      obtain h := Set.not_mem_compl_iff.mpr h
      exact (Set.mem_singleton_iff.mp ((or_iff_right h).mp hb)).symm
    · rw [h1]
      rw [AbsArchimedeanClass.orderHom_one]
      unfold AbsArchimedeanClass.orderHom AbsArchimedeanClass.orderHomFun orderMonoidHom
      simp only [OrderMonoidHom.coe_mk, QuotientGroup.mk'_apply, OrderHom.coe_mk]
      intro h
      obtain h := (QuotientGroup.eq_one_iff _).mp ((AbsArchimedeanClass.mk_eq_one _).mpr h) --
      unfold ArchimedeanSubgroup at h
      simp only [Subgroup.mem_mk, Set.mem_preimage] at h
      rw [AbsArchimedeanClass.out_eq] at h
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

    rw [← AbsArchimedeanClass.out_eq a, ← AbsArchimedeanClass.out_eq b]
    rw [← AbsArchimedeanClass.orderHom_comm_mk, ← AbsArchimedeanClass.orderHom_comm_mk]

    rw [AbsArchimedeanClass.eq_iff, AbsArchimedeanClass.eq_iff]
    intro h
    obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := h
    rw [OrderMonoidHom.map_mabs, OrderMonoidHom.map_mabs, ← map_pow] at hm hn
    rw [ArchimedeanQuotient.le_def] at hm hn
    set A := mabs a.out
    set B := mabs b.out
    set An := A ^ n
    set Bm := B ^ m
    set A' := Quotient.out ((orderMonoidHom s) A)
    set B' := Quotient.out ((orderMonoidHom s) B)
    set An' := Quotient.out ((orderMonoidHom s) An)
    set Bm' := Quotient.out ((orderMonoidHom s) Bm)
    have hBpos : 1 ≤ B := one_le_mabs b.out
    have hAA : AbsArchimedeanClass.mk (A'⁻¹ * A) ∈ s.carrier := by sorry
    have hABmpos : 1 ≤ A'⁻¹ * Bm' := le_inv_mul_iff_le.mpr hm
    have hBBm : AbsArchimedeanClass.mk (Bm⁻¹ * Bm') ∈ s.carrier := by sorry

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
      have hpos: 1 ≤ A'⁻¹ * Bm' * B := one_le_mul hABmpos hBpos
      have hpos' : AbsArchimedeanClass.mk (A'⁻¹ * Bm' * B) ∉ s.carrier := by
        rw [← AbsArchimedeanClass.mk_mul_of_one_le hABmpos hBpos]
        suffices AbsArchimedeanClass.mk B ∉ s.carrier by
          contrapose! this with h
          exact s.upper' (min_le_right _ _) h
        unfold B
        rw [AbsArchimedeanClass.mk_mabs, AbsArchimedeanClass.out_eq]
        exact hb
      apply le_of_lt
      apply AbsArchimedeanClass.lt_of_mk_lt_mk _ hpos
      refine lt_of_lt_of_le ?_ (AbsArchimedeanClass.mk_mul _ _)
      apply lt_min
      · contrapose! hpos' with h
        exact s.upper' h hAA
      · contrapose! hpos' with h
        exact s.upper' h hBBm
    · sorry

noncomputable
def ArchimedeanQuotient.classOrderIso (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
    (s.carrierᶜ ∪ {1} : Set (AbsArchimedeanClass M)) ≃o (AbsArchimedeanClass (ArchimedeanQuotient s)) where
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

/-theorem ArchimedeanQuotient.same_class (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier]
    (a b : ArchimedeanQuotient s) :
    AbsArchimedeanClass.mk a = AbsArchimedeanClass.mk b ↔ AbsArchimedeanClass.mk a.out = AbsArchimedeanClass.mk b.out := by
  rw [AbsArchimedeanClass.eq_iff, AbsArchimedeanClass.eq_iff]
  simp_rw [← mabs_pow]
  simp_rw [ArchimedeanQuotient.le_def]
  sorry

theorem ArchimedeanQuotient.class_transfer (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier]
    (a b : M) (hs : AbsArchimedeanClass.mk a ∉ s.carrier) :
    AbsArchimedeanClass.mk (ArchimedeanQuotient.mk s a) = AbsArchimedeanClass.mk (ArchimedeanQuotient.mk s b) ↔
    AbsArchimedeanClass.mk a = AbsArchimedeanClass.mk b := by
  rw [AbsArchimedeanClass.eq_iff, AbsArchimedeanClass.eq_iff]
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
def ArchimedeanQuotient.class_map (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier]
    (a : AbsArchimedeanClass (ArchimedeanQuotient s)) : (s.carrierᶜ ∪ {1} : Set (AbsArchimedeanClass M)) :=
  ⟨if a = 1 then 1 else AbsArchimedeanClass.mk a.out.out, by
    by_cases ha : a = 1
    · simp [ha]
    · apply Set.mem_union_left
      simp only [ha, ↓reduceIte, Set.mem_compl_iff]
      obtain ha := (AbsArchimedeanClass.out_eq_one _).not.mpr ha
      rw [← QuotientGroup.out_eq' a.out] at ha
      obtain ha := (QuotientGroup.eq_one_iff _).not.mp ha
      unfold ArchimedeanSubgroup at ha
      simpa using ha
  ⟩

theorem ArchimedeanQuotient.class_map_injective (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
    Function.Surjective (ArchimedeanQuotient.class_map s) := by
  intro a
  obtain hmem|hmem := (Set.mem_union _ _ _).mp a.prop
  · use AbsArchimedeanClass.mk (ArchimedeanQuotient.mk s a.val.out)
    unfold class_map
    have : ¬ AbsArchimedeanClass.mk (mk s a.val.out) = 1 := by
      apply (ArchimedeanQuotient.class_one _ _).not.mpr
      rw [AbsArchimedeanClass.out_eq]
      simpa using hmem
    simp only [this, ↓reduceIte]

    sorry
  · use 1
    unfold class_map
    simp only [↓reduceIte]
    refine (Subtype.coe_eq_of_eq_mk ?_).symm
    simpa using hmem

noncomputable
def ArchimedeanQuotient.class_map_iso (s : UpperSet (AbsArchimedeanClass M)) [Nonempty s.carrier] :
    AbsArchimedeanClass (ArchimedeanQuotient s) ≃o (s.carrierᶜ ∪ {1} : Set (AbsArchimedeanClass M)) where
  toFun := ArchimedeanQuotient.class_map s
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry-/

abbrev ArchimedeanLayer (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] :=
  Subgroup.map (ArchimedeanQuotient.orderMonoidHom s).toMonoidHom (ArchimedeanSubgroup t)

noncomputable
instance ArchimedeanLayer.instLinearOrder (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : LinearOrder (ArchimedeanLayer s t) := by infer_instance

theorem ArchimedeanLayer.le_def (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : ∀ (x y : ArchimedeanLayer s t), x ≤ y ↔ x.val.out ≤ y.val.out := by
  intro x y
  rfl

instance ArchimedeanLayer.instIsOrderedMonoid (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] : IsOrderedMonoid (ArchimedeanLayer s t) := by infer_instance

/-
noncomputable
def ArchimedeanLayer.class_map (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] (a : AbsArchimedeanClass (ArchimedeanLayer s t)) :
    (s.carrier \ t.carrier ∪ {1} : Set (AbsArchimedeanClass M)) :=
  ⟨AbsArchimedeanClass.mk a.val.out.val.out, sorry⟩

def ArchimedeanLayer.class_orderIso (s t : UpperSet (AbsArchimedeanClass M))
    [Nonempty s.carrier] [Nonempty t.carrier] :
    AbsArchimedeanClass (ArchimedeanLayer s t) ≃o (s.carrier \ t.carrier ∪ {1} : Set (AbsArchimedeanClass M)) := by sorry
-/
