import CorelibVerification
import WadrayVerification.Aux
import WadrayVerification.Load

open Sierra

theorem Bool.toSierraBool_def (b : Bool) : b.toSierraBool = if b then .inr () else .inl () := by
  aesop

aegis_spec "wadray::wadray::cast_to_u256" :=
  fun _ a b ρ =>
  ρ = ((a, 0), (b, 0))

aegis_prove "wadray::wadray::cast_to_u256" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::WadPartialOrd::le" :=
  fun _ _ (a b : Wad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat ≤ b.toRat)

aegis_prove "wadray::wadray::WadPartialOrd::le" :=
  fun _ _ (a b : Wad) _ ρ => by
  unfold «spec_wadray::wadray::WadPartialOrd::le»
  aesop (add safe forward [Wad.toRat_le_toRat_of_val_le_val, Wad.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::WadPartialOrd::lt" :=
  fun _ _ (a b : Wad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < b.toRat)

aegis_prove "wadray::wadray::WadPartialOrd::lt" :=
  fun _ _ (a b : Wad) _ ρ => by
  unfold «spec_wadray::wadray::WadPartialOrd::lt»
  aesop (add safe forward [Wad.toRat_le_toRat_of_val_le_val, Wad.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::WadPartialOrd::gt" :=
  fun _ _ (a b : Wad) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat < a.toRat)

aegis_prove "wadray::wadray::WadPartialOrd::gt" :=
  fun _ _ (a b : Wad) _ ρ => by
  unfold «spec_wadray::wadray::WadPartialOrd::gt»
  aesop (add safe forward [Wad.toRat_le_toRat_of_val_le_val, Wad.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::WadPartialOrd::ge" :=
  fun _ _ (a b : Wad) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat ≤ a.toRat)

aegis_prove "wadray::wadray::WadPartialOrd::ge" :=
  fun _ _ (a b : Wad) _ ρ => by
  unfold «spec_wadray::wadray::WadPartialOrd::ge»
  aesop (add safe forward [Wad.toRat_le_toRat_of_val_le_val, Wad.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::RayPartialOrd::lt" :=
  fun _ _ (a b : Ray) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < b.toRat)

aegis_prove "wadray::wadray::RayPartialOrd::lt" :=
  fun _ _ (a b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayPartialOrd::lt»
  aesop (add safe forward [Ray.toRat_le_toRat_of_val_le_val, Ray.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::RayPartialOrd::gt" :=
  fun _ _ (a b : Ray) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat < a.toRat)

aegis_prove "wadray::wadray::RayPartialOrd::gt" :=
  fun _ _ (a b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayPartialOrd::gt»
  aesop (add safe forward [Ray.toRat_le_toRat_of_val_le_val, Ray.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::RayPartialOrd::le" :=
  fun _ _ (a b : Ray) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat ≤ b.toRat)

aegis_prove "wadray::wadray::RayPartialOrd::le" :=
  fun _ _ (a b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayPartialOrd::le»
  aesop (add safe forward [Ray.toRat_le_toRat_of_val_le_val, Ray.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::RayPartialOrd::ge" :=
  fun _ _ (a b : Ray) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat ≤ a.toRat)

aegis_prove "wadray::wadray::RayPartialOrd::ge" :=
  fun _ _ (a b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayPartialOrd::ge»
  aesop (add safe forward [Ray.toRat_le_toRat_of_val_le_val, Ray.toRat_lt_toRat_of_val_lt_val])

theorem U128_MOD_lt_U256_MOD : U128_MOD < U256_MOD := by norm_num[U128_MOD, U256_MOD]

theorem WAD_SCALE_val : (1000000000000000000 : UInt128).val = 1000000000000000000 := rfl

aegis_spec "wadray::wadray::u128_wmul" :=
  fun _ _ a b _ ρ =>
  (a.val * b.val / Wad.WAD_SCALE < U128_MOD ∧ ρ = .inl (a.val * b.val / Wad.WAD_SCALE))
  ∨ (U128_MOD ≤ a.val * b.val / Wad.WAD_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::u128_wmul" :=
  fun _ _ a b _ ρ => by
  unfold «spec_wadray::wadray::u128_wmul»
  sierra_simp'
  rintro ⟨_,(⟨h₁,rfl⟩|⟨h₁,h₁'⟩),h₂⟩
  · simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    rcases h₂ with (⟨_,_,h₂,h₃,h₄⟩|h₂)
    · injection h₂ with h₂; subst h₂
      rcases h₃ with (⟨_,_,rfl,h₅⟩|⟨h₃,_⟩)
      · rcases h₄ with (⟨⟨wₗ,wₕ⟩,v,h₄,h₆,h₇⟩|h₄)
        · injection h₄ with h₄; subst h₄
          simp [UInt256.val, UInt256.mul_def, ← ZMod.val_mul_val_eq_hmul] at h₅  -- TODO
          rw [UInt256.val_lt_U128_MOD_iff, UInt256.U128_MOD_le_val_iff] at h₆
          rcases h₆ with (⟨rfl,rfl⟩|⟨h₆,rfl⟩)
          · rw [ZMod.val_zero, mul_zero, zero_add] at h₅
            simp only [Sum.inl.injEq, exists_eq_left, Nat.cast_ofNat, Int.int_cast_ofNat,
              List.nil_append, false_and, exists_false, or_false] at h₇; cases h₇
            erw [← h₅]
            simp only [wₗ.val_lt, Sum.inl.injEq, true_and, Sum.isRight_inl, and_false, or_false]
            rw [@ZMod.nat_cast_zmod_val]
          · simp only [false_and, exists_false, Nat.cast_ofNat, Int.int_cast_ofNat,
              List.nil_append, true_and, exists_const, false_or] at h₇; cases h₇
            rw [← UInt256.U128_MOD_le_val_iff] at h₆
            erw [← h₅]
            refine .inr ⟨h₆, ?_⟩
            simp
        · simp only [false_and, exists_false] at h₄
      · injection h₃ with h₃
        rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h₃
        norm_num[U128_MOD] at h₃
    · simp at h₂
  · simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    right
    constructor
    · rw [Nat.le_div_iff_mul_le' Wad.WAD_SCALE_pos]
      apply le_trans _ h₁
      norm_num [U128_MOD, Wad.WAD_SCALE, U256_MOD]
    · rename_i x x_1 x_2 w
      simp_all only [Nat.cast_ofNat, Int.int_cast_ofNat, ne_eq, exists_and_left, List.nil_append, Prod.exists,
        Prod.mk.injEq, Sum.exists, Sum.inl.injEq, exists_eq_left', Sum.isRight_inl, and_false, or_false, false_and,
        exists_false, Sum.isRight_inr, and_true, false_or, Sum.inr.injEq, exists_eq_left]
      unhygienic aesop_cases h₂
      · unhygienic with_reducible aesop_destruct_products
        aesop_subst left
        simp_all only [Sum.isRight_inl]
      · unhygienic with_reducible aesop_destruct_products
        aesop_subst [right, left]
        simp_all only [Sum.isRight_inr]

aegis_spec "wadray::wadray::wmul" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) =>
  (a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE < U128_MOD ∧ ρ = .inl (a * b))
  ∨ (U128_MOD ≤ a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::wmul" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::wmul»
  sierra_simp'
  aesop

aegis_spec "wadray::wadray::WadPartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "wadray::wadray::WadPartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray::WadPartialEq::ne»
  aesop

aegis_spec "wadray::wadray::WadPartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "wadray::wadray::WadPartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray::WadPartialEq::eq»
  aesop

aegis_spec "wadray::wadray::RayPartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "wadray::wadray::RayPartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray::RayPartialEq::eq»
  aesop

aegis_spec "wadray::wadray::RayPartialEq::ne" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a ≠ b)

aegis_prove "wadray::wadray::RayPartialEq::ne" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray::RayPartialEq::ne»
  aesop

theorem RAY_SCALE_val :
    (1000000000000000000000000000 : UInt128).val = 1000000000000000000000000000 := rfl

aegis_spec "wadray::wadray::u128_rmul" :=
  fun _ _ a b _ ρ =>
  (a.val * b.val / Ray.RAY_SCALE < U128_MOD ∧ ρ = .inl (a.val * b.val / Ray.RAY_SCALE))
  ∨ (U128_MOD ≤ a.val * b.val / Ray.RAY_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::u128_rmul" :=
  fun _ _ a b _ ρ => by
  unfold «spec_wadray::wadray::u128_rmul»
  sierra_simp'
  rintro ⟨_,(⟨h₁,rfl⟩|⟨h₁,h₁'⟩),h₂⟩
  · simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    rcases h₂ with (⟨_,_,h₂,h₃,h₄⟩|h₂)
    · injection h₂ with h₂; subst h₂
      rcases h₃ with (⟨_,_,rfl,h₅⟩|⟨h₃,_⟩)
      · rcases h₄ with (⟨⟨wₗ,wₕ⟩,v,h₄,h₆,h₇⟩|h₄)
        · injection h₄ with h₄; subst h₄
          simp [UInt256.val, UInt256.mul_def, ← ZMod.val_mul_val_eq_hmul] at h₅  -- TODO
          rw [UInt256.val_lt_U128_MOD_iff, UInt256.U128_MOD_le_val_iff] at h₆
          rcases h₆ with (⟨rfl,rfl⟩|⟨h₆,rfl⟩)
          · rw [ZMod.val_zero, mul_zero, zero_add] at h₅
            simp only [Sum.inl.injEq, exists_eq_left, Nat.cast_ofNat, Int.int_cast_ofNat,
              List.nil_append, false_and, exists_false, or_false] at h₇; cases h₇
            erw [← h₅]
            simp only [wₗ.val_lt, Sum.inl.injEq, true_and, Sum.isRight_inl, and_false, or_false]
            rw [@ZMod.nat_cast_zmod_val]
          · simp only [false_and, exists_false, Nat.cast_ofNat, Int.int_cast_ofNat,
              List.nil_append, true_and, exists_const, false_or] at h₇; cases h₇
            rw [← UInt256.U128_MOD_le_val_iff] at h₆
            erw [← h₅]
            refine .inr ⟨h₆, ?_⟩
            simp
        · simp only [false_and, exists_false] at h₄
      · injection h₃ with h₃
        rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h₃
        norm_num[U128_MOD] at h₃
    · simp at h₂
  · simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    right
    constructor
    · rw [Nat.le_div_iff_mul_le' Ray.RAY_SCALE_pos]
      apply le_trans _ h₁
      norm_num [U128_MOD, Ray.RAY_SCALE, U256_MOD]
    · rename_i x x_1 x_2 w
      simp_all only [Nat.cast_ofNat, Int.int_cast_ofNat, ne_eq, exists_and_left, List.nil_append, Prod.exists,
        Prod.mk.injEq, Sum.exists, Sum.inl.injEq, exists_eq_left', Sum.isRight_inl, and_false, or_false, false_and,
        exists_false, Sum.isRight_inr, and_true, false_or, Sum.inr.injEq, exists_eq_left]
      unhygienic aesop_cases h₂
      · unhygienic with_reducible aesop_destruct_products
        aesop_subst left
        simp_all only [Sum.isRight_inl]
      · unhygienic with_reducible aesop_destruct_products
        aesop_subst [right, left]
        simp_all only [Sum.isRight_inr]

aegis_spec "wadray::wadray::rmul" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE < U128_MOD ∧ ρ = .inl (a * b))
  ∨ (U128_MOD ≤ a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::rmul" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rmul»
  sierra_simp'
  aesop

aegis_spec "wadray::wadray::WadSub::sub" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) =>
  (b.toRat ≤ a.toRat ∧ ρ = .inl (a - b))
  ∨ (a.toRat < b.toRat ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadSub::sub" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::WadSub::sub»
  aesop (add safe forward [Wad.toRat_le_toRat_of_val_le_val, Wad.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::WadAdd::add" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) =>
  (a.toZMod.val + b.toZMod.val < U128_MOD ∧ ρ = .inl (a + b))
  ∨ (U128_MOD ≤ a.toZMod.val + b.toZMod.val ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadAdd::add" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::WadAdd::add»
  aesop

aegis_spec "wadray::wadray::RaySub::sub" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (b.toRat ≤ a.toRat ∧ ρ = .inl (a - b))
  ∨ (a.toRat < b.toRat ∧ ρ.isRight)

aegis_prove "wadray::wadray::RaySub::sub" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::RaySub::sub»
  aesop (add safe forward [Ray.toRat_le_toRat_of_val_le_val, Ray.toRat_lt_toRat_of_val_lt_val])

aegis_spec "wadray::wadray::RayAdd::add" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (a.toZMod.val + b.toZMod.val < U128_MOD ∧ ρ = .inl (a + b))
  ∨ (U128_MOD ≤ a.toZMod.val + b.toZMod.val ∧ ρ.isRight)

aegis_prove "wadray::wadray::RayAdd::add" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::RayAdd::add»
  aesop

aegis_spec "wadray::wadray::WadZeroable::is_non_zero" :=
  fun _ (a : Wad) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 0)

aegis_prove "wadray::wadray::WadZeroable::is_non_zero" :=
  fun _ (a : Wad) ρ => by
  unfold «spec_wadray::wadray::WadZeroable::is_non_zero»
  aesop (add simp norm [Wad.toRat, Wad.toZMod, ZMod.cast_rat_eq_zero_iff])

aegis_spec "wadray::wadray::WadZeroable::is_zero" :=
  fun _ (a : Wad) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 0)

aegis_prove "wadray::wadray::WadZeroable::is_zero" :=
  fun _ (a : Wad) ρ => by
  unfold «spec_wadray::wadray::WadZeroable::is_zero»
  aesop (add simp norm [Bool.toSierraBool_def, Wad.toRat, ZMod.cast_rat_eq_zero_iff, Wad.toZMod])

aegis_spec "wadray::wadray::RayZeroable::is_zero" :=
  fun _ (a : Ray) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 0)

aegis_prove "wadray::wadray::RayZeroable::is_zero" :=
  fun _ (a : Ray) ρ => by
  unfold «spec_wadray::wadray::RayZeroable::is_zero»
  aesop (add simp norm [Bool.toSierraBool_def, Ray.toRat, ZMod.cast_rat_eq_zero_iff, Ray.toZMod])

aegis_spec "wadray::wadray::RayZeroable::is_non_zero" :=
  fun _ (a : Ray) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 0)

aegis_prove "wadray::wadray::RayZeroable::is_non_zero" :=
  fun _ (a : Ray) ρ => by
  unfold «spec_wadray::wadray::RayZeroable::is_non_zero»
  aesop (add simp norm [Ray.toRat, Ray.toZMod, ZMod.cast_rat_eq_zero_iff])

aegis_spec "wadray::wadray::BoundedWad::min" :=
  fun _ ρ =>
  ρ = 0

aegis_prove "wadray::wadray::BoundedWad::min" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::BoundedRay::min" :=
  fun _ ρ =>
  ρ = 0

aegis_prove "wadray::wadray::BoundedRay::min" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::BoundedWad::max" :=
  fun _ ρ =>
  ρ = U128_MOD - 1

aegis_prove "wadray::wadray::BoundedWad::max" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::BoundedRay::max" :=
  fun _ ρ =>
  ρ = U128_MOD - 1

aegis_prove "wadray::wadray::BoundedRay::max" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::WadAddEq::add_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) =>
  (a.toZMod.val + b.toZMod.val < U128_MOD ∧ ρ = .inl (a + b, ()))
  ∨ (U128_MOD ≤ a.toZMod.val + b.toZMod.val ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadAddEq::add_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) => by
  unfold «spec_wadray::wadray::WadAddEq::add_eq»
  aesop

aegis_spec "wadray::wadray::WadSubEq::sub_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) =>
  (b.toRat ≤ a.toRat ∧ ρ = .inl (a - b, ()))
  ∨ (a.toRat < b.toRat ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadSubEq::sub_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) => by
  unfold «spec_wadray::wadray::WadSubEq::sub_eq»
  aesop

aegis_spec "wadray::wadray::WadMulEq::mul_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) =>
  (a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE < U128_MOD ∧ ρ = .inl (a * b, ()))
  ∨ (U128_MOD ≤ a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadMulEq::mul_eq" :=
  fun _ _ (a b : Wad) _ (ρ : Wad × _ ⊕ _) => by
  unfold «spec_wadray::wadray::WadMulEq::mul_eq»
  aesop

aegis_spec "wadray::wadray::TIntoWad<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into" :=
  fun _ a (ρ : Wad) =>
  ρ = a

aegis_prove "wadray::wadray::TIntoWad<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into" :=
  fun _ a (ρ : Wad) => by
  unfold «spec_wadray::wadray::TIntoWad<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into»
  aesop

aegis_spec "wadray::wadray::TIntoRay<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into" :=
  fun _ a (ρ : Ray) =>
  ρ = a

aegis_prove "wadray::wadray::TIntoRay<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into" :=
  fun _ a (ρ : Ray) => by
  unfold «spec_wadray::wadray::TIntoRay<core::integer::u128, core::traits::TIntoT<core::integer::u128>>::into»
  aesop

aegis_spec "wadray::wadray::u128_wdiv" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) =>
  a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val < U128_MOD
    ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b)
  ∨ (U128_MOD ≤ a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight

aegis_prove "wadray::wadray::u128_wdiv" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) => by
  sierra_simp'
  unfold «spec_wadray::wadray::u128_wdiv»
  rintro ⟨(x|x),h₁,h₂⟩
  · simp_all only [Nat.cast_ofNat, Int.int_cast_ofNat, Sum.inl.injEq, Sum.isRight_inl, and_false,
      or_false, ne_eq, exists_and_left, List.nil_append, exists_and_right, Sum.exists,
      exists_eq_left, exists_false, false_and, and_true, false_or, exists_const, true_and,
      Prod.exists, exists_eq_left', Prod.mk.injEq, Sum.isRight_inr, Sum.inr.injEq, ZMod.val_eq_zero]
    rcases h₁ with ⟨h₁,rfl⟩
    simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    rcases h₂ with (⟨_,_,⟨h₂,h₄⟩,_,_,⟨rfl,rfl⟩,h₃⟩|⟨h₂,_,_,rfl⟩)
    · simp [h₄, UInt256.val] at h₃
      simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add,
        UInt256.mul_def, mul_zero, add_zero, zero_mul] at h₄
      rcases ρ with (ρ|ρ)
      · simp only [Sum.inl.injEq, Sum.isRight_inl, and_false, or_false] at h₃ ⊢
        rcases h₃ with ⟨_,⟨h₃,rfl⟩,rfl⟩
        refine ⟨?_,?_,?_⟩
        · rwa [h₄, ← ZMod.val_mul_val_eq_hmul] at h₃
        · simp only [UInt256.zero_def] at h₂
          simp only [Wad.toZMod]
          apply Aesop.BuiltinRules.not_intro
          intro h
          aesop_subst h
          simp_all only [not_true]
        · simp only [Wad.div_def, Wad.WAD_SCALE]
          rw [← ZMod.val_mul_val_eq_hmul] at h₄
          erw [← h₄]; clear h₄
          simp [Nat.eq_zero_of_mul_lt_right (Nat.lt_of_add_lt h₃)]
      · simp only [and_false, exists_false, Sum.inr.injEq, false_or] at h₃
        simp only [and_false, Sum.isRight_inr, and_true, false_or]
        left
        rcases h₃ with ⟨h₃,rfl⟩
        rwa [h₄, ← ZMod.val_mul_val_eq_hmul] at h₃
    · simp only [and_false, Sum.isRight_inr, and_true, false_or]
      right
      injection h₂
  · simp_all only [UInt256.val, ZMod.val_zero, mul_zero, zero_add, Nat.cast_ofNat,
      Int.int_cast_ofNat, and_false, Sum.isRight_inr, and_true, false_or, ne_eq, exists_and_left,
      List.nil_append, exists_and_right, Sum.exists, Sum.inl.injEq, or_false, exists_eq_left,
      exists_false, false_and, exists_const, true_and, Prod.exists, Sum.inr.injEq]
    subst h₂
    simp only [and_false, Sum.isRight_inr, and_true, false_or]
    by_cases h₃ : b.toZMod.val = 0
    · simp [h₃]
    · left
      conv => lhs; rw [← U256_MOD_div]
      trans; apply Nat.div_le_div_left (le_of_lt b.toZMod.val_lt) (Nat.pos_of_ne_zero h₃)
      apply Nat.div_le_div_right h₁

aegis_spec "wadray::wadray::u128_rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b))
  ∨ ((U128_MOD ≤ a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

aegis_prove "wadray::wadray::u128_rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  sierra_simp'
  unfold «spec_wadray::wadray::u128_rdiv»
  rintro ⟨(x|x),h₁,h₂⟩
  · simp_all only [Nat.cast_ofNat, Int.int_cast_ofNat, Sum.inl.injEq, Sum.isRight_inl, and_false,
      or_false, ne_eq, exists_and_left, List.nil_append, exists_and_right, Sum.exists,
      exists_eq_left, exists_false, false_and, and_true, false_or, exists_const, true_and,
      Prod.exists, exists_eq_left', Prod.mk.injEq, Sum.isRight_inr, Sum.inr.injEq, ZMod.val_eq_zero]
    rcases h₁ with ⟨h₁,rfl⟩
    simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add] at h₁
    rcases h₂ with (⟨_,_,⟨h₂,h₄⟩,_,_,⟨rfl,rfl⟩,h₃⟩|⟨h₂,_,_,rfl⟩)
    · simp [h₄, UInt256.val] at h₃
      simp only [UInt256.val, ZMod.val_zero, mul_zero, zero_add,
        UInt256.mul_def, mul_zero, add_zero, zero_mul] at h₄
      rcases ρ with (ρ|ρ)
      · simp only [Sum.inl.injEq, Sum.isRight_inl, and_false, or_false] at h₃ ⊢
        rcases h₃ with ⟨_,⟨h₃,rfl⟩,rfl⟩
        refine ⟨?_,?_,?_⟩
        · rwa [h₄, ← ZMod.val_mul_val_eq_hmul] at h₃
        · simp only [UInt256.zero_def] at h₂
          simp only [Ray.toZMod]
          apply Aesop.BuiltinRules.not_intro
          intro h
          aesop_subst h
          simp_all only [not_true]
        · simp only [Ray.div_def, Ray.RAY_SCALE]
          rw [← ZMod.val_mul_val_eq_hmul] at h₄
          erw [← h₄]; clear h₄
          simp [Nat.eq_zero_of_mul_lt_right (Nat.lt_of_add_lt h₃)]
      · simp only [and_false, exists_false, Sum.inr.injEq, false_or] at h₃
        simp only [and_false, Sum.isRight_inr, and_true, false_or]
        left
        rcases h₃ with ⟨h₃,rfl⟩
        rwa [h₄, ← ZMod.val_mul_val_eq_hmul] at h₃
    · simp only [and_false, Sum.isRight_inr, and_true, false_or]
      right
      injection h₂
  · simp_all only [UInt256.val, ZMod.val_zero, mul_zero, zero_add, Nat.cast_ofNat,
      Int.int_cast_ofNat, and_false, Sum.isRight_inr, and_true, false_or, ne_eq, exists_and_left,
      List.nil_append, exists_and_right, Sum.exists, Sum.inl.injEq, or_false, exists_eq_left,
      exists_false, false_and, exists_const, true_and, Prod.exists, Sum.inr.injEq]
    subst h₂
    simp only [and_false, Sum.isRight_inr, and_true, false_or]
    by_cases h₃ : b.toZMod.val = 0
    · simp [h₃]
    · left
      conv => lhs; rw [← U256_MOD_div]
      trans; apply Nat.div_le_div_left (le_of_lt b.toZMod.val_lt) (Nat.pos_of_ne_zero h₃)
      apply Nat.div_le_div_right h₁

aegis_spec "wadray::wadray::wdiv" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) =>
  (a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b))
  ∨ ((U128_MOD ≤ a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

aegis_prove "wadray::wadray::wdiv" :=
  fun _ _ (a b : Wad) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::wdiv»
  aesop

aegis_spec "wadray::wadray::WadDivEq::div_eq" :=
  fun _ _ (a b : Wad) _ (ρ : (Wad × _) ⊕ _) =>
  (a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b, ()))
  ∨ ((U128_MOD ≤ a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

aegis_prove "wadray::wadray::WadDivEq::div_eq" :=
  fun _ _ (a b : Wad) _ (ρ : (Wad × _) ⊕ _) => by
  unfold «spec_wadray::wadray::WadDivEq::div_eq»
  aesop

aegis_spec "wadray::wadray::rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b))
  ∨ ((U128_MOD ≤ a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

aegis_prove "wadray::wadray::rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rdiv»
  aesop

aegis_spec "wadray::wadray::RayIntoWad::into" :=
  fun _ _ (a : Ray) _ ρ =>
  ρ = .inl a.toWad

aegis_prove "wadray::wadray::RayIntoWad::into" :=
  fun _ _ (a : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayIntoWad::into»
  rintro ⟨_,_,_,(h|h),h'⟩
  · rcases h' with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · rcases h with ⟨_,ρ',h₁,h₂⟩
      cases h₁
      congr
      simp only [Ray.toWad, ZMod.ndiv, U128_MOD]
      apply ZMod.val_injective
      exact h₂
    · simp at h
  · rcases h with ⟨h,-⟩
    rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h
    norm_num [U128_MOD] at h

aegis_spec "wadray::wadray::WadIntoU256::into" :=
  fun _ a ρ =>
  ρ = (a, 0)

aegis_prove "wadray::wadray::WadIntoU256::into" :=
  fun _ a ρ => by
  unfold «spec_wadray::wadray::WadIntoU256::into»
  rintro rfl
  rfl

aegis_spec "wadray::wadray::U256TryIntoWad::try_into" :=
  fun _ (a : UInt256) ρ =>
  (a.val < U128_MOD ∧ ρ = .inl a.1)
  ∨ (U128_MOD ≤ a.val ∧ ρ = .inr ())

aegis_prove "wadray::wadray::U256TryIntoWad::try_into" :=
  fun _ (a : UInt256) ρ => by
  unfold «spec_wadray::wadray::U256TryIntoWad::try_into»
  aesop

aegis_spec "wadray::wadray::TIntoRay<core::integer::u64, core::integer::UpcastableInto<core::integer::u64, core::integer::u128, core::integer::UpcastableU64U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoRay<core::integer::u64, core::integer::UpcastableInto<core::integer::u64, core::integer::u128, core::integer::UpcastableU64U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoRay<core::integer::u32, core::integer::UpcastableInto<core::integer::u32, core::integer::u128, core::integer::UpcastableU32U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoRay<core::integer::u32, core::integer::UpcastableInto<core::integer::u32, core::integer::u128, core::integer::UpcastableU32U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoRay<core::integer::u16, core::integer::UpcastableInto<core::integer::u16, core::integer::u128, core::integer::UpcastableU16U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoRay<core::integer::u16, core::integer::UpcastableInto<core::integer::u16, core::integer::u128, core::integer::UpcastableU16U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoRay<core::integer::u8, core::integer::UpcastableInto<core::integer::u8, core::integer::u128, core::integer::UpcastableU8U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoRay<core::integer::u8, core::integer::UpcastableInto<core::integer::u8, core::integer::u128, core::integer::UpcastableU8U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoWad<core::integer::u64, core::integer::UpcastableInto<core::integer::u64, core::integer::u128, core::integer::UpcastableU64U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoWad<core::integer::u64, core::integer::UpcastableInto<core::integer::u64, core::integer::u128, core::integer::UpcastableU64U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoWad<core::integer::u32, core::integer::UpcastableInto<core::integer::u32, core::integer::u128, core::integer::UpcastableU32U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoWad<core::integer::u32, core::integer::UpcastableInto<core::integer::u32, core::integer::u128, core::integer::UpcastableU32U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoWad<core::integer::u16, core::integer::UpcastableInto<core::integer::u16, core::integer::u128, core::integer::UpcastableU16U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoWad<core::integer::u16, core::integer::UpcastableInto<core::integer::u16, core::integer::u128, core::integer::UpcastableU16U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::TIntoWad<core::integer::u8, core::integer::UpcastableInto<core::integer::u8, core::integer::u128, core::integer::UpcastableU8U128>>::into" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "wadray::wadray::TIntoWad<core::integer::u8, core::integer::UpcastableInto<core::integer::u8, core::integer::u128, core::integer::UpcastableU8U128>>::into" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray::WadTryIntoRay::try_into" :=
  fun _ _ (a : Wad) _ (ρ : (Ray ⊕ _) ⊕ _) =>
  ρ = if (a.toZMod.val ≤ Wad.MAX_CONVERTIBLE_WAD) then .inl (.inl a.toRay)
      else .inl (.inr ())

aegis_prove "wadray::wadray::WadTryIntoRay::try_into" :=
  fun _ _ (a : Wad) _ (ρ : (Ray ⊕ _) ⊕ _) => by
  unfold «spec_wadray::wadray::WadTryIntoRay::try_into»
  have h₁ : ZMod.val (340282366920938463463374607431 : UInt128) = Wad.MAX_CONVERTIBLE_WAD := rfl
  have h₂ : ZMod.val (1000000000 : UInt128) = 1000000000 := rfl
  rintro ⟨_,_,_,(h|h)⟩
  · rcases h with ⟨h₃,(h₄|h₄),h₅⟩
    · aesop
    · rcases h₅ with (h₅|⟨rfl,rfl⟩)
      · aesop
      · simp only [Int.ofNat_eq_coe, Nat.cast_ofNat, Int.int_cast_ofNat, Sum.isRight_inr,
          and_true] at h₃ h₄
        rw [h₂] at h₄
        rw [h₁] at h₃
        replace h₄ := h₄.trans (Nat.mul_le_mul_right 1000000000 h₃)
        norm_num [U128_MOD, Wad.MAX_CONVERTIBLE_WAD] at h₄
  · aesop

aegis_spec "wadray::wadray::scale_u128_by_ray" :=
  fun _ _ a (b : Ray) _ ρ =>
  (a.val * b.toZMod.val / Ray.RAY_SCALE < U128_MOD ∧ ρ = .inl (a.val * b.toZMod.val / Ray.RAY_SCALE))
  ∨ (U128_MOD ≤ a.val * b.toZMod.val / Ray.RAY_SCALE ∧ ρ.isRight)

aegis_prove "wadray::wadray::scale_u128_by_ray" :=
  fun _ _ a (b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::scale_u128_by_ray»
  aesop

aegis_spec "wadray::wadray::div_u128_by_ray" :=
  fun _ _ a (b : Ray) _ ρ =>
  a.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0
    ∧ ρ = .inl (a.val * Ray.RAY_SCALE / b.toZMod.val)
  ∨ (U128_MOD ≤ a.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight

aegis_prove "wadray::wadray::div_u128_by_ray" :=
  fun _ _ a (b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::div_u128_by_ray»
  aesop

aegis_spec "wadray::wadray::wmul_wr" :=
  fun _ _ (a : Wad) (b : Ray) _ (ρ : Ray ⊕ _) =>
  a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE < U128_MOD
    ∧ ρ = .inl (Ray.ofZMod (a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE))
  ∨ U128_MOD ≤ a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray::wmul_wr" :=
  fun _ _ (a : Wad) (b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::wmul_wr»
  aesop

aegis_spec "wadray::wadray::wmul_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Ray ⊕ _) =>
  a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE < U128_MOD
    ∧ ρ = .inl (Ray.ofZMod (a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE))
  ∨ U128_MOD ≤ a.toZMod.val * b.toZMod.val / Wad.WAD_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray::wmul_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::wmul_rw»
  aesop (add simp [mul_comm])

aegis_spec "wadray::wadray::rmul_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Wad ⊕ _) =>
  a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE < U128_MOD
    ∧ ρ = .inl (Ray.ofZMod (a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE))
  ∨ U128_MOD ≤ a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray::rmul_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rmul_rw»
  aesop (add simp [mul_comm])

aegis_spec "wadray::wadray::rmul_wr" :=
  fun _ _ (a : Wad) (b : Ray) _ (ρ : Wad ⊕ _) =>
  a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE < U128_MOD
    ∧ ρ = .inl (Ray.ofZMod (a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE))
  ∨ U128_MOD ≤ a.toZMod.val * b.toZMod.val / Ray.RAY_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray::rmul_wr" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rmul_wr»
  aesop (add simp [mul_comm])

aegis_spec "wadray::wadray::rdiv_wr" :=
  fun _ _ (a : Wad) (b : Ray) _ (ρ : Wad ⊕ _) =>
  a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD
    ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (Wad.ofZMod (a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val))
  ∨ (U128_MOD ≤ a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight

aegis_prove "wadray::wadray::rdiv_wr" :=
  fun _ _ (a : Wad) (b : Ray) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::rdiv_wr»
  aesop

aegis_spec "wadray::wadray::wdiv_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Ray ⊕ _) =>
  a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val < U128_MOD
    ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (Ray.ofZMod (a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val))
  ∨ (U128_MOD ≤ a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight

aegis_prove "wadray::wadray::wdiv_rw" :=
  fun _ _ (a : Ray) (b : Wad) _ (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray::wdiv_rw»
  aesop

aegis_spec "wadray::wadray::rdiv_ww" :=
  fun _ _ (a b : Wad) _ (ρ : Ray ⊕ _) =>
  a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD
    ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (Wad.ofZMod (a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val))
  ∨ (U128_MOD ≤ a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight

aegis_prove "wadray::wadray::rdiv_ww" :=
  fun _ _ (a b : Wad) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rdiv_ww»
  aesop


/-
aegis_spec "core::starknet::SyscallResultTraitImpl<(wadray::wadray::Ray, wadray::wadray::Ray)>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<(wadray::wadray::Ray, wadray::wadray::Ray)>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<(wadray::wadray::Wad, wadray::wadray::Wad)>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<(wadray::wadray::Wad, wadray::wadray::Wad)>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self]

aegis_spec "core::starknet::SyscallResultTraitImpl<wadray::wadray::Wad>::unwrap_syscall" :=
  fun _ a ρ =>
  (∃ x, a = .inl x ∧ ρ = .inl x) ∨ a.isRight ∧ ρ.isRight

aegis_prove "core::starknet::SyscallResultTraitImpl<wadray::wadray::Wad>::unwrap_syscall" :=
  fun _ a ρ => by
  rintro ⟨_,_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · left; simp only [Sum.inl.injEq, and_self, exists_eq']
  · right; simp only [Sum.isRight_inr, and_self] -/
