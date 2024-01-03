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

aegis_spec "wadray::wadray::RayPartialOrd::le" :=
  fun _ _ (a b : Ray) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat ≤ b.toRat)

aegis_prove "wadray::wadray::RayPartialOrd::le" :=
  fun _ _ (a b : Ray) _ ρ => by
  unfold «spec_wadray::wadray::RayPartialOrd::le»
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

aegis_spec "wadray::wadray::RayPartialEq::eq" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (a = b)

aegis_prove "wadray::wadray::RayPartialEq::eq" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray::RayPartialEq::eq»
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

aegis_spec "wadray::wadray::RayZeroable::is_non_zero" :=
  fun _ (a : Ray) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 0)

aegis_prove "wadray::wadray::RayZeroable::is_non_zero" :=
  fun _ (a : Ray) ρ => by
  unfold «spec_wadray::wadray::RayZeroable::is_non_zero»
  aesop (add simp norm [Ray.toRat, Ray.toZMod, ZMod.cast_rat_eq_zero_iff])

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
  (a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b))
  ∨ ((U128_MOD ≤ a.toZMod.val * Wad.WAD_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

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

aegis_spec "wadray::wadray::rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) =>
  (a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val < U128_MOD ∧ b.toZMod.val ≠ 0 ∧ ρ = .inl (a / b))
  ∨ ((U128_MOD ≤ a.toZMod.val * Ray.RAY_SCALE / b.toZMod.val ∨ b.toZMod.val = 0) ∧ ρ.isRight)

aegis_prove "wadray::wadray::rdiv" :=
  fun _ _ (a b : Ray) _ (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray::rdiv»
  aesop

-- TODO maybe weaken to soundness only
/-aegis_spec "wadray::wadray::fixed_point_to_wad" :=
  fun m _ gas n decimals _ _ (ρ : Wad ⊕ _) =>
  let i : Identifier := (id!"wadray::pow::pow10")
  (decimals.val ≤ 18 ∧ (19 - decimals.val) * m.costs i ≤ gas ∧ ∃ ρ', ρ = .inl ρ' ∧ ρ'.toRat = n.val / 10 ^ decimals.val)
  ∨ ((18 < decimals.val ∨ gas < (19 - decimals.val) * m.costs i) ∧ ρ.isRight)

aegis_prove "wadray::wadray::fixed_point_to_wad" :=
  fun _ _ _ n decimals _ _ (ρ : Wad ⊕ _) => by
  sierra_simp'
  unfold «spec_wadray::wadray::fixed_point_to_wad»
  rintro (h₁|h₁)
  · rcases h₁ with ⟨_,h₁,h₂,h₃⟩
    simp only [h₁] at h₂
    rcases h₂ with (⟨-,rfl⟩|h₂)
    · rcases h₃ with (⟨_,_,h₃,h₄,h₅⟩|h₃)
      · injection h₃ with h₃; subst h₃
        rcases h₅ with (⟨_,_,rfl,h₅⟩|⟨_,rfl,rfl⟩)
        · sorry
        · simp at h₄
          sorry
      · simp_all
    · aesop
  · aesop-/

/-aegis_spec "wadray::wadray::WadSerde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "wadray::wadray::WadSerde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_wadray::wadray::WadSerde::serialize»
  rintro rfl
  rfl-/

/-aegis_spec "wadray::wadray::WadSerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U128_MOD)).map ZMod.cast).toSum

aegis_prove "wadray::wadray::WadSerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_wadray::wadray::WadSerde::deserialize»
  aesop-/

/-aegis_spec "wadray::wadray::RaySerde::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.cast]

aegis_prove "wadray::wadray::RaySerde::serialize" :=
  fun _ a b ρ _ => by
  unfold «spec_wadray::wadray::RaySerde::serialize»
  rintro rfl
  rfl-/

/-aegis_spec "wadray::wadray::RaySerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = ((a.head?.filter (·.val < U128_MOD)).map ZMod.cast).toSum

aegis_prove "wadray::wadray::RaySerde::deserialize" :=
  fun _ _ a _ ρ₁ ρ₂ => by
  unfold «spec_wadray::wadray::RaySerde::deserialize»
  aesop-/

/-aegis_spec "core::cmp::min<wadray::wadray::Wad, wadray::wadray::WadPartialOrd, wadray::wadray::WadDrop, wadray::wadray::WadCopy>" :=
  fun _ _ (a b : Wad) _ ρ =>
  (b.toRat < a.toRat ∧ ρ = b) ∨ (a.toRat ≤ b.toRat ∧ ρ = a)

aegis_prove "core::cmp::min<wadray::wadray::Wad, wadray::wadray::WadPartialOrd, wadray::wadray::WadDrop, wadray::wadray::WadCopy>" :=
  fun _ _ (a b : Wad) _ ρ => by
  unfold «spec_core::cmp::min<wadray::wadray::Wad, wadray::wadray::WadPartialOrd, wadray::wadray::WadDrop, wadray::wadray::WadCopy>»
  aesop-/

/-aegis_spec "core::serde::TupleSize2Serde<wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.cast]

aegis_prove "core::serde::TupleSize2Serde<wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize2Serde<wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize»
  simp-/

/-aegis_spec "core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.cast]

aegis_prove "core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop>::serialize»
  simp-/

/-aegis_spec "core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.cast]

aegis_prove "core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize2Serde<wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize»
  simp-/

/-aegis_spec "core::serde::TupleSize3Serde<wadray::wadray::Wad, wadray::wadray::Wad, core::integer::u64, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.1.cast, a.2.2.cast]

aegis_prove "core::serde::TupleSize3Serde<wadray::wadray::Wad, wadray::wadray::Wad, core::integer::u64, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize3Serde<wadray::wadray::Wad, wadray::wadray::Wad, core::integer::u64, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize»
  simp-/

/-aegis_spec "core::serde::TupleSize3Serde<wadray::wadray::Ray, wadray::wadray::Ray, core::integer::u64, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.1.cast, a.2.2.cast]

aegis_prove "core::serde::TupleSize3Serde<wadray::wadray::Ray, wadray::wadray::Ray, core::integer::u64, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize3Serde<wadray::wadray::Ray, wadray::wadray::Ray, core::integer::u64, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, core::serde::U64Serde, core::integer::u64Drop>::serialize»
  simp-/

/-aegis_spec "core::serde::TupleSize4Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ =>
  ρ = b ++ [a.1.cast, a.2.1.cast, a.2.2.1.cast, a.2.2.2.cast]

aegis_prove "core::serde::TupleSize4Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize" :=
  fun _ a b ρ _ => by
  rintro ⟨_,_,_,_,rfl,rfl⟩
  unfold «spec_core::serde::TupleSize4Serde<wadray::wadray::Ray, wadray::wadray::Ray, wadray::wadray::Wad, wadray::wadray::Wad, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::RaySerde, wadray::wadray::RayDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop, wadray::wadray::WadSerde, wadray::wadray::WadDrop>::serialize»
  simp-/

/-aegis_spec "core::serde::serialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" :=
  fun m _ gas data str _ gas' ρ =>
  let c := m.costs id!"core::serde::serialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>"
    if (data.length + 1) * c ≤ gas then
    gas' = gas - (data.length + 1) * c ∧ ρ = .inl (str ++ data.map ZMod.cast, ())
  else ρ.isRight

aegis_prove "core::serde::serialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" :=
  fun m _ gas data str _ gas' ρ => by
  unfold «spec_core::serde::serialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>»
  sierra_simp'
  generalize m.costs id!"core::serde::serialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" = c
  rintro (⟨hle,h⟩|⟨h,rfl⟩)
  · rcases h with (⟨a,b,_,d,e,rfl,h₁,h₂,h₃⟩|⟨rfl,rfl,rfl⟩)
    · injection h₁ with h₁; subst h₁
      split_ifs at h₂ with hle'
      · rcases h₂ with ⟨rfl,rfl⟩
        have : (a.length + 2) * c ≤ gas
        · have := Nat.add_le_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.append_assoc, List.singleton_append, Sum.inl.injEq, ge_iff_le,
          tsub_le_iff_right, exists_and_left, exists_and_right, exists_eq_left, Prod.mk.injEq,
          and_true, exists_const, false_and, exists_false, or_false] at h₃
        rcases h₃ with ⟨rfl,rfl⟩
        simp only [List.length_cons, this, ge_iff_le, tsub_le_iff_right, and_true, Sum.isRight_inl,
          ite_true]
        rw [add_mul, one_mul, add_mul, Nat.succ_mul, one_mul, Nat.sub_sub]
        simp only [List.map_cons, and_true]
        ac_rfl
      · have : ¬ (a.length + 2) * c ≤ gas
        · rw [not_le] at hle' ⊢
          have := Nat.add_lt_add_right hle' c
          rw [Nat.sub_add_cancel hle] at this
          linarith
        simp only [List.length_cons, this, ge_iff_le, ite_false]
        aesop
    · simp [hle]
  · have : ¬ (data.length + 1) * c ≤ gas
    · rw [not_le, Nat.add_mul, one_mul]; apply Nat.lt_add_left h
    simp_all [this, prop_if_false_true]

aegis_spec "core::serde::deserialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" :=
  fun m _ gas s curr r _ gas' ρ =>
  let c := m.costs id!"core::serde::deserialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>"
  if ((s.takeWhileN (·.val < U128_MOD) r.val).length + 1) * c ≤ gas then
    if r.val ≤ s.length ∧ (s.take r.val).all (·.val < U128_MOD) then
      gas' = gas - (r.val + 1) * c
      ∧ ρ = .inl (s.drop r.val, .inl (curr ++ (s.take r.val).map .cast))
    else ρ = .inl ((s.dropWhileN (·.val < U128_MOD) r.val).tail, .inr ())
  else ρ.isRight

aegis_prove "core::serde::deserialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" :=
  fun m _ gas s curr r _ gas' ρ => by
  unfold «spec_core::serde::deserialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>»
  generalize Metadata.costs m id!"core::serde::deserialize_array_helper<wadray::wadray::Ray, wadray::wadray::RaySerde, wadray::wadray::RayDrop>" = c
  rintro ⟨hd,_,_,_,_,_,_,_,(⟨hle,h⟩|⟨h,rfl⟩)⟩
  -- Case: Enough gas for one run
  · rcases h with (⟨rfl,rfl,rfl⟩|⟨hne,h⟩)
    -- Case: `r = 0`
    · simp [hle]
    -- Case: `r ≠ 0`
    · have hr' : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ZMod.val_ne_zero]
      have hr : (r - 1).val = r.val - 1 := by apply ZMod.val_sub; rwa [ZMod.val_one]
      rcases h with (⟨hs,hrec,h⟩|⟨h,rfl,rfl⟩)
      -- Case: `s ≠ []`, recursive call succeeds
      · dsimp only at hrec; erw [hr] at hrec
        have hs' : 0 < s.length := by rw [List.length_pos]; rintro rfl; simp at hs
        induction' s with s ss ihs
        · simp at hs'
        clear ihs -- see if we need this
        rw [Option.inl_eq_toSum_iff] at hs
        simp only [List.head?_cons, not_lt, Option.map_eq_some', Option.filter_eq_some_iff] at hs
        rcases hs with ⟨a, ⟨ha, ha'⟩, rfl⟩; rcases ha'
        rcases h with (⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
        -- Case: recursive call does not panic
        · simp only [ge_iff_le, List.length_tail, tsub_le_iff_right, List.append_assoc,
            List.singleton_append, Sum.inl.injEq, Prod.mk.injEq, Sum.isRight_inl,
            Nat.sub_add_cancel hr', Nat.sub_add_cancel hs'] at hrec
          simp only [add_mul, one_mul, ← Nat.le_sub_iff_add_le hle]
          split_ifs at hrec with hrsg hrs
          · rcases hrec with ⟨rfl,rfl,rfl⟩
            clear hrec  -- TODO seems to be a bug of that the obsolete `hrec` is still in context
            rcases hrs with ⟨hrs,hrs'⟩
            simp only [List.length_cons] at hrs
            simp only [ge_iff_le, List.length_cons, hrs, List.all_eq_true, decide_eq_true_eq,
              true_and, tsub_le_iff_right, Nat.sub_sub, Nat.add_comm c, List.tail_cons, Sum.inl.injEq, Prod.mk.injEq,
              List.append_cancel_left_eq, and_false, ite_prop_iff_or, not_forall, not_lt, exists_prop, or_false,
              Sum.isRight_inl, not_le]
            refine ⟨?_,?_,?_,?_⟩
            · rw [List.tail_cons] at hrs' hrsg
              rw [List.takeWhileN_cons_of_pos _ _ _ hr', ha]
              simp only [ite_true, List.length_cons, ge_iff_le]
              rw [← Nat.add_one]
              exact hrsg
            · intros x hx
              rw [← Nat.succ_pred_eq_of_pos hr', List.take_succ_cons] at hx
              aesop
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
            · conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr']
          · rcases hrec with ⟨rfl,rfl⟩; clear hrec
            rw [ite_prop_iff_or]; left
            rw [not_and_or] at hrs; rcases hrs with (hrs|hrs)
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · simp only [hrs]
                simp only [List.all_eq_true, decide_eq_true_eq, false_and, ge_iff_le,
                  List.tail_cons, Sum.inl.injEq, Prod.mk.injEq, and_false, and_true, ite_false]
                conv_rhs => rw [List.dropWhileN_cons_of_pos _ _ _ hr', ha]
            · constructor
              · refine le_trans (Nat.mul_le_mul_right _ ?_) hrsg
                simp_all [List.takeWhileN_cons_of_pos]
              · rw [ite_prop_iff_or]; right; constructor
                · rw [not_and_or]; right
                  contrapose! hrs
                  rw [List.take_pred_tail hr']
                  exact List.all_tail hrs
                · simp_all [List.dropWhileN_cons_of_pos]
        -- Case: recursive call panics
        · rw [List.length_pos] at hs'
          simp only [List.tail_cons, ge_iff_le, List.length_takeWhileN, tsub_le_iff_right, add_mul,
            one_mul, List.all_eq_true, decide_eq_true_eq, List.append_assoc, List.singleton_append,
            and_false, ite_self, Sum.isRight_inr, prop_if_false_true, not_le] at hrec
          simp only [List.length_takeWhileN, ge_iff_le, add_mul, one_mul, List.length_cons,
            List.all_eq_true, decide_eq_true_eq, and_false, ite_self, Sum.isRight_inr,
            prop_if_false_true, not_le, gt_iff_lt]
          rw [List.takeWhile_cons_of_pos]
          · simp only [List.length_cons, ge_iff_le, ← tsub_lt_iff_right hle]
            rw [← Nat.succ_pred_eq_of_pos hr', Nat.min_succ_succ, Nat.succ_mul]
            exact hrec
          · exact ha
      -- Case: recursive call fails due to `s = []` or `s` containing overflows
      · rw [Option.inr_eq_toSum_iff, Option.map_eq_none', Option.filter_eq_none_iff] at h
        rcases h with (h|⟨a,h,h'⟩)
        · rw [@Option.isNone_iff_eq_none, List.head?] at h
          have : s = [] := by aesop
          subst this
          simp_all
        · rcases s with ⟨_,⟨s,ss⟩⟩
          · simp only [List.head?_nil] at h
          · simp only [List.head?_cons, Option.some.injEq] at h; subst h
            generalize hrval : r.val = rval
            rcases rval with ⟨_,rval⟩
            · simp [hrval] at hr'
            · simp only [decide_eq_true_eq] at h'
              simp [h', hle]
  -- Case: Not enough gas for one run
  · aesop

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
  · right; simp only [Sum.isRight_inr, and_self]-/
