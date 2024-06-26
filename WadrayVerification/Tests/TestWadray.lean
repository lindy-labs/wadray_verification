import CorelibVerification
import WadrayVerification.Aux
import WadrayVerification.Wadray

open Sierra

/-
aegis_info "wadray::tests::test_wadray::test_add"

aegis_spec "wadray::tests::test_wadray::test_add" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

set_option maxHeartbeats 800000
set_option trace.aesop true
aegis_prove "wadray::tests::test_wadray::test_add" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_add»
  sierra_simp'
  have h₁ : (1 : UInt128) + 1 = 2
  · rfl
  have h₂ : ¬ (U128_MOD = 0)
  · rw [← ne_eq, ← Nat.pos_iff_ne_zero]; apply Fact.out
  have h₃ : ¬ (U128_MOD ≤ 1 + 1)
  · norm_num[U128_MOD]
  have h₄ : (123456789101112 : UInt128) + 121110987654321 = 244567776755433
  · rfl
  have h₅ : ¬ (U128_MOD ≤ ZMod.val (123456789101112 : UInt128)
    + ZMod.val (121110987654321 : UInt128))
  · erw [ZMod.val_nat_cast, ZMod.val_nat_cast]
    norm_num [U128_MOD]
  intro h
  generalize hU : U128_MOD = U'
  aesop (add simp [Wad.toZMod, ZMod.val_one])
    (options := { maxRuleApplications := 300 })
  exact left h₁
  exact left_2 h₄
  exact left_3 h₁
  exact left_6 h₄

example
  (h₁ : 1 + 1 = 2)
  (h₂ : (123456789101112 : ZMod 340282366920938463463374607431768211456).val < 340282366920938463463374607431768211456)
  (h₃ : ¬ 1 + 1 = 2) : False := by
  generalize 340282366920938463463374607431768211456 = x at h₂
  contradiction -/

aegis_spec "wadray::tests::test_wadray::test_add_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_add_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_add_eq»
  have : ZMod.val (Wad.toZMod (5 : UInt128)) + ZMod.val (Wad.toZMod (3 : UInt128)) < U128_MOD := by
    simp only [Wad.toZMod]
    erw [ZMod.val_natCast, ZMod.val_natCast]
    norm_num [U128_MOD]
  aesop

aegis_spec "wadray::tests::test_wadray::test_sub_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_sub_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_sub_eq»
  have : Wad.toRat (3 : UInt128) ≤ Wad.toRat (5 : UInt128) := by
    simp [Wad.toRat]
    apply div_le_div_of_nonneg_right _ (by norm_num [Wad.WAD_SCALE])
    norm_cast
  sierra_simp'
  aesop (add unsafe forward [not_le_of_lt])

aegis_spec "wadray::tests::test_wadray::test_mul_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_mul_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_mul_eq»
  have : (Wad.toZMod (5 : UInt128)).val * (Wad.toZMod (3 : UInt128)).val / Wad.WAD_SCALE < U128_MOD := by
    simp only [Wad.toZMod]
    erw [ZMod.val_natCast, ZMod.val_natCast]
    norm_num [U128_MOD, Wad.WAD_SCALE]
  aesop

aegis_spec "wadray::tests::test_wadray::test_div_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_div_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_eq»
  have : (Wad.toZMod (15 : UInt128)).val * Wad.WAD_SCALE / (Wad.toZMod (3 : UInt128)).val < U128_MOD := by
    simp only [Wad.toZMod]
    erw [ZMod.val_natCast, ZMod.val_natCast]
    norm_num [U128_MOD, Wad.WAD_SCALE]
  have : Wad.toZMod (3 : UInt128) ≠ 0 := by
    simp only [Wad.toZMod]
    intro he
    have := congr_arg ZMod.val he
    erw [ZMod.val_natCast, ZMod.val_natCast] at this
    norm_num [U128_MOD] at this
  aesop

aegis_spec "wadray::tests::test_wadray::test_div_of_0" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_div_of_0" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_of_0»
  sierra_simp'
  have : U128_MOD ≠ 0 := by
    norm_num [U128_MOD]
  have : (42 : UInt128) ≠ 0 := by
    intro he
    have := congr_arg ZMod.val he
    erw [ZMod.val_natCast, ZMod.val_natCast] at this
    norm_num [U128_MOD] at this
  have : @HDiv.hDiv Wad Wad Wad instHDiv (0 : UInt128) (42 : UInt128) = (0 : Wad) := by
    simp [Wad.div_def, Wad.zero_toZMod]
  have : @HDiv.hDiv Ray Ray Ray instHDiv (0 : UInt128) (42 : UInt128) = (0 : Ray) := by
    simp [Ray.div_def, Ray.zero_toZMod]
  intro h_auto
  sorry  -- TODO fix this

aegis_spec "wadray::tests::test_wadray::test_div_wad_fail" :=
  fun _ _ _ ρ =>
  ρ.isRight

aegis_prove "wadray::tests::test_wadray::test_div_wad_fail" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_wad_fail»
  aesop

aegis_spec "wadray::tests::test_wadray::test_div_ray_fail" :=
  fun _ _ _ ρ =>
  ρ.isRight

aegis_prove "wadray::tests::test_wadray::test_div_ray_fail" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_ray_fail»
  aesop

/-aegis_spec "wadray::tests::test_wadray::test_conversions" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_conversions" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_conversions»
  sierra_simp'
  have : Wad.toRay (1000000000000000000 : UInt128) = (1000000000000000000000000000 : UInt128)
  · sorry
  aesop-/

aegis_spec "wadray::tests::test_wadray::test_zeroable" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_zeroable" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_zeroable»
  have : Wad.WAD_SCALE ≠ 0 := by norm_num [Wad.WAD_SCALE]
  have : Ray.RAY_SCALE ≠ 0 := by norm_num [Ray.RAY_SCALE]
  have : ((1 : UInt128).cast : Rat) = 1 := by aesop
  aesop (add simp [Wad.toRat, Ray.toRat, Wad.toZMod, Ray.toZMod, ZMod.cast_one'])

aegis_spec "wadray::tests::test_wadray::test_bounded" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_bounded" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_bounded»
  have : (340282366920938463463374607431768211455 : UInt128) = -1 := by
    apply ZMod.val_injective
    erw [ZMod.val_natCast]
  aesop

aegis_spec "wadray::tests::test_wadray::test_conversions_from_primitive_types" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_conversions_from_primitive_types" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_conversions_from_primitive_types»
  have : ((1 : Sierra.UInt8).cast : UInt128) = (1 : UInt128) := by aesop
  have : ((1 : Sierra.UInt16).cast : UInt128) = (1 : UInt128) := by aesop
  have : ((1 : Sierra.UInt32).cast : UInt128) = (1 : UInt128) := by aesop
  have : ((1 : Sierra.UInt64).cast : UInt128) = (1 : UInt128) := by aesop
  aesop

aegis_spec "wadray::tests::test_wadray::test_u256_try_into_wadray" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_u256_try_into_wadray" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_u256_try_into_wadray»
  have : (5 : UInt128).val < U128_MOD := by apply ZMod.val_lt
  aesop (add simp [UInt256.val])

aegis_spec "wadray::tests::test_wadray::test_wadray_into_u256" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_wadray_into_u256" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_wadray_into_u256»
  aesop

aegis_spec "wadray::tests::test_wadray::test_conversions_fail2" :=
  fun _ _ _ ρ =>
  ρ.isRight

aegis_prove "wadray::tests::test_wadray::test_conversions_fail2" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_conversions_fail2»
  aesop (add simp [Wad.toZMod, ZMod.val_add_of_lt])

aegis_spec "wadray::tests::test_wadray::test_comparisons2" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_comparisons2" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_comparisons2»
  have : (1000000000000000000 : UInt128).val + (1 : UInt128).val < U128_MOD := by
    erw [ZMod.val_natCast, ZMod.val_natCast]
    norm_num [U128_MOD]
  have : (1000000000000000000000000000 : UInt128).val + (1 : UInt128).val < U128_MOD := by
    erw [ZMod.val_natCast, ZMod.val_natCast]
    norm_num [U128_MOD]
  rename_i x x_1 x_2 this_1
  intro h_auto
  aesop

aegis_spec "wadray::tests::test_wadray::test_comparisons1" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

set_option maxHeartbeats 800000
aegis_prove "wadray::tests::test_wadray::test_comparisons1" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_comparisons1»
  /-sierra_simp'
  have uone : (((1000000000000000000000000000 : ℕ) : ℤ) : UInt128) = 1
  · sorry
  have uone' : (((1000000000000000000 : ℕ) : ℤ) : UInt128) = 1
  · sorry
  have wone : Wad.toRat (1 : UInt128) = 1
  · sorry
  have rone : Ray.toRat (1 : UInt128) = 1
  · sorry
  have : Wad.toRat ((1 : UInt128) + (1 : UInt128)) = 2
  · sorry
  have : Ray.toRat ((1 : UInt128) + (1 : UInt128)) = 2
  · sorry
  have : (1 : UInt128).val + (1 : UInt128).val < U128_MOD
  · sorry
  have : (1 : ℚ) < 2 := by norm_num-/
  sorry

aegis_spec "wadray::tests::test_wadray::test_conversions" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_conversions" :=
  fun _ _ _ ρ => by
  /-unfold «spec_wadray::tests::test_wadray::test_conversions»
  have : Wad.toRay (1000000000000000000 : UInt128) = (1000000000000000000000000000 : UInt128)
  · sorry
  have : Wad.toRay (340282366920938463463374607431 : UInt128) = (340282366920938463463374607431 : UInt128) * (1000000000 : UInt128)
  · sorry
  have : Ray.toWad (1000000000000000000000000000 : UInt128) = (1000000000000000000 : UInt128)
  · sorry
  have : (Wad.toZMod (340282366920938463463374607431 : UInt128)).val = Wad.MAX_CONVERTIBLE_WAD
  · sorry
  have : ZMod.val (Wad.toZMod (1000000000000000000 : UInt128)) ≤ Wad.MAX_CONVERTIBLE_WAD
  · sorry
  have : ZMod.val (340282366920938463463374607431 : UInt128) + ZMod.val (1 : UInt128) < U128_MOD
  · sorry
  have : ZMod.val (340282366920938463463374607431 : UInt128) * ZMod.val (1000000000 : UInt128) < U128_MOD
  · sorry
  have : Wad.MAX_CONVERTIBLE_WAD < ZMod.val (Wad.toZMod ((340282366920938463463374607431 : UInt128) + (1 : UInt128)))
  · sorry
  aesop (add safe forward [not_le_of_lt])-/
  sorry

aegis_spec "wadray::tests::test_wadray::test_add" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_add" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray::test_sub" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_sub" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray::test_mul" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_mul" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray::test_div" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_div" :=
  fun _ _ _ ρ => by
  sorry
