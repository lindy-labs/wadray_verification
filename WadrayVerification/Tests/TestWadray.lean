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
  have : ZMod.val (Wad.toZMod (5 : UInt128)) + ZMod.val (Wad.toZMod (3 : UInt128)) < U128_MOD
  · simp only [Wad.toZMod]
    erw [ZMod.val_nat_cast, ZMod.val_nat_cast]
    norm_num [U128_MOD]
  aesop

aegis_spec "wadray::tests::test_wadray::test_sub_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_sub_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_sub_eq»
  have : Wad.toRat (3 : UInt128) ≤ Wad.toRat (5 : UInt128)
  · simp [Wad.toRat]
    apply div_le_div_of_le (by norm_num [Wad.WAD_SCALE])
    norm_cast
  sierra_simp'
  aesop (add unsafe forward [not_le_of_lt])

aegis_spec "wadray::tests::test_wadray::test_mul_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_mul_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_mul_eq»
  have : (Wad.toZMod (5 : UInt128)).val * (Wad.toZMod (3 : UInt128)).val / Wad.WAD_SCALE < U128_MOD
  · simp only [Wad.toZMod]
    erw [ZMod.val_nat_cast, ZMod.val_nat_cast]
    norm_num [U128_MOD, Wad.WAD_SCALE]
  aesop

aegis_spec "wadray::tests::test_wadray::test_div_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_div_eq" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_eq»
  have : (Wad.toZMod (15 : UInt128)).val * Wad.WAD_SCALE / (Wad.toZMod (3 : UInt128)).val < U128_MOD
  · simp only [Wad.toZMod]
    erw [ZMod.val_nat_cast, ZMod.val_nat_cast]
    norm_num [U128_MOD, Wad.WAD_SCALE]
  have : Wad.toZMod (3 : UInt128) ≠ 0
  · simp only [Wad.toZMod]
    intro he
    have := congr_arg ZMod.val he
    erw [ZMod.val_nat_cast, ZMod.val_nat_cast] at this
    norm_num [U128_MOD] at this
  aesop

aegis_spec "wadray::tests::test_wadray::test_div_of_0" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_div_of_0" :=
  fun _ _ _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_div_of_0»
  sierra_simp'
  have : U128_MOD ≠ 0
  · norm_num [U128_MOD]
  have : (42 : UInt128) ≠ 0
  · intro he
    have := congr_arg ZMod.val he
    erw [ZMod.val_nat_cast, ZMod.val_nat_cast] at this
    norm_num [U128_MOD] at this
  have : @HDiv.hDiv Wad Wad Wad instHDiv (0 : UInt128) (42 : UInt128) = (0 : Wad)
  · simp [Wad.div_def, Wad.zero_toZMod]
  have : @HDiv.hDiv Ray Ray Ray instHDiv (0 : UInt128) (42 : UInt128) = (0 : Ray)
  · simp [Ray.div_def, Ray.zero_toZMod]
  aesop (add simp [Ray.toZMod, Ray.ofZMod, Wad.toZMod, Wad.ofZMod])


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
  have : Wad.WAD_SCALE ≠ 0
  · norm_num [Wad.WAD_SCALE]
  have : Ray.RAY_SCALE ≠ 0
  · norm_num [Ray.RAY_SCALE]
  have : ((1 : UInt128) : Rat) = 1
  · aesop
  aesop (add simp [Wad.toRat, Ray.toRat, Wad.toZMod, Ray.toZMod, ZMod.cast_one'])

aegis_spec "wadray::tests::test_wadray::test_bounded" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_bounded" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_bounded»
  have : (340282366920938463463374607431768211455 : UInt128) = -1
  · apply ZMod.val_injective
    erw [ZMod.val_nat_cast]
  aesop

aegis_spec "wadray::tests::test_wadray::test_conversions_from_primitive_types" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_conversions_from_primitive_types" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_conversions_from_primitive_types»
  have : ((1 : Sierra.UInt8) : UInt128) = (1 : UInt128)
  · aesop
  have : ((1 : Sierra.UInt16) : UInt128) = (1 : UInt128)
  · aesop
  have : ((1 : Sierra.UInt32) : UInt128) = (1 : UInt128)
  · aesop
  have : ((1 : Sierra.UInt64) : UInt128) = (1 : UInt128)
  · aesop
  aesop

aegis_spec "wadray::tests::test_wadray::test_u256_try_into_wadray" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_u256_try_into_wadray" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_u256_try_into_wadray»
  have : (5 : UInt128).val < U128_MOD
  · apply ZMod.val_lt
  aesop (add simp [UInt256.val])

aegis_spec "wadray::tests::test_wadray::test_wadray_into_u256" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray::test_wadray_into_u256" :=
  fun _ ρ => by
  unfold «spec_wadray::tests::test_wadray::test_wadray_into_u256»
  aesop
