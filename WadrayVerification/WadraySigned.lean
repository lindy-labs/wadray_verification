import WadrayVerification.Aux
import WadrayVerification.Wadray

aegis_spec "wadray::wadray_signed::SignedWadZeroable::zero" :=
  fun _ (ρ : SignedWad) =>
  ρ = 0

aegis_prove "wadray::wadray_signed::SignedWadZeroable::zero" :=
  fun _ (ρ : SignedWad) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::SignedRayZeroable::zero" :=
  fun _ (ρ : SignedRay) =>
  ρ = 0

aegis_prove "wadray::wadray_signed::SignedRayZeroable::zero" :=
  fun _ (ρ : SignedRay) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::SignedWadOneable::one" :=
  fun _ (ρ : SignedWad) =>
  ρ = 1

aegis_prove "wadray::wadray_signed::SignedWadOneable::one" :=
  fun _ (ρ : SignedWad) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::SignedRayOneable::one" :=
  fun _ (ρ : SignedRay) =>
  ρ = 1

aegis_prove "wadray::wadray_signed::SignedRayOneable::one" :=
  fun _ (ρ : SignedRay) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::SignedWadPartialEq::eq" :=
  fun _ (a b : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat = b.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialEq::eq" :=
  fun _ (a b : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialEq::eq»
  aesop (add safe forward [SignedWad.val_eq_of_toRat_eq, SignedWad.val_eq_zero_of_toRat_neg,
    SignedWad.val_eq_zero_of_toRat_neg'])

aegis_spec "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat = b.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialEq::eq»
  aesop (add safe forward [SignedRay.val_eq_of_toRat_eq, SignedRay.val_eq_zero_of_toRat_neg,
    SignedRay.val_eq_zero_of_toRat_neg'])

aegis_spec "wadray::wadray_signed::SignedWadPartialEq::ne" :=
  fun _ (a b : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ b.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialEq::ne" :=
  fun _ (a b : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialEq::ne»
  rintro rfl
  simp

aegis_spec "wadray::wadray_signed::SignedRayPartialEq::ne" :=
  fun _ (a b : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ b.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialEq::ne" :=
  fun _ (a b : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialEq::ne»
  rintro rfl
  simp

aegis_spec "wadray::wadray_signed::SignedWadSigned::is_positive" :=
  fun _ _ (a : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat > 0)

aegis_prove "wadray::wadray_signed::SignedWadSigned::is_positive" :=
  fun _ _ (a : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadSigned::is_positive»
  rintro ⟨w,s,rfl,(⟨h,rfl⟩|⟨h,rfl⟩)⟩
  · aesop (add simp [SignedWad.toRat, Wad.toRat])
  · rcases s with (s|s)
    · simp_all only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Int.cast_zero, ZMod.val_zero,
        SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true, SignedWad.toRat, Wad.toRat,
        Wad.toZMod, ZMod.nat_cast_val, ite_false, gt_iff_lt, Bool.toSierraBool_decide_inr']
      rw [lt_div_iff (by norm_num [Wad.WAD_SCALE]), zero_mul]
      apply Ne.lt_of_le _ (ZMod.cast_rat_nonneg _)
      intro he
      rw [eq_comm, ZMod.cast_rat_eq_zero_iff] at he; subst he
      simp at h
    · simp [SignedWad.toRat, Wad.toRat]
      rw [le_div_iff (by norm_num [Wad.WAD_SCALE]), zero_mul]
      apply ZMod.cast_rat_nonneg

aegis_spec "wadray::wadray_signed::SignedRaySigned::is_positive" :=
  fun _ _ (a : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat > 0)

aegis_prove "wadray::wadray_signed::SignedRaySigned::is_positive" :=
  fun _ _ (a : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRaySigned::is_positive»
  rintro ⟨w,s,rfl,(⟨h,rfl⟩|⟨h,rfl⟩)⟩
  · aesop (add simp [SignedRay.toRat, Ray.toRat])
  · rcases s with (s|s)
    · simp_all only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Int.cast_zero, ZMod.val_zero,
        SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true, SignedRay.toRat, Ray.toRat,
        Ray.toZMod, ZMod.nat_cast_val, ite_false, gt_iff_lt, Bool.toSierraBool_decide_inr']
      rw [lt_div_iff (by norm_num [Ray.RAY_SCALE]), zero_mul]
      apply Ne.lt_of_le _ (ZMod.cast_rat_nonneg _)
      intro he
      rw [eq_comm, ZMod.cast_rat_eq_zero_iff] at he; subst he
      simp at h
    · simp [SignedRay.toRat, Ray.toRat]
      rw [le_div_iff (by norm_num [Ray.RAY_SCALE]), zero_mul]
      apply ZMod.cast_rat_nonneg

aegis_spec "wadray::wadray_signed::SignedWadSigned::is_negative" :=
  fun _ _ (a : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < 0)

aegis_prove "wadray::wadray_signed::SignedWadSigned::is_negative" :=
  fun _ _ (a : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadSigned::is_negative»
  rintro ⟨w,s,rfl,(⟨h,rfl⟩|⟨h,rfl⟩)⟩
  · aesop (add simp [SignedWad.toRat, Wad.toRat])
  · have : 0 < (Wad.WAD_SCALE : ℚ) := by norm_num [Wad.WAD_SCALE]
    rcases s with (s|s)
    <;> aesop (add simp [SignedWad.toRat, Wad.toRat, lt_div_iff, le_div_iff,
      Wad.toZMod, ZMod.cast_rat_nonneg], safe apply [Ne.lt_of_le])

aegis_spec "wadray::wadray_signed::SignedRaySigned::is_negative" :=
  fun _ _ (a : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < 0)

aegis_prove "wadray::wadray_signed::SignedRaySigned::is_negative" :=
  fun _ _ (a : SignedRay) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRaySigned::is_negative»
  rintro ⟨w,s,rfl,(⟨h,rfl⟩|⟨h,rfl⟩)⟩
  · aesop (add simp [SignedRay.toRat, Ray.toRat])
  · have : 0 < (Ray.RAY_SCALE : ℚ) := by norm_num [Ray.RAY_SCALE]
    rcases s with (s|s)
    <;> aesop (add simp [SignedRay.toRat, Ray.toRat, lt_div_iff, le_div_iff,
      Ray.toZMod, ZMod.cast_rat_nonneg], safe apply [Ne.lt_of_le])

aegis_spec "wadray::wadray_signed::SignedWadZeroable::is_zero" :=
  fun _ (a : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 0)

aegis_prove "wadray::wadray_signed::SignedWadZeroable::is_zero" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadZeroable::is_zero»
  have : ¬ (Wad.WAD_SCALE = 0)
  · norm_num [Wad.WAD_SCALE]
  aesop (add simp [SignedWad.toRat, Wad.toRat])

aegis_spec "wadray::wadray_signed::SignedRayZeroable::is_zero" :=
  fun _ (a : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 0)

aegis_prove "wadray::wadray_signed::SignedRayZeroable::is_zero" :=
  fun _ (a : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayZeroable::is_zero»
  have : ¬ (Ray.RAY_SCALE = 0)
  · norm_num [Ray.RAY_SCALE]
  aesop (add simp [SignedRay.toRat, Ray.toRat])

aegis_spec "wadray::wadray_signed::SignedWadZeroable::is_non_zero" :=
  fun _ (a : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 0)

aegis_prove "wadray::wadray_signed::SignedWadZeroable::is_non_zero" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadZeroable::is_non_zero»
  aesop (add simp [SignedWad.toRat, Wad.toRat, Wad.toZMod])

aegis_spec "wadray::wadray_signed::SignedRayZeroable::is_non_zero" :=
  fun _ (a : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 0)

aegis_prove "wadray::wadray_signed::SignedRayZeroable::is_non_zero" :=
  fun _ (a : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayZeroable::is_non_zero»
  aesop (add simp [SignedRay.toRat, Ray.toRat, Ray.toZMod])

aegis_spec "wadray::wadray_signed::SignedWadOneable::is_one" :=
  fun _ (a : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 1)

aegis_prove "wadray::wadray_signed::SignedWadOneable::is_one" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadOneable::is_one»
  rintro ⟨w,s,h⟩
  have : 1000000000000000000 = ((1000000000000000000 : Sierra.UInt128) : ℚ)
  · rw [ZMod.cast_eq_val]; aesop
  have : (1000000000000000000 : ℚ) ≠ 0
  · norm_num
  have : ¬ (-(w : ℚ) = 1000000000000000000)
  · apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  aesop (add simp [SignedWad.toRat, Wad.toRat, Wad.toZMod, Wad.WAD_SCALE,
    div_eq_iff, neg_div'], safe forward [ZMod.cast_rat_injective])

aegis_spec "wadray::wadray_signed::SignedRayOneable::is_one" :=
  fun _ (a : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 1)

aegis_prove "wadray::wadray_signed::SignedRayOneable::is_one" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayOneable::is_one»
  rintro ⟨w,s,h⟩
  have : 1000000000000000000000000000 = ((1000000000000000000000000000 : Sierra.UInt128) : ℚ)
  · rw [ZMod.cast_eq_val]; aesop
  have : (1000000000000000000000000000 : ℚ) ≠ 0
  · norm_num
  have : ¬ (-(w : ℚ) = 1000000000000000000000000000)
  · apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  aesop (add simp [SignedRay.toRat, Ray.toRat, Ray.toZMod, Ray.RAY_SCALE,
    div_eq_iff, neg_div'], safe forward [ZMod.cast_rat_injective])

aegis_spec "wadray::wadray_signed::SignedWadOneable::is_non_one" :=
  fun _ (a : SignedWad) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 1)

aegis_prove "wadray::wadray_signed::SignedWadOneable::is_non_one" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadOneable::is_non_one»
  rintro ⟨w,s,rfl,h⟩
  have : ¬ (-(w : ℚ) = 1000000000000000000)
  · apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  have : ¬w = 1000000000000000000 → ¬(w : ℚ) = 1000000000000000000
  · have hn : 1000000000000000000 = ((1000000000000000000 : Sierra.UInt128) : ℚ)
    · rw [ZMod.cast_eq_val]; aesop
    intros he hee; rw [hn] at hee; have := ZMod.cast_rat_injective hee; contradiction
  aesop (add simp [SignedWad.toRat, Wad.toRat, Wad.toZMod, Wad.WAD_SCALE,
    div_eq_iff, neg_div'], safe forward [ZMod.cast_rat_injective])

aegis_spec "wadray::wadray_signed::SignedRayOneable::is_non_one" :=
  fun _ (a : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat ≠ 1)

aegis_prove "wadray::wadray_signed::SignedRayOneable::is_non_one" :=
  fun _ (a : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayOneable::is_non_one»
  rintro ⟨w,s,rfl,h⟩
  have : ¬ (-(w : ℚ) = 1000000000000000000000000000)
  · apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  have : ¬w = 1000000000000000000000000000 → ¬(w : ℚ) = 1000000000000000000000000000
  · have hn : 1000000000000000000000000000 = ((1000000000000000000000000000 : Sierra.UInt128) : ℚ)
    · rw [ZMod.cast_eq_val]; aesop
    intros he hee; rw [hn] at hee; have := ZMod.cast_rat_injective hee; contradiction
  aesop (add simp [SignedRay.toRat, Ray.toRat, Ray.toZMod, Ray.RAY_SCALE,
    div_eq_iff, neg_div'], safe forward [ZMod.cast_rat_injective])
