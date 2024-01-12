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
  ρ = Bool.toSierraBool (a == b)

aegis_prove "wadray::wadray_signed::SignedWadPartialEq::eq" :=
  fun _ (a b : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialEq::eq»
  aesop (add simp [SignedWad.bEq_def])

aegis_spec "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a == b)

aegis_prove "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialEq::eq»
  aesop (add simp [SignedRay.bEq_def])

aegis_spec "wadray::wadray_signed::SignedWadPartialEq::ne" :=
  fun _ (a b : SignedWad) ρ =>
  ρ = Bool.toSierraBool (!(a == b))

aegis_prove "wadray::wadray_signed::SignedWadPartialEq::ne" :=
  fun _ (a b : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialEq::ne»
  rintro rfl
  simp

aegis_spec "wadray::wadray_signed::SignedRayPartialEq::ne" :=
  fun _ (a b : SignedRay) ρ =>
  ρ = Bool.toSierraBool (!(a == b))

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
