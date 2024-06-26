import WadrayVerification.Aux
import WadrayVerification.Wadray

open Sierra

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
  rename_i x
  intro h_auto
  aesop (add safe forward [SignedWad.val_eq_of_toRat_eq, SignedWad.val_eq_zero_of_toRat_neg,
    SignedWad.val_eq_zero_of_toRat_neg'])

aegis_spec "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat = b.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialEq::eq" :=
  fun _ (a b : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialEq::eq»
  rename_i x
  intro h_auto
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
        Wad.toZMod, ZMod.natCast_val, ite_false, gt_iff_lt, Bool.toSierraBool_decide_inr']
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
        Ray.toZMod, ZMod.natCast_val, ite_false, gt_iff_lt, Bool.toSierraBool_decide_inr']
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
  have : ¬ (Wad.WAD_SCALE = 0) := by
    norm_num [Wad.WAD_SCALE]
  aesop (add simp [SignedWad.toRat, Wad.toRat])

aegis_spec "wadray::wadray_signed::SignedRayZeroable::is_zero" :=
  fun _ (a : SignedRay) ρ =>
  ρ = Bool.toSierraBool (a.toRat = 0)

aegis_prove "wadray::wadray_signed::SignedRayZeroable::is_zero" :=
  fun _ (a : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayZeroable::is_zero»
  have : ¬ (Ray.RAY_SCALE = 0) := by
    norm_num [Ray.RAY_SCALE]
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
  have : 1000000000000000000 = ((1000000000000000000 : Sierra.UInt128).cast : ℚ) := by
    rw [ZMod.cast_eq_val]; aesop
  have : (1000000000000000000 : ℚ) ≠ 0 := by
    norm_num
  have : ¬ (-(w.cast : ℚ) = 1000000000000000000) := by
    apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
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
  have : 1000000000000000000000000000 = ((1000000000000000000000000000 : Sierra.UInt128).cast : ℚ) := by
    rw [ZMod.cast_eq_val]; aesop
  have : (1000000000000000000000000000 : ℚ) ≠ 0 := by
    norm_num
  have : ¬ (-(w.cast : ℚ) = 1000000000000000000000000000) := by
    apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
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
  have : ¬ (-(w.cast : ℚ) = 1000000000000000000) := by
    apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  have : ¬w = 1000000000000000000 → ¬(w.cast : ℚ) = 1000000000000000000 := by
    have hn : 1000000000000000000 = ((1000000000000000000 : Sierra.UInt128).cast : ℚ) := by
      rw [ZMod.cast_eq_val]; aesop
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
  have : ¬ (-(w.cast : ℚ) = 1000000000000000000000000000) := by
    apply ne_of_lt (lt_of_le_of_lt (b := 0) _ (by norm_num))
    simp only [Left.neg_nonpos_iff, ZMod.cast_rat_nonneg]
  have : ¬w = 1000000000000000000000000000 → ¬(w.cast : ℚ) = 1000000000000000000000000000 := by
    have hn : 1000000000000000000000000000 = ((1000000000000000000000000000 : Sierra.UInt128).cast : ℚ) := by
      rw [ZMod.cast_eq_val]; aesop
    intros he hee; rw [hn] at hee; have := ZMod.cast_rat_injective hee; contradiction
  aesop (add simp [SignedRay.toRat, Ray.toRat, Ray.toZMod, Ray.RAY_SCALE,
    div_eq_iff, neg_div'], safe forward [ZMod.cast_rat_injective])

aegis_spec "wadray::wadray_signed::BoundedSignedWad::max" :=
  fun _ ρ =>
  ρ = ((U128_MOD - 1 : UInt128), .inl ())

aegis_prove "wadray::wadray_signed::BoundedSignedWad::max" :=
  fun _ ρ => by
  rintro rfl
  rfl
aegis_spec "wadray::wadray_signed::BoundedSignedRay::max" :=
  fun _ ρ =>
  ρ = ((U128_MOD - 1 : UInt128), .inl ())

aegis_prove "wadray::wadray_signed::BoundedSignedRay::max" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::BoundedSignedWad::min" :=
  fun _ ρ =>
  ρ = ((U128_MOD - 1 : UInt128), .inr ())

aegis_prove "wadray::wadray_signed::BoundedSignedWad::min" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::BoundedSignedRay::min" :=
  fun _ ρ =>
  ρ = ((U128_MOD - 1 : UInt128), .inr ())

aegis_prove "wadray::wadray_signed::BoundedSignedRay::min" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::SignedWadPartialOrd::gt" :=
  fun _ _ (a b : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat < a.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialOrd::gt" :=
  fun _ _ (a b : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialOrd::gt»
  have : 0 < (Wad.WAD_SCALE : ℚ) := by
    norm_num [Wad.WAD_SCALE]
  rintro ⟨w₁,s₁,w₂,s₂,u₁,u₂,u₃,u₄,u₅,u₆,rfl,rfl,(h|h)⟩
    <;> (cases u₁; cases u₂; cases u₃; cases u₄; cases u₅; cases u₆)
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨rfl,(⟨hne,h⟩|⟨rfl,rfl,rfl⟩)⟩
      · rcases h with (⟨hle,rfl⟩|⟨hlt,rfl⟩)
        · simp [SignedWad.toRat_le_toRat_of_val_le_val_inl hle]
        · simp only [SierraBool_toBool_inr, SierraBool_toBool_inl, Bool.xor_false,
            Bool.toSierraBool_true, Bool.toSierraBool_decide_inr']
          apply lt_of_le_of_ne
          · apply SignedWad.toRat_le_toRat_of_val_le_val_inl
            simp [Wad.toZMod, le_of_lt hlt]
          · intro he
            exact hne (SignedWad.val_eq_of_toRat_eq _ _ he).symm
      · simp only [lt_self_iff_false, decide_False, Bool.toSierraBool_false]
    · rcases h with ⟨rfl,(⟨hne,rfl,rfl⟩|h)⟩
      · simp only [SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true,
          Bool.toSierraBool_decide_inr']
        apply lt_of_le_of_ne
        · simp [SignedWad.toRat_inr_le_toRat_inl]
        · intro he
          exact hne (SignedWad.val_eq_of_toRat_eq _ _ he).symm
      · rcases h with ⟨rfl,(⟨h,rfl,rfl⟩|⟨h,rfl,rfl⟩)⟩
        · simp only [Nat.cast_pos, Bool.toSierraBool_decide_inl', SierraBool_toBool_inl,
            Bool.not_false, Bool.toSierraBool_true, Bool.toSierraBool_decide_inr'] at *
          apply lt_of_lt_of_le (b := 0)
          · apply lt_of_le_of_ne
            · simp [SignedWad.toRat, Wad.toRat_nonneg]
            · simpa [SignedWad.toRat]
          · simp [SignedWad.toRat, Wad.toRat_nonneg]
        · simp only [Nat.cast_pos, SignedWad.toRat, SierraBool_toBool_inl, ite_false,
            Bool.toSierraBool_decide_inr', SierraBool_toBool_inr, ite_true, neg_lt_self_iff,
            Bool.toSierraBool_decide_inl', not_lt] at *
          apply le_of_eq h
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨h',(h|⟨rfl,rfl,rfl⟩)⟩ <;> rcases s₂ with (_|s₂); · simp at h'
      · simp at h'
        rcases h with ⟨hne,(⟨hle,rfl⟩|⟨h,rfl⟩)⟩
        · simp at *
          · cases s₂
            apply lt_of_le_of_ne
            · apply SignedWad.toRat_le_toRat_of_val_ge_val_inr hle
            · intro he
              exact hne (SignedWad.val_eq_of_toRat_eq _ _ he).symm
        · simp at *
          apply SignedWad.toRat_le_toRat_of_val_ge_val_inr (le_of_lt h)
      · simp at *
      · simp at *
    · rcases h with ⟨h',h⟩
      rcases s₂ with (s₂|s₂) <;> cases s₂
      · rcases h with (⟨_,rfl,rfl⟩|⟨rfl,(⟨_,rfl,rfl⟩|⟨_,rfl,rfl⟩)⟩)
          <;> simp [SignedWad.toRat_inr_le_toRat_inl]
      · simp at h'

aegis_spec "wadray::wadray_signed::SignedWadPartialOrd::lt" :=
  fun _ _ (a b : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < b.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialOrd::lt" :=
  fun _ _ (a b : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialOrd::lt»
  have : 0 < (Wad.WAD_SCALE : ℚ) := by
    norm_num [Wad.WAD_SCALE]
  rintro ⟨w₁,s₁,w₂,s₂,u₁,u₂,u₃,u₄,u₅,u₆,rfl,rfl,(h|h)⟩
    <;> (cases u₁; cases u₂; cases u₃; cases u₄; cases u₅; cases u₆)
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨rfl,(⟨hne,h⟩|⟨rfl,rfl,rfl⟩)⟩
      · rcases h with (⟨hle,rfl⟩|⟨hlt,rfl⟩)
        · simp [SignedWad.toRat_le_toRat_of_val_le_val_inl hle]
        · simp only [SierraBool_toBool_inr, SierraBool_toBool_inl, Bool.xor_false,
            Bool.toSierraBool_true, Bool.toSierraBool_decide_inr']
          apply lt_of_le_of_ne
          · apply SignedWad.toRat_le_toRat_of_val_le_val_inl
            simp [Wad.toZMod, le_of_lt hlt]
          · intro he
            exact hne (SignedWad.val_eq_of_toRat_eq _ _ he)
      · simp only [lt_self_iff_false, decide_False, Bool.toSierraBool_false]
    · rcases h with ⟨rfl,(⟨_,rfl,rfl⟩|⟨rfl,(⟨_,rfl,rfl⟩|⟨_,rfl,rfl⟩)⟩)⟩
        <;> simp [SignedWad.toRat_inr_le_toRat_inl]
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨h',(h|⟨rfl,rfl,rfl⟩)⟩ <;> rcases s₂ with (_|s₂); · simp at h'
      · simp at h'
        rcases h with ⟨hne,(⟨hle,rfl⟩|⟨h,rfl⟩)⟩
        · simp at *
          · cases s₂
            apply lt_of_le_of_ne
            · apply SignedWad.toRat_le_toRat_of_val_ge_val_inr hle
            · intro he
              exact hne (SignedWad.val_eq_of_toRat_eq _ _ he)
        · simp at *
          apply SignedWad.toRat_le_toRat_of_val_ge_val_inr (le_of_lt h)
      · simp at *
      · simp at *
    · rcases h with ⟨h',h⟩
      rcases s₂ with (s₂|s₂) <;> cases s₂
      · rcases h with (⟨hne,rfl,rfl⟩|⟨rfl,h⟩)
        · simp
          apply lt_of_le_of_ne
          · apply SignedWad.toRat_inr_le_toRat_inl
          · intro he
            exact hne (SignedWad.val_eq_of_toRat_eq _ _ he)
        · rcases h with (⟨h,rfl,rfl⟩|⟨h,rfl,rfl⟩)
          · simp at *
            apply lt_of_lt_of_le (b := 0)
            · apply lt_of_le_of_ne
              · simp [SignedWad.toRat, Wad.toRat_nonneg]
              · exact h
            · simp [SignedWad.toRat, Wad.toRat_nonneg]
          · simp only [Nat.cast_pos, SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true,
              SignedWad.toRat, SierraBool_toBool_inr, ite_true, neg_eq_zero,
              Bool.toSierraBool_decide_inr', ite_false, neg_lt_self_iff,
              Bool.toSierraBool_decide_inl', not_lt] at *
            simp [h]
      · simp at h'

aegis_spec "wadray::wadray_signed::SignedWadPartialOrd::ge" :=
  fun _ _ (a b : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat ≤ a.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialOrd::ge" :=
  fun _ _ (a b : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialOrd::ge»
  rintro rfl
  simp only [← not_lt]
  rw [decide_not]
  simp only [Bool.coe_toSierraBool, Bool.toSierraBool_not]

aegis_spec "wadray::wadray_signed::SignedWadPartialOrd::le" :=
  fun _ _ (a b : SignedWad) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat ≤ b.toRat)

aegis_prove "wadray::wadray_signed::SignedWadPartialOrd::le" :=
  fun _ _ (a b : SignedWad) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadPartialOrd::le»
  rintro rfl
  simp only [← not_lt]
  rw [decide_not]
  simp only [Bool.coe_toSierraBool, Bool.toSierraBool_not]

aegis_spec "wadray::wadray_signed::SignedRayPartialOrd::gt" :=
  fun _ _ (a b : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat < a.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialOrd::gt" :=
  fun _ _ (a b : SignedRay) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialOrd::gt»
  have : 0 < (Ray.RAY_SCALE : ℚ) := by
    norm_num [Ray.RAY_SCALE]
  rintro ⟨w₁,s₁,w₂,s₂,u₁,u₂,u₃,u₄,u₅,u₆,rfl,rfl,(h|h)⟩
    <;> (cases u₁; cases u₂; cases u₃; cases u₄; cases u₅; cases u₆)
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨rfl,(⟨hne,h⟩|⟨rfl,rfl,rfl⟩)⟩
      · rcases h with (⟨hle,rfl⟩|⟨hlt,rfl⟩)
        · simp [SignedRay.toRat_le_toRat_of_val_le_val_inl hle]
        · simp only [SierraBool_toBool_inr, SierraBool_toBool_inl, Bool.xor_false,
            Bool.toSierraBool_true, Bool.toSierraBool_decide_inr']
          apply lt_of_le_of_ne
          · apply SignedRay.toRat_le_toRat_of_val_le_val_inl
            simp [Ray.toZMod, le_of_lt hlt]
          · intro he
            exact hne (SignedRay.val_eq_of_toRat_eq _ _ he).symm
      · simp only [lt_self_iff_false, decide_False, Bool.toSierraBool_false]
    · rcases h with ⟨rfl,(⟨hne,rfl,rfl⟩|h)⟩
      · simp only [SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true,
          Bool.toSierraBool_decide_inr']
        apply lt_of_le_of_ne
        · simp [SignedRay.toRat_inr_le_toRat_inl]
        · intro he
          exact hne (SignedRay.val_eq_of_toRat_eq _ _ he).symm
      · rcases h with ⟨rfl,(⟨h,rfl,rfl⟩|⟨h,rfl,rfl⟩)⟩
        · simp only [Nat.cast_pos, Bool.toSierraBool_decide_inl', SierraBool_toBool_inl,
            Bool.not_false, Bool.toSierraBool_true, Bool.toSierraBool_decide_inr'] at *
          apply lt_of_lt_of_le (b := 0)
          · apply lt_of_le_of_ne
            · simp [SignedRay.toRat, Ray.toRat_nonneg]
            · simpa [SignedRay.toRat]
          · simp [SignedRay.toRat, Ray.toRat_nonneg]
        · simp only [Nat.cast_pos, SignedRay.toRat, SierraBool_toBool_inl, ite_false,
            Bool.toSierraBool_decide_inr', SierraBool_toBool_inr, ite_true, neg_lt_self_iff,
            Bool.toSierraBool_decide_inl', not_lt] at *
          apply le_of_eq h
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨h',(h|⟨rfl,rfl,rfl⟩)⟩ <;> rcases s₂ with (_|s₂); · simp at h'
      · simp at h'
        rcases h with ⟨hne,(⟨hle,rfl⟩|⟨h,rfl⟩)⟩
        · simp at *
          · cases s₂
            apply lt_of_le_of_ne
            · apply SignedRay.toRat_le_toRat_of_val_ge_val_inr hle
            · intro he
              exact hne (SignedRay.val_eq_of_toRat_eq _ _ he).symm
        · simp at *
          apply SignedRay.toRat_le_toRat_of_val_ge_val_inr (le_of_lt h)
      · simp at *
      · simp at *
    · rcases h with ⟨h',h⟩
      rcases s₂ with (s₂|s₂) <;> cases s₂
      · rcases h with (⟨_,rfl,rfl⟩|⟨rfl,(⟨_,rfl,rfl⟩|⟨_,rfl,rfl⟩)⟩)
          <;> simp [SignedRay.toRat_inr_le_toRat_inl]
      · simp at h'

aegis_spec "wadray::wadray_signed::SignedRayPartialOrd::lt" :=
  fun _ _ (a b : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat < b.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialOrd::lt" :=
  fun _ _ (a b : SignedRay) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialOrd::lt»
  have : 0 < (Ray.RAY_SCALE : ℚ) := by
    norm_num [Ray.RAY_SCALE]
  rintro ⟨w₁,s₁,w₂,s₂,u₁,u₂,u₃,u₄,u₅,u₆,rfl,rfl,(h|h)⟩
    <;> (cases u₁; cases u₂; cases u₃; cases u₄; cases u₅; cases u₆)
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨rfl,(⟨hne,h⟩|⟨rfl,rfl,rfl⟩)⟩
      · rcases h with (⟨hle,rfl⟩|⟨hlt,rfl⟩)
        · simp [SignedRay.toRat_le_toRat_of_val_le_val_inl hle]
        · simp only [SierraBool_toBool_inr, SierraBool_toBool_inl, Bool.xor_false,
            Bool.toSierraBool_true, Bool.toSierraBool_decide_inr']
          apply lt_of_le_of_ne
          · apply SignedRay.toRat_le_toRat_of_val_le_val_inl
            simp [Ray.toZMod, le_of_lt hlt]
          · intro he
            exact hne (SignedRay.val_eq_of_toRat_eq _ _ he)
      · simp only [lt_self_iff_false, decide_False, Bool.toSierraBool_false]
    · rcases h with ⟨rfl,(⟨_,rfl,rfl⟩|⟨rfl,(⟨_,rfl,rfl⟩|⟨_,rfl,rfl⟩)⟩)⟩
        <;> simp [SignedRay.toRat_inr_le_toRat_inl]
  · rcases h with ⟨rfl,(h|h)⟩
    · rcases h with ⟨h',(h|⟨rfl,rfl,rfl⟩)⟩ <;> rcases s₂ with (_|s₂); · simp at h'
      · simp at h'
        rcases h with ⟨hne,(⟨hle,rfl⟩|⟨h,rfl⟩)⟩
        · simp at *
          · cases s₂
            apply lt_of_le_of_ne
            · apply SignedRay.toRat_le_toRat_of_val_ge_val_inr hle
            · intro he
              exact hne (SignedRay.val_eq_of_toRat_eq _ _ he)
        · simp at *
          apply SignedRay.toRat_le_toRat_of_val_ge_val_inr (le_of_lt h)
      · simp at *
      · simp at *
    · rcases h with ⟨h',h⟩
      rcases s₂ with (s₂|s₂) <;> cases s₂
      · rcases h with (⟨hne,rfl,rfl⟩|⟨rfl,h⟩)
        · simp
          apply lt_of_le_of_ne
          · apply SignedRay.toRat_inr_le_toRat_inl
          · intro he
            exact hne (SignedRay.val_eq_of_toRat_eq _ _ he)
        · rcases h with (⟨h,rfl,rfl⟩|⟨h,rfl,rfl⟩)
          · simp at *
            apply lt_of_lt_of_le (b := 0)
            · apply lt_of_le_of_ne
              · simp [SignedRay.toRat, Ray.toRat_nonneg]
              · exact h
            · simp [SignedRay.toRat, Ray.toRat_nonneg]
          · simp only [Nat.cast_pos, SierraBool_toBool_inl, Bool.not_false, Bool.toSierraBool_true,
              SignedRay.toRat, SierraBool_toBool_inr, ite_true, neg_eq_zero,
              Bool.toSierraBool_decide_inr', ite_false, neg_lt_self_iff,
              Bool.toSierraBool_decide_inl', not_lt] at *
            simp [h]
      · simp at h'

aegis_spec "wadray::wadray_signed::SignedRayPartialOrd::ge" :=
  fun _ _ (a b : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (b.toRat ≤ a.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialOrd::ge" :=
  fun _ _ (a b : SignedRay) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialOrd::ge»
  rintro rfl
  simp only [← not_lt]
  rw [decide_not]
  simp only [Bool.coe_toSierraBool, Bool.toSierraBool_not]

aegis_spec "wadray::wadray_signed::SignedRayPartialOrd::le" :=
  fun _ _ (a b : SignedRay) _ ρ =>
  ρ = Bool.toSierraBool (a.toRat ≤ b.toRat)

aegis_prove "wadray::wadray_signed::SignedRayPartialOrd::le" :=
  fun _ _ (a b : SignedRay) _ ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayPartialOrd::le»
  rintro rfl
  simp only [← not_lt]
  rw [decide_not]
  simp only [Bool.coe_toSierraBool, Bool.toSierraBool_not]

aegis_spec "wadray::wadray_signed::SignedWadTryIntoWad::try_into" :=
  fun _ (a : SignedWad) (ρ : Wad ⊕ _) =>
  ρ = if SierraBool.toBool a.2 then .inr () else .inl a.1

aegis_prove "wadray::wadray_signed::SignedWadTryIntoWad::try_into" :=
  fun _ (a : SignedWad) (ρ : Wad ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadTryIntoWad::try_into»
  aesop

aegis_spec "wadray::wadray_signed::SignedRayTryIntoRay::try_into" :=
  fun _ (a : SignedRay) (ρ : Ray ⊕ _) =>
  ρ = if SierraBool.toBool a.2 then .inr () else .inl a.1

aegis_prove "wadray::wadray_signed::SignedRayTryIntoRay::try_into" :=
  fun _ (a : SignedRay) (ρ : Ray ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedRayTryIntoRay::try_into»
  aesop

aegis_spec "wadray::wadray_signed::_felt_sign" :=
  fun _ _ a _ ρ =>
  ρ = Bool.toSierraBool (a.valMinAbs < 0)

aegis_prove "wadray::wadray_signed::_felt_sign" :=
  fun _ _ a _ ρ => by
  unfold «spec_wadray::wadray_signed::_felt_sign»
  rintro ⟨x : UInt256, y : UInt256, h₁, h₂, rfl⟩
  have : (1809251394333065606848661391547535052811553607665798349986546028067936010240 : F).val
          = PRIME / 2 := rfl
  simp only [Int.ofNat_eq_coe, Nat.cast_ofNat, Int.cast_ofNat] at h₂
  simp only [UInt256.val, h₂, h₁, ← not_le (b := a.valMinAbs) (a := 0), ZMod.valMinAbs_nonneg_iff]
  congr; apply propext
  rw [not_le, ← this, ← h₂, UInt256.val, ← h₁, UInt256.val]

aegis_spec "wadray::wadray_signed::_felt_abs" :=
  fun _ _ a _ ρ =>
  ρ = a.valMinAbs.natAbs

aegis_prove "wadray::wadray_signed::_felt_abs" :=
  fun _ _ a _ ρ => by
  unfold «spec_wadray::wadray_signed::_felt_abs»
  sierra_simp'
  rw [← not_le, ZMod.valMinAbs_nonneg_iff, not_le, not_lt, ZMod.natCast_natAbs_valMinAbs a]
  aesop

aegis_spec "wadray::wadray_signed::sign_from_mul" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (xor (SierraBool.toBool a) (SierraBool.toBool b))

aegis_prove "wadray::wadray_signed::sign_from_mul" :=
  fun _ a b ρ => by
  unfold «spec_wadray::wadray_signed::sign_from_mul»
  aesop

aegis_spec "wadray::wadray_signed::signed_wad_from_felt" :=
  fun _ _ a _ (ρ : SignedWad ⊕ _) =>
  if a.valMinAbs.natAbs < U128_MOD
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.valMinAbs / Wad.WAD_SCALE
  else ρ.isRight

aegis_prove "wadray::wadray_signed::signed_wad_from_felt" :=
  fun _ _ a _ (ρ : SignedWad ⊕ _) => by
  have hlt : a.valMinAbs.natAbs < PRIME := by
    apply lt_of_le_of_lt (ZMod.natAbs_valMinAbs_le a)
    norm_num [PRIME]
  unfold «spec_wadray::wadray_signed::signed_wad_from_felt»
  rintro ⟨_,_,_,(⟨h₁,rfl⟩|⟨h₁,rfl⟩),(⟨h₂,rfl⟩|⟨h₂,rfl⟩)⟩
  · cases h₂
    rw [ZMod.val_natCast_of_lt hlt] at h₁
    simp only [SignedWad.toRat]
    split_ifs with h₃
    · simp_all only [Option.get!, ZMod.cast_nat_cast_of_lt hlt, Sum.getLeft?_inl,
        Bool.coe_toSierraBool, decide_eq_true_eq, decide_True, Bool.toSierraBool_true, Sum.isLeft_inl,
        Wad.toRat, Wad.toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt h₁, neg_div', true_and]
      congr
      rw [Nat.cast_natAbs, Int.cast_abs, neg_eq_iff_eq_neg]
      simp only [abs_eq_neg_self, Int.cast_nonpos]
      exact le_of_lt h₃
    · simp_all only [Option.get!, Sum.getLeft?_inl, Bool.coe_toSierraBool, decide_eq_true_eq,
        not_lt, Sum.isLeft_inl, Wad.toRat, Wad.toZMod, ZMod.natCast_val, true_and,
        ZMod.cast_nat_cast_of_lt hlt, ZMod.cast_nat_cast_of_lt h₁]
      congr
      rw [Nat.cast_natAbs]
      aesop
  · simp at h₂
  · simp at h₂
  · cases h₂
    rw [ZMod.val_natCast_of_lt hlt, ← not_lt] at h₁
    simp [h₁]

aegis_spec "wadray::wadray_signed::signed_ray_from_felt" :=
  fun _ _ a _ (ρ : SignedRay ⊕ _) =>
  if a.valMinAbs.natAbs < U128_MOD
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.valMinAbs / Ray.RAY_SCALE
  else ρ.isRight

aegis_prove "wadray::wadray_signed::signed_ray_from_felt" :=
  fun _ _ a _ (ρ : SignedRay ⊕ _) => by
  have hlt : a.valMinAbs.natAbs < PRIME := by
    apply lt_of_le_of_lt (ZMod.natAbs_valMinAbs_le a)
    norm_num [PRIME]
  unfold «spec_wadray::wadray_signed::signed_ray_from_felt»
  rintro ⟨_,_,_,(⟨h₁,rfl⟩|⟨h₁,rfl⟩),(⟨h₂,rfl⟩|⟨h₂,rfl⟩)⟩
  · cases h₂
    rw [ZMod.val_natCast_of_lt hlt] at h₁
    simp only [SignedRay.toRat]
    split_ifs with h₃
    · simp_all only [Option.get!, ZMod.cast_nat_cast_of_lt hlt, Sum.getLeft?_inl,
        Bool.coe_toSierraBool, decide_eq_true_eq, decide_True, Bool.toSierraBool_true, Sum.isLeft_inl,
        Ray.toRat, Ray.toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt h₁, neg_div', true_and]
      congr
      rw [Nat.cast_natAbs, Int.cast_abs, neg_eq_iff_eq_neg]
      simp only [abs_eq_neg_self, Int.cast_nonpos]
      exact le_of_lt h₃
    · simp_all only [Option.get!, Sum.getLeft?_inl, Bool.coe_toSierraBool, decide_eq_true_eq,
        not_lt, Sum.isLeft_inl, Ray.toRat, Ray.toZMod, ZMod.natCast_val, true_and,
        ZMod.cast_nat_cast_of_lt hlt, ZMod.cast_nat_cast_of_lt h₁]
      congr
      rw [Nat.cast_natAbs]
      aesop
  · simp at h₂
  · simp at h₂
  · cases h₂
    rw [ZMod.val_natCast_of_lt hlt, ← not_lt] at h₁
    simp [h₁]

aegis_spec "wadray::wadray_signed::SignedWadIntoFelt252::into" :=
  fun _ (a : SignedWad) ρ =>
  ρ = if SierraBool.toBool a.2 then -a.1.cast else a.1.cast

aegis_prove "wadray::wadray_signed::SignedWadIntoFelt252::into" :=
  fun _ (a : SignedWad) ρ => by
  unfold «spec_wadray::wadray_signed::SignedWadIntoFelt252::into»
  aesop

aegis_spec "wadray::wadray_signed::SignedRayIntoFelt252::into" :=
  fun _ (a : SignedRay) ρ =>
  ρ = if SierraBool.toBool a.2 then -a.1.cast else a.1.cast

aegis_prove "wadray::wadray_signed::SignedRayIntoFelt252::into" :=
  fun _ (a : SignedRay) ρ => by
  unfold «spec_wadray::wadray_signed::SignedRayIntoFelt252::into»
  aesop

aegis_spec "wadray::wadray_signed::SignedWadAdd::add" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) =>
  if |a.toRat + b.toRat| < U128_MOD / Wad.WAD_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.toRat + b.toRat
  else ρ.isRight

theorem two_U128_MOD_lt_PRIME : 2 * U128_MOD < PRIME := by norm_num [U128_MOD, PRIME]

theorem four_U128_MOD_lt_PRIME : 4 * U128_MOD < PRIME := by norm_num [U128_MOD, PRIME]

theorem four_U128_MOD_le_PRIME : 4 * U128_MOD ≤ PRIME := le_of_lt four_U128_MOD_lt_PRIME

theorem add_aux1 (x : UInt128) : 4 * (x.cast : F).valMinAbs.natAbs < PRIME := by
  rw [ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, Int.natAbs_ofNat]
  apply lt_of_lt_of_le _ four_U128_MOD_le_PRIME
  apply Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (by norm_num)

aegis_prove "wadray::wadray_signed::SignedWadAdd::add" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadAdd::add»
  rcases a with ⟨va,sa⟩
  rcases b with ⟨vb,sb⟩
  have hS : 0 < (Wad.WAD_SCALE : ℚ) := by
    norm_num [Wad.WAD_SCALE]
  have hane : 2 * (va.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME va) two_pos)
      two_U128_MOD_lt_PRIME)
  have hbne : 2 * (vb.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME vb) two_pos)
      two_U128_MOD_lt_PRIME)
  have ha : 4 * (va.cast : F).valMinAbs.natAbs < PRIME := add_aux1 va
  have hb : 4 * (vb.cast : F).valMinAbs.natAbs < PRIME := add_aux1 vb
  have ha' : 4 * (- (va.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hane, Int.natAbs_neg]
  have hb' : 4 * (- (vb.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hbne, Int.natAbs_neg]
  rintro ⟨x,y,z,h₁,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ <;> dsimp only at h₁
  · simp only [Sum.isLeft_inl, Sum.getLeft?_inl, Option.get!_some, true_and, Sum.isRight_inl,
      ite_prop_iff_or, not_lt, and_false, or_false] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true] at h₁
      <;> rcases h₁ with ⟨h₁,h₂⟩
    · simp only [ZMod.valMinAbs_add_of_four_lt ha hb, Int.natAbs_ofNat,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, ← Nat.cast_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inl, Wad.toRat, Wad.toZMod,
        ite_false, and_true, add_div]
      rw [← add_div, ← Nat.cast_add, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rwa [Nat.cast_lt]
    · simp only [ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inl, Wad.toRat, Wad.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · simp only [ZMod.valMinAbs_add_of_four_lt ha' hb, ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inl, Wad.toRat, Wad.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · simp only [ZMod.valMinAbs_add_of_four_lt ha' hb',
         ZMod.valMinAbs_neg_of_ne_half hbne,  ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, neg_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inr, Wad.toRat, Wad.toZMod,
        ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rw [← neg_add, abs_neg, ← Nat.cast_add, Nat.abs_cast, Nat.cast_lt]
      rwa [← neg_add, ← Nat.cast_add, Int.natAbs_neg, Int.natAbs_ofNat] at h₁
  · simp only [Sum.isLeft_inr, Sum.getLeft?_inr, Option.get!_none, false_and, Sum.isRight_inr,
      ite_prop_iff_or, and_false, not_lt, and_true, false_or] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true,
        ZMod.valMinAbs_add_of_four_lt ha hb, ZMod.valMinAbs_add_of_four_lt ha' hb,
        ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_add_of_four_lt ha' hb',
        ZMod.valMinAbs_neg_of_ne_half hane, ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME,
        ← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁
      <;> simpa [SignedWad.toRat, Wad.toRat, Wad.toZMod, ← neg_div, ← add_div, abs_div,
        div_le_div_right hS]

aegis_spec "wadray::wadray_signed::SignedWadAddEq::add_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit  ⊕ _) =>
  if |a.toRat + b.toRat| < U128_MOD / Wad.WAD_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.1.toRat = a.toRat + b.toRat
  else ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadAddEq::add_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit  ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadAddEq::add_eq»
  aesop

aegis_spec "wadray::wadray_signed::SignedRayAdd::add" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) =>
  if |a.toRat + b.toRat| < U128_MOD / Ray.RAY_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.toRat + b.toRat
  else ρ.isRight

aegis_prove "wadray::wadray_signed::SignedRayAdd::add" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedRayAdd::add»
  rcases a with ⟨va,sa⟩
  rcases b with ⟨vb,sb⟩
  have hS : 0 < (Ray.RAY_SCALE : ℚ) := by
    norm_num [Ray.RAY_SCALE]
  have hane : 2 * (va.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME va) two_pos)
      two_U128_MOD_lt_PRIME)
  have hbne : 2 * (vb.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME vb) two_pos)
      two_U128_MOD_lt_PRIME)
  have ha : 4 * (va.cast : F).valMinAbs.natAbs < PRIME := add_aux1 va
  have hb : 4 * (vb.cast : F).valMinAbs.natAbs < PRIME := add_aux1 vb
  have ha' : 4 * (-(va.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hane, Int.natAbs_neg]
  have hb' : 4 * (-(vb.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hbne, Int.natAbs_neg]
  rintro ⟨x,y,z,h₁,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ <;> dsimp only at h₁
  · simp only [Sum.isLeft_inl, Sum.getLeft?_inl, Option.get!_some, true_and, Sum.isRight_inl,
      ite_prop_iff_or, not_lt, and_false, or_false] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true] at h₁
      <;> rcases h₁ with ⟨h₁,h₂⟩
    · simp only [ZMod.valMinAbs_add_of_four_lt ha hb, Int.natAbs_ofNat,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, ← Nat.cast_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inl, Ray.toRat, Ray.toZMod,
        ite_false, and_true, add_div]
      rw [← add_div, ← Nat.cast_add, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rwa [Nat.cast_lt]
    · simp only [ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inl, Ray.toRat, Ray.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · simp only [ZMod.valMinAbs_add_of_four_lt ha' hb, ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inl, Ray.toRat, Ray.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · simp only [ZMod.valMinAbs_add_of_four_lt ha' hb',
         ZMod.valMinAbs_neg_of_ne_half hbne,  ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, neg_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inr, Ray.toRat, Ray.toZMod,
        ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rw [← neg_add, abs_neg, ← Nat.cast_add, Nat.abs_cast, Nat.cast_lt]
      rwa [← neg_add, ← Nat.cast_add, Int.natAbs_neg, Int.natAbs_ofNat] at h₁
  · simp only [Sum.isLeft_inr, Sum.getLeft?_inr, Option.get!_none, false_and, Sum.isRight_inr,
      ite_prop_iff_or, and_false, not_lt, and_true, false_or] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true,
        ZMod.valMinAbs_add_of_four_lt ha hb, ZMod.valMinAbs_add_of_four_lt ha' hb,
        ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_add_of_four_lt ha' hb',
        ZMod.valMinAbs_neg_of_ne_half hane, ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME,
        ← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁
      <;> simpa [SignedRay.toRat, Ray.toRat, Ray.toZMod, ← neg_div, ← add_div, abs_div,
        div_le_div_right hS]

aegis_spec "wadray::wadray_signed::SignedWadSub::sub" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) =>
  if |a.toRat - b.toRat| < U128_MOD / Wad.WAD_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.toRat - b.toRat
  else ρ.isRight


aegis_prove "wadray::wadray_signed::SignedWadSub::sub" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadSub::sub»
  rcases a with ⟨va,sa⟩
  rcases b with ⟨vb,sb⟩
  have hS : 0 < (Wad.WAD_SCALE : ℚ) := by norm_num [Wad.WAD_SCALE]
  have hane : 2 * (va.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME va) two_pos)
      two_U128_MOD_lt_PRIME)
  have hbne : 2 * (vb.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME vb) two_pos)
      two_U128_MOD_lt_PRIME)
  have ha : 4 * (va.cast : F).valMinAbs.natAbs < PRIME := add_aux1 va
  have hb : 4 * (vb.cast : F).valMinAbs.natAbs < PRIME := add_aux1 vb
  have ha' : 4 * (- (va.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hane, Int.natAbs_neg]
  have hb' : 4 * (- (vb.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hbne, Int.natAbs_neg]
  rintro ⟨x,y,z,h₁,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ <;> dsimp only at h₁
  · simp only [Sum.isLeft_inl, Sum.getLeft?_inl, Option.get!_some, true_and, Sum.isRight_inl,
      ite_prop_iff_or, not_lt, and_false, or_false] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true] at h₁
      <;> rcases h₁ with ⟨h₁,h₂⟩
    · rw [sub_eq_add_neg] at h₁ h₂ ⊢
      simp only [ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inl, Wad.toRat, Wad.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · rw [sub_neg_eq_add] at h₁ h₂; rw [sub_eq_add_neg]
      simp only [ZMod.valMinAbs_add_of_four_lt ha hb, Int.natAbs_ofNat,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, ← Nat.cast_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inl, Wad.toRat, Wad.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, neg_neg, add_div, and_true]
      rw [← add_div, ← Nat.cast_add, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rwa [Nat.cast_lt]
    · rw [sub_eq_add_neg] at h₁ h₂ ⊢
      simp only [ZMod.valMinAbs_add_of_four_lt ha' hb',
         ZMod.valMinAbs_neg_of_ne_half hbne,  ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, neg_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inr, Wad.toRat, Wad.toZMod,
        ite_true, SierraBool_toBool_inl, ite_false, add_div, neg_div, and_true]
      rw [← neg_div, ← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rw [← neg_add, abs_neg, ← Nat.cast_add, Nat.abs_cast, Nat.cast_lt]
      rwa [← neg_add, ← Nat.cast_add, Int.natAbs_neg, Int.natAbs_ofNat] at h₁
    · rw [sub_neg_eq_add] at h₁ h₂; rw [sub_eq_add_neg]
      simp only [ZMod.valMinAbs_add_of_four_lt ha' hb, ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedWad.toRat, SierraBool_toBool_inr, Wad.toRat, Wad.toZMod,
        ite_true, neg_neg, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
  · simp only [Sum.isLeft_inr, Sum.getLeft?_inr, Option.get!_none, false_and, Sum.isRight_inr,
      ite_prop_iff_or, and_false, not_lt, and_true, false_or] at h₁ ⊢
    rw [sub_eq_add_neg] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true,
        ZMod.valMinAbs_add_of_four_lt ha hb, ZMod.valMinAbs_add_of_four_lt ha' hb,
        ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_add_of_four_lt ha' hb',
        ZMod.valMinAbs_neg_of_ne_half hane, ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME,
        ← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg, neg_neg] at h₁
      <;> simpa [SignedWad.toRat, Wad.toRat, Wad.toZMod, ← neg_div, ← add_div, abs_div,
        div_le_div_right hS]

aegis_spec "wadray::wadray_signed::SignedWadSubEq::sub_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) =>
  if |a.toRat - b.toRat| < U128_MOD / Wad.WAD_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.1.toRat = a.toRat - b.toRat
  else ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadSubEq::sub_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadSubEq::sub_eq»
  aesop

aegis_spec "wadray::wadray_signed::SignedRaySub::sub" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) =>
  if |a.toRat - b.toRat| < U128_MOD / Ray.RAY_SCALE
  then ρ.isLeft ∧ ρ.getLeft?.get!.toRat = a.toRat - b.toRat
  else ρ.isRight

aegis_prove "wadray::wadray_signed::SignedRaySub::sub" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedRaySub::sub»
  rcases a with ⟨va,sa⟩
  rcases b with ⟨vb,sb⟩
  have hS : 0 < (Ray.RAY_SCALE : ℚ) := by
    norm_num [Ray.RAY_SCALE]
  have hane : 2 * (va.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME va) two_pos)
      two_U128_MOD_lt_PRIME)
  have hbne : 2 * (vb.cast : ZMod PRIME).val ≠ PRIME := by
    apply ne_of_lt (lt_trans (Nat.mul_lt_mul_of_pos_left (ZMod.val_cast_lt PRIME vb) two_pos)
      two_U128_MOD_lt_PRIME)
  have ha : 4 * (va.cast : F).valMinAbs.natAbs < PRIME := add_aux1 va
  have hb : 4 * (vb.cast : F).valMinAbs.natAbs < PRIME := add_aux1 vb
  have ha' : 4 * (- (va.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hane, Int.natAbs_neg]
  have hb' : 4 * (- (vb.cast : F)).valMinAbs.natAbs < PRIME := by
    rwa [ZMod.valMinAbs_neg_of_ne_half hbne, Int.natAbs_neg]
  rintro ⟨x,y,z,h₁,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ <;> dsimp only at h₁
  · simp only [Sum.isLeft_inl, Sum.getLeft?_inl, Option.get!_some, true_and, Sum.isRight_inl,
      ite_prop_iff_or, not_lt, and_false, or_false] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true] at h₁
      <;> rcases h₁ with ⟨h₁,h₂⟩
    · rw [sub_eq_add_neg] at h₁ h₂ ⊢
      simp only [ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inl, Ray.toRat, Ray.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
    · rw [sub_neg_eq_add] at h₁ h₂; rw [sub_eq_add_neg]
      simp only [ZMod.valMinAbs_add_of_four_lt ha hb, Int.natAbs_ofNat,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, ← Nat.cast_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inl, Ray.toRat, Ray.toZMod,
        ite_false, SierraBool_toBool_inr, ite_true, neg_neg, add_div, and_true]
      rw [← add_div, ← Nat.cast_add, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rwa [Nat.cast_lt]
    · rw [sub_eq_add_neg] at h₁ h₂ ⊢
      simp only [ZMod.valMinAbs_add_of_four_lt ha' hb',
         ZMod.valMinAbs_neg_of_ne_half hbne,  ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME, neg_add] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inr, Ray.toRat, Ray.toZMod,
        ite_true, SierraBool_toBool_inl, ite_false, add_div, neg_div, and_true]
      rw [← neg_div, ← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      rw [← neg_add, abs_neg, ← Nat.cast_add, Nat.abs_cast, Nat.cast_lt]
      rwa [← neg_add, ← Nat.cast_add, Int.natAbs_neg, Int.natAbs_ofNat] at h₁
    · rw [sub_neg_eq_add] at h₁ h₂; rw [sub_eq_add_neg]
      simp only [ZMod.valMinAbs_add_of_four_lt ha' hb, ZMod.valMinAbs_neg_of_ne_half hane,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME] at h₁ h₂
      push_cast at h₂; rw [h₂]
      simp only [SignedRay.toRat, SierraBool_toBool_inr, Ray.toRat, Ray.toZMod,
        ite_true, neg_neg, add_div, neg_div, and_true]
      rw [← neg_div, ← add_div, abs_div, Nat.abs_cast]
      apply div_lt_div_of_pos_right _ hS
      simp only [← Nat.cast_lt (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg] at h₁ ⊢
      assumption
  · simp only [Sum.isLeft_inr, Sum.getLeft?_inr, Option.get!_none, false_and, Sum.isRight_inr,
      ite_prop_iff_or, and_false, not_lt, and_true, false_or] at h₁ ⊢
    rw [sub_eq_add_neg] at h₁ ⊢
    rcases sa with (sa|sa) <;> cases sa <;> rcases sb with (sb|sb) <;> cases sb
      <;> simp only [SierraBool_toBool_inl, SierraBool_toBool_inr, ite_false, ite_true,
        ZMod.valMinAbs_add_of_four_lt ha hb, ZMod.valMinAbs_add_of_four_lt ha' hb,
        ZMod.valMinAbs_add_of_four_lt ha hb', ZMod.valMinAbs_add_of_four_lt ha' hb',
        ZMod.valMinAbs_neg_of_ne_half hane, ZMod.valMinAbs_neg_of_ne_half hbne,
        ZMod.valMinAbs_cast_of_lt_half two_U128_MOD_lt_PRIME,
        ← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs, Int.cast_add,
        ZMod.natCast_val, ZMod.intCast_cast, Int.cast_neg, neg_neg] at h₁
      <;> simpa [SignedRay.toRat, Ray.toRat, Ray.toZMod, ← neg_div, ← add_div, abs_div,
        div_le_div_right hS]

aegis_spec "wadray::wadray_signed::SignedWadMul::mul" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) =>
  a.1.val * b.1.val / Wad.WAD_SCALE < U128_MOD ∧ ρ = .inl (a * b)
  ∨ U128_MOD ≤ a.1.val * b.1.val / Wad.WAD_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadMul::mul" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadMul::mul»
  rintro ⟨va,sa,vb,sb,_,_,_,rfl,rfl,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl⟩|⟨h₁,h₁'⟩)
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,rfl⟩
    simp [h₁, SignedWad.mul_def, Wad.mul, Wad.toZMod]
  · rcases h₂ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp at h₁'
    · simp [h₁]

aegis_spec "wadray::wadray_signed::SignedRayMul::mul" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) =>
  a.1.val * b.1.val / Ray.RAY_SCALE < U128_MOD ∧ ρ = .inl (a * b)
  ∨ U128_MOD ≤ a.1.val * b.1.val / Ray.RAY_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedRayMul::mul" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedRayMul::mul»
  rintro ⟨va,sa,vb,sb,_,_,_,rfl,rfl,h₁,h₂⟩
  rcases h₁ with (⟨h₁,rfl⟩|⟨h₁,h₁'⟩)
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,rfl⟩
    simp [h₁, SignedRay.mul_def, Ray.mul, Ray.toZMod]
  · rcases h₂ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp at h₁'
    · simp [h₁]

aegis_spec "wadray::wadray_signed::SignedWadMulEq::mul_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) =>
  a.1.val * b.1.val / Wad.WAD_SCALE < U128_MOD ∧ ρ = .inl (a * b, ())
  ∨ U128_MOD ≤ a.1.val * b.1.val / Wad.WAD_SCALE ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadMulEq::mul_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadMulEq::mul_eq»
  rename_i x x_1 x_2
  intro h_auto
  aesop

aegis_spec "wadray::wadray_signed::SignedWadDiv::div" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) =>
  a.1.val * Wad.WAD_SCALE / b.1.val < U128_MOD ∧ b.1.val ≠ 0
    ∧ ρ = .inl (a / b)
  ∨ (U128_MOD ≤ a.1.val * Wad.WAD_SCALE / b.1.val ∨ b.1.val = 0)
    ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadDiv::div" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadDiv::div»
  rintro ⟨va,sa,vb,sb,_,_,_,rfl,rfl,h₁,h₂⟩
  rcases h₁ with (⟨h₁,hne,rfl⟩|⟨h₁,h₁'⟩)
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,rfl⟩
    simp_all [h₁, Wad.toZMod, SignedWad.div_def, Wad.div, Wad.div_def]
  · rcases h₂ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp at h₁'
    · simp_all [Wad.toZMod]

aegis_spec "wadray::wadray_signed::SignedRayDiv::div" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) =>
  a.1.val * Ray.RAY_SCALE / b.1.val < U128_MOD ∧ b.1.val ≠ 0
    ∧ ρ = .inl (a / b)
  ∨ (U128_MOD ≤ a.1.val * Ray.RAY_SCALE / b.1.val ∨ b.1.val = 0)
    ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedRayDiv::div" :=
  fun _ _ (a b : SignedRay) _ (ρ : SignedRay ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedRayDiv::div»
  rintro ⟨va,sa,vb,sb,_,_,_,rfl,rfl,h₁,h₂⟩
  rcases h₁ with (⟨h₁,hne,rfl⟩|⟨h₁,h₁'⟩)
  · simp only [Sum.inl.injEq, false_and, or_false] at h₂
    rcases h₂ with ⟨rfl,rfl⟩
    simp_all [h₁, Ray.toZMod, SignedRay.div_def, Ray.div, Ray.div_def]
  · rcases h₂ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp at h₁'
    · simp_all [Ray.toZMod]

aegis_spec "wadray::wadray_signed::SignedWadDivEq::div_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) =>
  a.1.val * Wad.WAD_SCALE / b.1.val < U128_MOD ∧ b.1.val ≠ 0
    ∧ ρ = .inl (a / b, ())
  ∨ (U128_MOD ≤ a.1.val * Wad.WAD_SCALE / b.1.val ∨ b.1.val = 0)
    ∧ ρ.isRight

aegis_prove "wadray::wadray_signed::SignedWadDivEq::div_eq" :=
  fun _ _ (a b : SignedWad) _ (ρ : SignedWad × Unit ⊕ _) => by
  unfold «spec_wadray::wadray_signed::SignedWadDivEq::div_eq»
  rename_i x x_1 x_2
  intro h_auto
  aesop

aegis_spec "wadray::wadray_signed::U128IntoSignedWad::into" :=
  fun _ a (ρ : SignedWad) =>
  ρ = ⟨a, Bool.toSierraBool .false⟩

aegis_prove "wadray::wadray_signed::U128IntoSignedWad::into" :=
  fun _ a (ρ : SignedWad) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::U128IntoSignedRay::into" :=
  fun _ a (ρ : SignedRay) =>
  ρ = ⟨a, Bool.toSierraBool .false⟩

aegis_prove "wadray::wadray_signed::U128IntoSignedRay::into" :=
  fun _ a (ρ : SignedRay) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::WadIntoSignedWad::into" :=
  fun _ (a : Wad) (ρ : SignedWad) =>
  ρ = ⟨a, Bool.toSierraBool .false⟩

aegis_prove "wadray::wadray_signed::WadIntoSignedWad::into" :=
  fun _ (a : Wad) (ρ : SignedWad) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::RayIntoSignedRay::into" :=
  fun _ (a : Ray) (ρ : SignedRay) =>
  ρ = ⟨a, Bool.toSierraBool .false⟩

aegis_prove "wadray::wadray_signed::RayIntoSignedRay::into" :=
  fun _ (a : Ray) (ρ : SignedRay) => by
  rintro rfl
  rfl

aegis_spec "wadray::wadray_signed::WadIntoSignedRay::into" :=
  fun _ _ (a : Wad) _ (ρ : SignedRay ⊕ _) =>
  if a.toZMod.val * Ray.DIFF < U128_MOD
  then ρ = .inl ⟨a.toZMod * Ray.DIFF, Bool.toSierraBool .false⟩
  else ρ.isRight

aegis_prove "wadray::wadray_signed::WadIntoSignedRay::into" :=
  fun _ _ (a : Wad) _ (ρ : SignedRay ⊕ _) => by
  unfold «spec_wadray::wadray_signed::WadIntoSignedRay::into»
  rintro ⟨_,_,_,h₁,h₂⟩
  aesop
