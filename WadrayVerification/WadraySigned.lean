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
