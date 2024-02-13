import WadrayVerification.WadraySigned

aegis_info "wadray::tests::test_wadray_signed::test_wadray_signed::test_add_eq"

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_add_sub" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_add_sub" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_add_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_add_eq" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_sub_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_sub_eq" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_mul_div" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_mul_div" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_mul_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_mul_eq" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_div_eq" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_div_eq" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_comparison" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_comparison" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_bounded" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_bounded" :=
  fun _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_into_conversions" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_into_conversions" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_zeroable_oneable" :=
  fun _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_zeroable_oneable" :=
  fun _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_signed" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_signed" :=
  fun _ _ _ ρ => by
  sorry

aegis_spec "wadray::tests::test_wadray_signed::test_wadray_signed::test_zero_cmp" :=
  fun _ _ _ ρ =>
  ρ = .inl ()

aegis_prove "wadray::tests::test_wadray_signed::test_wadray_signed::test_zero_cmp" :=
  fun _ _ _ ρ => by
  sorry
