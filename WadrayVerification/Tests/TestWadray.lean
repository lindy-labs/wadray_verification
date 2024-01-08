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
